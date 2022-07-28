////////////////////////////////////////////////////////////////////////////
//                       Imports and multi-contracts                      //
////////////////////////////////////////////////////////////////////////////

// Last verification (without receiveAfterRetryFail rule):
// https://vaas-stg.certora.com/output/41958/2d66cd791481cf5550eb/?anonymousKey=094323d3c6e902fc8a1bf3c1c0021f922fbc7c52

////////////////////////////////////////////////////////////////////////////
//                       Methods                                          //
////////////////////////////////////////////////////////////////////////////
methods{
    // Endpoint
    isSendingPayload() returns (bool) envfree
    isReceivingPayload() returns (bool) envfree
    getChainId() returns (uint16) envfree
    getStoredPayLoad(uint16, bytes) returns (uint64, address, bytes32) envfree
    bytes2Address(bytes) returns (address) envfree
    getInboundNonce(uint16, bytes) returns (uint64) envfree
    getOutboundNonce(uint16, address) returns (uint64) envfree
    getReceiveVersion(address) returns (uint16) envfree
    getSendVersion(address) returns (uint16) envfree
    getReceiveLibraryAddress(address) returns (address) envfree
        
    // Messaging library
    send(address, uint64, uint16, bytes, bytes, address, address, bytes) => NONDET
    estimateFees(uint16, address, bytes, bool, bytes) returns (uint256, uint256) => NONDET
    setConfig(uint16, address, uint256, bytes)
    getConfig(uint16, address, uint256) returns (bytes)

    // Receiver
    lzReceive(uint16, bytes, uint64, bytes) => NONDET
}

////////////////////////////////////////////////////////////////////////////
//                       Definitions                                      //
////////////////////////////////////////////////////////////////////////////

definition MAX_BYTES() returns uint = 96;

////////////////////////////////////////////////////////////////////////////
//                       Ghosts                                           //
////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////


// Cannot by receiving and sending payload simultaneously
invariant sendReceiveSeparate()
    !(isReceivingPayload() && isSendingPayload())

// inbound and outbound nonces are never zero.
invariant NonceNotZero(uint16 ID, bytes dst, address src)
    bytes2Address(dst) == src => 
    ( getInboundNonce(ID, dst) != 0 && getOutboundNonce(ID, src) != 0 )
{
    preserved
    {
        require dst.length <= MAX_BYTES(); // tool limitations
        require getInboundNonce(ID, dst) < max_uint64 && getOutboundNonce(ID, src) < max_uint64; //overflow!
    }
}

// Only retryPayload and forceResumeReceive can change the stored payload.
rule whoChangedStoredPayLoad(method f, uint16 ID, bytes dst)
{
    env e;
    calldataarg args;
    uint64 Length1; uint64 Length2;
    address Address1; address Address2;
    bytes32 Hash1; bytes32 Hash2;

    Length1, Address1, Hash1 = getStoredPayLoad(ID, dst);
        f(e, args);
    Length2, Address2, Hash2 = getStoredPayLoad(ID, dst);
    
    assert !(Length1 == Length2 && Address1 == Address2 && Hash1 == Hash2)
    => f.selector == retryPayload(uint16, bytes, bytes).selector ||
    f.selector == forceResumeReceive(uint16,bytes).selector ;
}

// The correct stored payload is changed according to the input arguments
// of the acting functions.
rule changedCorrectPayLoad(uint8 func, uint16 chainId, bytes dstAddress)
{
    env e;
    uint16 _chainId; bytes _dstAddress;
    require dstAddress.length <= MAX_BYTES();
    require _dstAddress.length <= MAX_BYTES();
    bytes _payload; require _payload.length <= MAX_BYTES();

    uint64 Length1; uint64 Length2;
    address Address1; address Address2;
    bytes32 Hash1; bytes32 Hash2;

    Length1, Address1, Hash1 = getStoredPayLoad(chainId, dstAddress);

    if (func == 0){
        retryPayload(e, _chainId, _dstAddress, _payload);
    }
    else {
        forceResumeReceive(e, _chainId, _dstAddress);
    }

    Length2, Address2, Hash2 = getStoredPayLoad(chainId, dstAddress);

    assert !(Length1 == Length2 && Address1 == Address2 && Hash1 == Hash2)
    => (_chainId == chainId && 
    bytes2Address(_dstAddress) == bytes2Address(dstAddress));
}

// Only recievePayLoad can change the inbound nonce.
rule onlyReceiveChangedInNonce(method f, uint16 ID, bytes dst)
{
    env e;
    calldataarg args;
    require dst.length <= MAX_BYTES();

    uint64 inNonce1 = getInboundNonce(ID, dst);
        f(e, args);
    uint64 inNonce2 = getInboundNonce(ID, dst);

    assert inNonce1 != inNonce2 => f.selector == 
    receivePayload(uint16, bytes, address, uint64, uint256, bytes).selector,
    "function ${f} changed inbound Nonce";
}

// recievePayLoad changes the correct inbound nonce according to its input arguments.
rule receiveChangeCorrectInNonce(uint16 ID, bytes dst)
{
    env e;
    bytes dst2; bytes payload;
    uint gasLimit;
    uint16 ID2;
    uint64 nonce;
    address dstAddress;

    require dst.length <= MAX_BYTES();
    require dst2.length <= MAX_BYTES();

    uint64 inNonce1 = getInboundNonce(ID, dst);
        receivePayload(e, ID2, dst2, dstAddress, nonce, gasLimit, payload);
    uint64 inNonce2 = getInboundNonce(ID, dst);

    assert inNonce1 != inNonce2 => 
        (ID2 == ID &&
        bytes2Address(dst) == bytes2Address(dst2)); 
}

// only send() function can change outbound nonce.
rule onlySendChangedOutNonce(method f, uint16 ID, address dst)
{
    env e;
    calldataarg args;
    uint64 outNonce1 = getOutboundNonce(ID, dst);
        f(e, args);
    uint64 outNonce2 = getOutboundNonce(ID, dst);

    assert outNonce1 != outNonce2 => f.selector == 
    send(uint16, bytes, bytes, address, address, bytes).selector,
    "function ${f} changed outbound Nonce";
}

// send() changes the correct outbound nonce according to its input arguments.
rule sendChangeCorrectOutNonce(uint16 dstChainID, address srcAddress)
{
    env e;
    bytes destination;
    uint16 dstChainID2;
    bytes payload;
    address refundAddress;
    address zroPaymentAddress;
    bytes adapterParams;

    uint64 outNonce1 = getOutboundNonce(dstChainID, srcAddress);
        send(e, dstChainID2, destination, payload, 
            refundAddress, zroPaymentAddress, adapterParams);
    uint64 outNonce2 = getOutboundNonce(dstChainID, srcAddress);

    assert outNonce1 != outNonce2 => 
        dstChainID == dstChainID2 &&
        e.msg.sender == srcAddress;
}

rule onlyNewVersionChangedLibrary(method f, uint16 chainID)
{
    env e;
    calldataarg args;
    address Lib1 = libraryLookup(e, chainID);
        f(e, args);
    address Lib2 = libraryLookup(e, chainID);
    assert Lib1 != Lib2 => f.selector == newVersion(address).selector,
    "function ${f} changed library lookup";
}

rule setVersionChangedLibraryAddress(method f, address UA)
{
    env e;
    calldataarg args;
    address Lib1 = getReceiveLibraryAddress(UA);
        f(e, args);
    address Lib2 = getReceiveLibraryAddress(UA);
    assert Lib1 != Lib2 => f.selector == setReceiveVersion(uint16).selector ||
    f.selector == setDefaultReceiveVersion(uint16).selector,
    "function ${f} changed library address";
}

// The library address of an application cannot only changed by itself
// (the msg.sender).
rule changedLibraryAddressIntegrity(address UA)
{
    env e;
    uint16 version;
    address Lib1 = getReceiveLibraryAddress(UA);
        setReceiveVersion(e, version);
    address Lib2 = getReceiveLibraryAddress(UA);
    assert Lib1 != Lib2 => e.msg.sender == UA;
}

// One cannot successfully call retryPayLoad twice.
rule retryPayLoadSucceedsOnlyOnce()
{
    env e; env e2;

    uint16 chainID;
    bytes srcAddress;
    bytes payLoad;

    require payLoad.length <= MAX_BYTES();
    require srcAddress.length <= MAX_BYTES();

    retryPayload(e, chainID, srcAddress, payLoad);
    retryPayload@withrevert(e2, chainID, srcAddress, payLoad);
    
    assert lastReverted;
}

// Only one value of inbound nonce is changed at a time.
rule oneInNonceAtATime(method f, uint16 ID, bytes dst)
{
    env e;
    calldataarg args;
    uint16 ID2; bytes dst2;
    require dst.length <= MAX_BYTES();
    require dst2.length <= MAX_BYTES();

    uint64 inNonce1_A = getInboundNonce(ID, dst);
    uint64 inNonce2_A = getInboundNonce(ID2, dst2);
        f(e, args);
    uint64 inNonce1_B = getInboundNonce(ID, dst);
    uint64 inNonce2_B = getInboundNonce(ID2, dst2);
    
    assert  inNonce1_A != inNonce1_B && 
            inNonce2_A != inNonce2_B =>
            ID == ID2 && bytes2Address(dst) == bytes2Address(dst2);
}

// Only one value of outbound nonce is changed at a time.
rule oneOutNonceAtATime(method f, uint16 ID, address src)
filtered {f -> !f.isView}
{
    env e;
    calldataarg args;
    uint16 ID2; address src2;

    uint64 inNonce1_A = getOutboundNonce(ID, src);
    uint64 inNonce2_A = getOutboundNonce(ID2, src2);
        f(e, args);
    uint64 inNonce1_B = getOutboundNonce(ID, src);
    uint64 inNonce2_B = getOutboundNonce(ID2, src2);
    
    assert  inNonce1_A != inNonce1_B && 
            inNonce2_A != inNonce2_B =>
            ID == ID2 && src == src2;
}

// If receivePayLoad succeeds for a nonce, then it must also succeed for the
// subsequent nonce.
rule receivePayLoadSuccessStep(uint16 srcChainID, uint64 nonce)
{
    env e;
    bytes payload; require payload.length <= MAX_BYTES();
    uint gasLimit;
    address dstAddress;
    bytes srcAddress; require srcAddress.length <= MAX_BYTES();

    receivePayload(e, srcChainID, srcAddress, 
        dstAddress, nonce, gasLimit, payload);
    
    receivePayload@withrevert(e, srcChainID, srcAddress, 
        dstAddress, nonce+1, gasLimit, payload);

    assert !lastReverted;
}

// The inbound and outbound nonces remain synced after a pair of send-receive call.
rule sendReceiveEqualNonce(uint16 srcChainID, uint16 dstChainID)
{
    env e;
    bytes srcAddress; require srcAddress.length <= MAX_BYTES();
    bytes _destination; require _destination.length <= MAX_BYTES();
    bytes _adapterParams; require _adapterParams.length <= MAX_BYTES();
    bytes _payload; require _payload.length <= MAX_BYTES();
    uint64 nonce;
    uint gasLimit;
    address dstAddress;
    address _zroPaymentAddress;
    address _refundAddress;

    uint64 outNonce_A = getOutboundNonce(dstChainID, e.msg.sender);
    uint64 inNonce_A = getInboundNonce(srcChainID, srcAddress);
        send(e, dstChainID, _destination, _payload, _refundAddress, _zroPaymentAddress, _adapterParams);
        receivePayload(e, srcChainID, srcAddress, dstAddress, nonce, gasLimit, _payload);
    uint64 outNonce_B = getOutboundNonce(dstChainID, e.msg.sender);
    uint64 inNonce_B = getInboundNonce(srcChainID, srcAddress);

    assert outNonce_A == inNonce_A => 
            ( outNonce_B == inNonce_B && 
            ( inNonce_A < max_uint64 => inNonce_A + 1 == inNonce_B) &&
            ( outNonce_A < max_uint64 => outNonce_A + 1 == outNonce_B) );
}

rule receiveAfterRetryFail(uint16 srcChainID)
{
 env e;

    bytes srcAddress; require srcAddress.length <= MAX_BYTES();
    bytes payLoad;  require payLoad.length <= MAX_BYTES();
    address dstAddress;
    uint64 nonce;
    uint gasLimit;

    receivePayload@withrevert(e, srcChainID, srcAddress, 
        dstAddress, nonce, gasLimit, payLoad);
    require lastReverted;

    uint16 _srcChainID;
    bytes _srcAddress; require _srcAddress.length <= MAX_BYTES();
    forceResumeReceive(e, _srcChainID, _srcAddress);

    receivePayload@withrevert(e, srcChainID, srcAddress, 
        dstAddress, nonce + 1, gasLimit, payLoad);
    bool receiveReverted = lastReverted;

    assert !receiveReverted => 
        _srcChainID == srcChainID && 
        bytes2Address(_srcAddress) == bytes2Address(srcAddress);
}

rule afterForceCannotRetry(uint16 srcChainID, bytes srcAddress)
{
    env e;
    bytes payload;
    require srcAddress.length <= MAX_BYTES();
    forceResumeReceive(e, srcChainID, srcAddress);
    retryPayload@withrevert(e, srcChainID, srcAddress, payload);
    assert lastReverted;
}

rule bytes2AddressReach(bytes dst)
{
    address foo = bytes2Address(dst);
    assert dst.length >= 32;
}

////////////////////////////////////////////////////////////////////////////
//                       Functions                                        //
////////////////////////////////////////////////////////////////////////////
