////////////////////////////////////////////////////////////////////////////
//                       Imports and multi-contracts                      //
////////////////////////////////////////////////////////////////////////////

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
    estimateFees(uint16, address , bytes, bool, bytes) returns (uint256, uint256) => NONDET
    setConfig(uint16, address, uint256, bytes)
    getConfig(uint16, address, uint256) returns (bytes)

    // Receiver
    lzReceive(uint16, bytes, uint64, bytes) => NONDET
}

////////////////////////////////////////////////////////////////////////////
//                       Definitions                                      //
////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////
//                       Ghosts                                           //
////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////
//                       Rules                                            //
////////////////////////////////////////////////////////////////////////////

invariant sendReceiveSeparate()
    !(isReceivingPayload() && isSendingPayload())

rule whoChangedStoredPayLoad(method f, uint16 ID, bytes dst)
filtered {f -> !f.isView}
{
    env e;
    calldataarg args;
    uint64 Length1; uint64 Length2;
    address Address1; address Address2;
    bytes32 Hash1; bytes32 Hash2;

    Length1, Address1, Hash1 = getStoredPayLoad(ID, dst);
        f(e, args);
    Length2, Address2, Hash2 = getStoredPayLoad(ID, dst);
    
    assert Length1 == Length2 && Address1 == Address2 && Hash1 == Hash2;
}

rule whoChangedInNonce(method f, uint16 ID, bytes dst)
filtered{f -> !f.isView}
{
    env e;
    calldataarg args;
    require dst.length <=7;

    uint64 inNonce1 = getInboundNonce(ID, dst);
        f(e, args);
    uint64 inNonce2 = getInboundNonce(ID, dst);

    assert inNonce1 == inNonce2,
    "function ${f} changed inbound Nonce";
}

rule whoChangedOutNonce(method f, uint16 ID, address dst)
filtered {f -> !f.isView}
{
    env e;
    calldataarg args;
    uint64 outNonce1 = getOutboundNonce(ID, dst);
        f(e, args);
    uint64 outNonce2 = getOutboundNonce(ID, dst);

    assert outNonce1 == outNonce2,
    "function ${f} changed outbound Nonce";
}

rule whoChangedLibrary(method f, uint16 chainID)
{
    env e;
    calldataarg args;
    address Lib1 = libraryLookup(e, chainID);
        f(e, args);
    address Lib2 = libraryLookup(e, chainID);
    assert Lib1 == Lib2, "function ${f} changed library lookup";
}

rule whoChangedLibraryAddress(method f, address UA)
{
    env e;
    calldataarg args;
    address Lib1 = getReceiveLibraryAddress(UA);
        f(e, args);
    address Lib2 = getReceiveLibraryAddress(UA);
    assert Lib1 == Lib2, "function ${f} changed library address";
}

rule retryPayLoadSucceedsOnlyOnce()
{
    env e; env e2;

    uint16 chainID;
    bytes srcAddress;
    bytes payLoad;

    require payLoad.length <= 7;
    require srcAddress.length <= 7;

    retryPayload(e, chainID, srcAddress, payLoad);
    retryPayload@withrevert(e2, chainID, srcAddress, payLoad);
    
    assert lastReverted;
}

invariant NonceNotZero(uint16 ID, bytes dst, address destination)
    bytes2Address(dst) == destination => getInboundNonce(ID, dst) != 0 && getOutboundNonce(ID, destination) != 0
filtered {f -> !f.isView}
{
    preserved{
    require dst.length <=7; //tool limitatiions
    require getInboundNonce(ID, dst) < max_uint64 && getOutboundNonce(ID, destination) < max_uint64; //overflow!
    }
}

rule oneInNonceAtATime(method f, uint16 ID, bytes dst)
filtered {f -> !f.isView}
{
    env e;
    calldataarg args;
    uint16 ID2; bytes dst2;
    require dst.length <=7;
    require dst2.length <=7;

    uint64 inNonce1_A = getInboundNonce(ID, dst);
    uint64 inNonce2_A = getInboundNonce(ID2, dst2);
        f(e, args);
    uint64 inNonce1_B = getInboundNonce(ID, dst);
    uint64 inNonce2_B = getInboundNonce(ID2, dst2);
    
    assert  inNonce1_A != inNonce1_B && 
            inNonce2_A != inNonce2_B =>
            ID == ID2 && bytes2Address(dst) == bytes2Address(dst2);
}

rule oneOutNonceAtATime(method f, uint16 ID, address dst)
filtered {f -> !f.isView}
{
    env e;
    calldataarg args;
    uint16 ID2; address dst2;

    uint64 inNonce1_A = getOutboundNonce(ID, dst);
    uint64 inNonce2_A = getOutboundNonce(ID2, dst2);
        f(e, args);
    uint64 inNonce1_B = getOutboundNonce(ID, dst);
    uint64 inNonce2_B = getOutboundNonce(ID2, dst2);
    
    assert  inNonce1_A != inNonce1_B && 
            inNonce2_A != inNonce2_B =>
            ID == ID2 && dst == dst2;
}

rule receivePayLoadSuccessStep(uint16 srcChainID, uint64 nonce)
{
    env e;
    bytes payload; require payload.length <=7;
    uint gasLimit;
    address dstAddress;
    bytes srcAddress; require srcAddress.length <=7;

    receivePayload(e, srcChainID, srcAddress, 
        dstAddress, nonce, gasLimit, payload);
    
    receivePayload@withrevert(e, srcChainID, srcAddress, 
        dstAddress, nonce+1, gasLimit, payload);

    assert !lastReverted;
}

rule sendReceiveEqualNonce(uint16 srcChainID, uint16 dstChainID)
{
    env e;
    bytes srcAddress; require srcAddress.length <= 7;
    bytes _destination; require _destination.length <= 7;
    bytes _adapterParams; require _adapterParams.length <= 7;
    bytes _payload; require _payload.length <= 7;
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

    assert outNonce_A == inNonce_A => outNonce_B == inNonce_B && 
            inNonce_A + 1 == inNonce_B &&
            outNonce_A + 1 == outNonce_B;
}

rule receiveAfterRetryFail(uint16 srcChainID)
{
 env e;

    bytes srcAddress; require srcAddress.length <= 7;
    bytes payLoad;  require payLoad.length <= 7;
    address dstAddress;
    uint64 nonce;
    uint gasLimit;

    retryPayload@withrevert(e, srcChainID, srcAddress, payLoad);
    bool retryReverted = lastReverted;

    uint16 _srcChainID;
    bytes _srcAddress; require _srcAddress.length <= 7;
    forceResumeReceive(e,_srcChainID, _srcAddress);

    receivePayload@withrevert(e, srcChainID, srcAddress, dstAddress, nonce, gasLimit, payLoad);
    bool receiveReverted = lastReverted;

    assert retryReverted && !receiveReverted => _srcChainID == srcChainID && bytes2Address(_srcAddress) == bytes2Address(srcAddress);
}

/*
rule receivePayLoadCheck()
{
    env e;
    calldataarg args;
    uint64 Length1; uint64 Length2;
    address Address1; address Address2;
    bytes32 Hash1; bytes32 Hash2;
    uint16 srcChainId; bytes srcAddress;
    require srcAddress.length <= 7;

    Length1, Address1, Hash1 = getStoredPayLoad(srcChainId, srcAddress);
        receivePayload(e, args);
    Length2, Address2, Hash2 = getStoredPayLoad(srcChainId, srcAddress);

    assert Length1 == Length2 && Address1 == Address2 && Hash1 == Hash2;
}
*/
////////////////////////////////////////////////////////////////////////////
//                       Functions                                        //
////////////////////////////////////////////////////////////////////////////
