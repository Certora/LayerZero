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
    getInboundNonceHar(uint16, bytes) returns (uint64) envfree
    getOutboundNonce(uint16, address) returns (uint64) envfree
        
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
filtered {f -> !f.isView}
{
    env e;
    calldataarg args;
    uint64 inNonce1 = getInboundNonceHar(ID, dst);
        f(e, args);
    uint64 inNonce2 = getInboundNonceHar(ID, dst);

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

rule retryPayLoadSucceedsOnlyOnce()
{
    env e; env e2;
    calldataarg args;
    retryPayload(e, args);
    retryPayload@withrevert(e2, args);
    assert lastReverted;
}

invariant NonceNotZero(uint16 ID, bytes dst)
    getInboundNonceHar(ID, dst) != 0 //&& getOutboundNonce(ID, dst) != 0
filtered {f -> !f.isView}

////////////////////////////////////////////////////////////////////////////
//                       Functions                                        //
////////////////////////////////////////////////////////////////////////////