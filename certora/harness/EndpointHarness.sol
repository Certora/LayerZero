// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.7.6;

import "../../contracts/Endpoint.sol";

contract EndpointHarness is Endpoint {
    constructor(uint16 _ID)
        Endpoint(_ID){}

    function getStoredPayLoad(uint16 _srcChainId, bytes memory _srcAddress)
    external view returns (uint64, address, bytes32)
    {
        StoredPayload storage sp = storedPayload[_srcChainId][_srcAddress];
        return (sp.payloadLength, sp.dstAddress, sp.payloadHash);
    }

    function getInboundNonceHar(uint16 _srcChainId, bytes memory _srcAddress) 
    external view returns (uint64) {
        return inboundNonce[_srcChainId][_srcAddress];
    }
}