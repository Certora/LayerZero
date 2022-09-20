// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.7.6;

import "../../contracts/Endpoint.sol";

contract EndpointHarness is Endpoint {
    constructor(uint16 _ID)
        Endpoint(_ID){}

    // Getter for the stored payload struct fields.
    function getStoredPayLoad(uint16 _srcChainId, bytes memory _srcAddress)
    external view returns (uint64, address, bytes32)
    {
        StoredPayload storage sp = storedPayload[_srcChainId][_srcAddress];
        return (sp.payloadLength, sp.dstAddress, sp.payloadHash);
    }

    // Converts bytes to address.
    function bytes2Address(bytes memory address_bytes) public pure returns (address)
    {
        return abi.decode(address_bytes, (address));
    }

    // A simple dummy implementation for lzReceive that includes a reverting path.
    function lzReceive(uint16 _srcChainId, bytes calldata _srcAddress, uint64 _nonce, bytes calldata _payload) pure external
    {
        require(bytes2Address(_srcAddress) != address(0));
    }
}
