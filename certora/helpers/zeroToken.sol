// SPDX-License-Identifier: agpl-3.0
pragma solidity ^0.8.0;
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "@openzeppelin/contracts/token/ERC20/SafeERC20.sol";

contract zeroToken is ERC20 {
    using SafeERC20 for IERC20;
}
    