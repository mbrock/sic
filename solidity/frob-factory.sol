pragma solidity ^0.4.20;

import "./frob.sol";

contract FrobFactory {
    function make(
        address pie,
        address flap,
        address flop
    ) public returns (Bin) {
        return new Bin(pie, flap, flop);
    }
}