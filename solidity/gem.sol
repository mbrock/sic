pragma solidity ^0.4.20;

import "ds-token/token.sol";

contract Gem is DSToken {
    function Gem(bytes32 symbol) DSToken(symbol) public {}
    function move(address src, address dst, int wad) public {
        if (wad > 0) move(src, dst, uint(wad));
        if (wad < 0) move(dst, src, uint(-wad));
    }
}
