pragma solidity ^0.4.20;

import "ds-token/token.sol";

contract Pie is DSToken {
    function Pie(bytes32 sym) DSToken(sym) {}
    function flex(address guy, int wad) public {
        if (wad > 0) mint(guy, uint( wad));
        if (wad < 0) burn(guy, uint(-wad));
    }
    function suck(uint wad) public {
        this.mint(msg.sender, wad);
    }
}
