pragma solidity ^0.4.20;

contract PieLike {
    function flex(address,int) public;
    function balanceOf(address) public returns (uint);
    function approve(address) public;
}

contract GemLike {
    function move(address,address,uint) public;
    function approve(address) public;
}

contract Flippy{
    function kick(address lad, address gal, uint tab, uint lot, uint bid)
        public returns (uint);
}

contract Fusspot {
    function kick(address gal, uint lot, uint bid) public returns (uint);
}

contract Bin {
    address public mom;
    PieLike public pie;
    bool    public live;
    uint256 public forms;

    address public flapper;
    address public flopper;

    struct Ilk {
        uint256  spot;  // Liquidation Factor (ray)
        uint256  rate;  // Accumulated Rates  (ray)
        uint256  line;  // Debt Ceiling       (wad)

        uint256  Art;   // Total Debt         (wad)

        address gem;    // Collateral
        Flippy  flip;   // Liquidator
    }
    struct Urn {
        uint256 ink;    // Locked Collateral  (wad)
        uint256 art;    // Debt               (wad)
    }

    mapping (bytes32 => Ilk)                      public ilks;
    mapping (bytes32 => mapping (address => Urn)) public urns;

    function get_ink(bytes32 ilk, address lad) public view returns (uint) {
        return urns[ilk][lad].ink;
    }
    function get_art(bytes32 ilk, address lad) public view returns (uint) {
        return urns[ilk][lad].art;
    }

    function era() internal view returns (uint48) { return uint48(now); }

    uint constant RAY = 10 ** 27;
    function add(uint x, uint y) internal pure returns (uint z) {
        require((z = x + y) >= x);
    }
    function sub(uint x, uint y) internal pure returns (uint z) {
        require((z = x - y) <= x);
    }
    function mul(uint x, uint y) internal pure returns (uint z) {
        require(y == 0 || (z = x * y) / y == x);
    }
    function rmul(uint x, uint y) internal pure returns (uint z) {
        z = add(mul(x, y), RAY / 2) / RAY;
    }
    // todo: int math safety
    function addi(uint x, int y) internal pure returns (uint z) {
        return uint(int(x) + y);
    }
    function isub(uint x, uint y) internal pure returns (int z) {
        return int(x) - int(y);
    }
    function rmuli(uint x, int y) internal pure returns (int z) {
        return y > 0 ? int(rmul(x, uint(y))) : -int(rmul(x, uint(-y)));
    }

    function Bin(address pie_, address flapper_, address flopper_) public {
        mom = msg.sender;
        pie = PieLike(pie_);
        live = true;

        flapper = flapper_;
        flopper = flopper_;

        pie.approve(flapper);
    }
    function form(address gem)
        public returns (bytes32 ilk)
    {
        require(msg.sender == mom);
        ilk = bytes32(++forms);
        ilks[ilk].rate = RAY;
        ilks[ilk].gem = gem;
    }
    function file(bytes32 ilk, bytes32 what, uint risk) public {
        require(msg.sender == mom);
        if (what == "spot") ilks[ilk].spot = risk;
        if (what == "rate") ilks[ilk].rate = risk;
        if (what == "line") ilks[ilk].line = risk;
    }
    function fuss(bytes32 ilk, address flip) public {
        require(msg.sender == mom);
        ilks[ilk].flip = Flippy(flip);
        GemLike(ilks[ilk].gem).approve(flip);
    }
    function flux(address gem, address lad, int wad) internal {
        if (wad > 0) GemLike(gem).move(address(this), lad, uint( wad));
        if (wad < 0) GemLike(gem).move(lad, address(this), uint(-wad));
    }
    function frob(bytes32 ilk, uint ink, uint art) public {
        Urn storage u = urns[ilk][msg.sender];
        Ilk storage i = ilks[ilk];

        uint ink_ = u.ink;
        uint art_ = u.art;
        int  dart = isub(art, art_);

        u.ink = ink;
        u.art = art;
        i.Art = addi(i.Art, dart);

        bool calm = rmul(i.rate, i.Art) <= i.line;
        bool cool = dart <= 0;
        bool nice = rmul(ink, art_)   >= rmul(ink_, art);
        bool safe = rmul(ink, i.spot) >= rmul(art, i.rate);

        require(( calm || cool ) && ( nice || safe ) && live);

        pie.flex(msg.sender, rmuli(i.rate, dart));
        flux(i.gem, msg.sender, isub(ink_, ink));
    }

    function bite(bytes32 ilk, address lad) public returns (uint) {
        Urn storage u = urns[ilk][lad];
        Ilk storage i = ilks[ilk];

        uint ink = u.ink;
        uint art = u.art;
        uint tab = rmul(art, i.rate);

        u.ink = 0;
        u.art = 0;
        i.Art = sub(i.Art, art);

        require(rmul(ink, i.spot) < tab);  // !safe

        woe = add(woe, tab);
        return i.flip.kick({lad: lad, gal: this, tab: tab, lot: ink, bid: 0});
    }
    function bump(bytes32 ilk, address lad, uint wad) public {
        GemLike(ilks[ilk].gem).move(msg.sender, this, wad);
        urns[ilk][lad].ink = add(urns[ilk][lad].ink, wad);
    }

    uint256 public woe;
    function heal(uint wad) public {
        pie.flex(this, -int(wad));
        woe = sub(woe, wad);
    }

    function flap(uint wad) public returns (uint) {
        require(woe == 0);
        return Fusspot(flapper).kick(this, wad, 0);
    }
    function flop(uint wad) public returns (uint) {
        require(pie.balanceOf(this) == 0);
        return Fusspot(flopper).kick(this, uint(-1), wad);
    }
}
