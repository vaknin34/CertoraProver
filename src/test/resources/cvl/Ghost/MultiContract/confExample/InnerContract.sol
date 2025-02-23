contract InnerContract {
    uint256 inner_slot_0;
    mapping(uint256 => uint256) inner_slot_1;

    constructor() public { }

    function setZeroSlot(uint256 x) public {
        inner_slot_0 = x;
    }
    
    function setOneSlotAt(uint256 key, uint256 x) public {
        inner_slot_1[key] = x;
    }
}