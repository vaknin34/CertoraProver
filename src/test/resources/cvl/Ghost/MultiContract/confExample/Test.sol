import './InnerContract.sol';

contract Test {
    uint256 test_slot_0;
    mapping(uint256 => uint256) test_slot_1;
    InnerContract c;

    constructor() public {
        c = new InnerContract();
    }

    function setZeroSlots(uint256 outer, uint256 inner) public {
        test_slot_0 = outer;
        c.setZeroSlot(inner);
    }

    function setZeroSlotsReversed(uint256 outer, uint256 inner) public {
        c.setZeroSlot(inner);
        test_slot_0 = outer;
    }

    function setOneSlotsAt(uint256 key, uint256 outer, uint256 inner) public {
        test_slot_1[key] = outer;
        c.setOneSlotAt(key, inner);
    }

    function setOneSlotsAtReversed(uint256 key, uint256 outer, uint256 inner) public {
        c.setOneSlotAt(key, inner);
        test_slot_1[key] = outer;
    }
}