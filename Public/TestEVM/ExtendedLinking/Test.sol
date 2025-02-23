interface IStateManager {
    function setField(uint f) external;
    function getField() external returns (uint);
}

contract DelegateStorage {
    uint theField;

    function setField(uint f) external {
        theField = f;
    }

    function getField() external returns (uint) {
        return theField;
    }
}

abstract contract MixinState {
    struct UintPointer {
        uint x;
    }

    function setField(uint f) external {
        getPointer().x = f;
    }

    function getField() external returns (uint) {
        return getPointer().x;
    }

    function getPointer() internal virtual returns (UintPointer storage ret);
}

contract DelegateMixin1 is MixinState {
    bytes32 constant storageSlot = keccak256("delegate.mixin1");

    function getPointer() internal override returns (UintPointer storage ret) {
        bytes32 raw = storageSlot;
        assembly {
            ret.slot := raw
        }
    }
}

contract DelegateMixin2 is MixinState {
	bytes32 constant storageSlot = keccak256("delegate.mixin2");

    function getPointer() internal override returns (UintPointer storage ret) {
        bytes32 raw = storageSlot;
        assembly {
            ret.slot := raw
        }
    }
}

abstract contract WithDelegateStorage {
    function doGet(address a) internal returns (uint) {
        bytes memory data = abi.encodeCall(IStateManager.getField, ());
        (bool success, bytes memory ret) = a.delegatecall(data);
        require(success);
        return abi.decode(ret, (uint));
    }

    function doSet(address a, uint f) internal {
        bytes memory data = abi.encodeCall(IStateManager.setField, (f));
        (bool success, ) = a.delegatecall(data);
        require(success);
    }
}

contract Test is WithDelegateStorage {
    function getCallee() internal returns (address) {
        return msg.sender;
    }

    function doSet(uint f) external {
        doSet(getCallee(), f);
    }

    function doGet() external returns (uint) {
        return doGet(getCallee());
    }

    function getCalleeVirt(bool x) internal returns (address) {
        return msg.sender;
    }

    function doSet(uint f, bool callee) external {
        doSet(getCalleeVirt(callee), f);
    }

    function doGet(bool callee) external returns (uint) {
        return doGet(getCalleeVirt(callee));
    }
}

contract WithCollision is WithDelegateStorage {
    mapping(address => uint) public dummy;
    function getCallee() internal returns (address) {
        return msg.sender;
    }
    function doGet() external returns (uint) {
        return doGet(getCallee());
    }

    function doSet(uint f) external {
        doSet(getCallee(), f);
    }
}
