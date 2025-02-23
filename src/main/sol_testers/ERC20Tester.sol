pragma solidity ^0.4.24;

import "./ERC20.sol";

contract MyERC is ERC20 {
    
    function pubMint(address account, uint256 amount) public {
        _mint(account, amount);
    }
    
}

contract AccountWithApprove {

    constructor(MyERC erc, address addrForApprove) public payable {
        erc.approve(addrForApprove,50);
    }
}

contract ERC20Tester {
    MyERC erc;
    AccountWithApprove otherAccount;
    address addr1 = 0x1baeb01683c6f91c4140d9ec114e2b24d8450883;
    uint256 MAX_UINT256 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;

    event debugBool(bool boolVar);

    constructor() public payable {
        erc = new MyERC();
        otherAccount = new AccountWithApprove(erc,this);
        erc.pubMint(this,200);
        erc.pubMint(addr1,100);
        erc.pubMint(otherAccount,100);
    }

    function testTransfer1(address _to, uint256 _value) public {
        bool precon = (erc.balanceOf(this) >= _value && 
            erc.balanceOf(_to) + _value >= erc.balanceOf(_to) && 
            _to != address(this));
        if (!precon) {
            return;
        }

        uint256 origBalanceOfThis = erc.balanceOf(this);
        uint256 origBalanceOfTo = erc.balanceOf(_to);

        bool ret = erc.transfer(_to, _value);

        bool postcon = erc.balanceOf(this) == origBalanceOfThis - _value && 
            erc.balanceOf(_to) == origBalanceOfTo + _value && 
            ret == true;
        assert(postcon);
    }
    
    function testTransfer2(address _to, uint256 _value) public {
        // no precon
        
        uint256 origTotalSupply = erc.totalSupply();
        uint256 origAllowanceThisTo = erc.allowance(this,_to);
        uint256 origAllowanceToThis = erc.allowance(_to,this);
        uint256 origAllowanceToTo = erc.allowance(_to,_to);
        uint256 origAllowanceThisThis = erc.allowance(this,this);

        bool ret = address(erc).call(bytes4(keccak256("transfer(address,uint256)")),_to,_value);
        emit debugBool(ret);
        
        bool postcon =  (erc.totalSupply() == origTotalSupply && 
            erc.allowance(this,_to) == origAllowanceThisTo &&
            erc.allowance(_to,this) == origAllowanceToThis &&
            erc.allowance(_to,_to) == origAllowanceToTo &&
            erc.allowance(this,this) == origAllowanceThisThis);

        assert(postcon);
    }
    
    function testTransfer3(address _to, uint256 _value) public {
        bool precon = (_to == address(this));
        if (!precon) {
            return;
        }
        
        uint256 origBalanceOfTo = erc.balanceOf(_to);
        
        bool ret = address(erc).call(bytes4(keccak256("transfer(address,uint256)")),_to,_value);
        emit debugBool(ret);
        
        if (!ret) {
            return;
        }
        
        bool postcon = (erc.balanceOf(_to) == origBalanceOfTo);
        assert(postcon);
    }
   
    function testTransfer4(address _to, uint256 _value) public {
        bool precon = (erc.balanceOf(this) < _value && _to != address(this));
        if (!precon) {
            return;
        }
        
        uint256 origBalanceOfThis = erc.balanceOf(this);
        uint256 origBalanceOfTo = erc.balanceOf(_to);
        
        bool retCall = address(erc).call(bytes4(keccak256("transfer(address,uint256)")),_to,_value);
        emit debugBool(retCall);
        
        if (retCall == false) {
            return;
        }
        
        //we run transer twice in this test, but it is OK
        assert(erc.balanceOf(this) < _value);
        bool ret = erc.transfer(_to, _value);
        
        bool postcon = (ret == false && 
            erc.balanceOf(this) == origBalanceOfThis && 
            erc.balanceOf(_to) == origBalanceOfTo);
        assert(postcon);
    }
    
    
    function testTransfer5(address _to, uint256 _value) public {
        bool precon = (erc.balanceOf(_to) + _value < erc.balanceOf(_to) && 
            _to != address(this));
        if (!precon) {
            return;
        }
        
        uint256 origBalanceOfThis = erc.balanceOf(this);
        uint256 origBalanceOfTo = erc.balanceOf(_to);
        
        bool retCall = address(erc).call(bytes4(keccak256("transfer(address,uint256)")),_to,_value);
        emit debugBool(retCall);
        
        if (retCall == false) {
            return;
        }
        
        //we run transer twice in this test, but it is OK
        assert(erc.balanceOf(_to) + _value < erc.balanceOf(_to));
        bool ret = erc.transfer(_to, _value);
        
        bool postcon = (ret == false && 
            erc.balanceOf(this) == origBalanceOfThis && 
            erc.balanceOf(_to) == origBalanceOfTo);
        assert(postcon);
    }
    
    function testTransferFrom1(address _from, address _to, uint256 _value) public {
		bool precon = (erc.balanceOf(this) >= _value &&
			erc.allowance(_from, this) >= _value &&	
            erc.balanceOf(_to) + _value >= erc.balanceOf(_to) && 
            _to != _from);
        if (!precon) {
            return;
        }

        uint256 origBalanceOfTo = erc.balanceOf(_to);
		uint256 origBalanceOfFrom = erc.balanceOf(_from);
		uint256 origAllowanceFromThis = erc.allowance(_from, this);
		
        bool ret = erc.transferFrom(_from, _to, _value);

        bool postcon = (erc.balanceOf(_from) == origBalanceOfFrom - _value && 
            erc.balanceOf(_to) == origBalanceOfTo + _value && 
			erc.allowance(_from,this) == origAllowanceFromThis - _value &&
            ret == true);
        assert(postcon);	
	}
	
	function runTestTransferFrom1() public {
	    testTransferFrom1(otherAccount,addr1,10);         
	}
	
	
	function compareTwoTupple(address t11, address t12, address t21, address t22) pure private returns (bool) {
	    return (t11 == t21 && t12 == t22);
	}
	
	// This test is divided to three parts to avoid a compiler "stack too deep" error. Such a crappy language...
	function testTransferFrom2part1(address _from, address _to, uint256 _value) private {
		//no precon

        uint256 origBalanceOfThis = erc.balanceOf(this);
		uint256 origTotalSupply = erc.totalSupply();
    
        
        /*
        uint256 origAllowanceThisFrom = erc.allowance(this,_from);
        uint256 origAllowanceThisTo = erc.allowance(this,_to);
        uint256 origAllowanceToThis = erc.allowance(_to,this);
        uint256 origAllowanceToFrom = erc.allowance(_to,_from);
        uint256 origAllowanceFromTo = erc.allowance(_from,_to);
        uint256 origAllowanceFromFrom = erc.allowance(_from,_from);
        uint256 origAllowanceToTo = erc.allowance(_to,_to);
        uint256 origAllowanceThisThis = erc.allowance(this,this);
        */
		
        bool ret = address(erc).call(bytes4(keccak256("transferFrom(address,address,uint256)")),_from,_to,_value);
        emit debugBool(ret);

        bool postcon = (erc.totalSupply() == origTotalSupply &&
            (address(this) == _from || address(this) == _to || erc.balanceOf(this) == origBalanceOfThis));
    /*
        bool postcon = (erc.totalSupply() == origTotalSupply &&
            (compareTwoTupple(this,_to,_from,this) || erc.allowance(this,_to) == origAllowanceThisTo) &&
            (compareTwoTupple(this,_from,_from,this) || erc.allowance(this,_from) == origAllowanceThisFrom) &&
            (compareTwoTupple(_to,this,_from,this) || erc.allowance(_to,this) == origAllowanceToThis) &&
            (compareTwoTupple(_to,_from,_from,this) || erc.allowance(_to,_from) == origAllowanceToFrom) &&
            (compareTwoTupple(_from,_to,_from,this) || erc.allowance(_from,_to) == origAllowanceFromTo) &&
            (compareTwoTupple(_from,_from,_from,this) || erc.allowance(_from,_from) == origAllowanceFromFrom) &&
            (compareTwoTupple(_to,_to,_from,this) || erc.allowance(_to,_to) == origAllowanceToTo) &&
            (compareTwoTupple(this,this,_from,this) || erc.allowance(this,this) == origAllowanceThisThis) &&
            (address(this) == _from || address(this) == _to || erc.balanceOf(this) == origBalanceOfThis)
            );
*/
        assert(postcon);	
	}
	
	function testTransferFrom2part2(address _from, address _to, uint256 _value) private {
		//no precon

        uint256 origAllowanceThisTo = erc.allowance(this,_to);
        uint256 origAllowanceThisFrom = erc.allowance(this,_from);
        uint256 origAllowanceToThis = erc.allowance(_to,this);
        uint256 origAllowanceToFrom = erc.allowance(_to,_from);
        
        bool ret = address(erc).call(bytes4(keccak256("transferFrom(address,address,uint256)")),_from,_to,_value);
        emit debugBool(ret);

        bool postcon = (
            (compareTwoTupple(this,_to,_from,this) || erc.allowance(this,_to) == origAllowanceThisTo) &&
            (compareTwoTupple(this,_from,_from,this) || erc.allowance(this,_from) == origAllowanceThisFrom) &&
            (compareTwoTupple(_to,this,_from,this) || erc.allowance(_to,this) == origAllowanceToThis) &&
            (compareTwoTupple(_to,_from,_from,this) || erc.allowance(_to,_from) == origAllowanceToFrom)
            );

        assert(postcon);	
	}
	
    
    function testTransferFrom2part3(address _from, address _to, uint256 _value) private {
		//no precon

        uint256 origAllowanceFromTo = erc.allowance(_from,_to);
        uint256 origAllowanceFromFrom = erc.allowance(_from,_from);
        uint256 origAllowanceToTo = erc.allowance(_to,_to);
        uint256 origAllowanceThisThis = erc.allowance(this,this);
        
		
        bool ret = address(erc).call(bytes4(keccak256("transferFrom(address,address,uint256)")),_from,_to,_value);
        emit debugBool(ret);

        bool postcon = (
            (compareTwoTupple(_from,_to,_from,this) || erc.allowance(_from,_to) == origAllowanceFromTo) &&
            (compareTwoTupple(_from,_from,_from,this) || erc.allowance(_from,_from) == origAllowanceFromFrom) &&
            (compareTwoTupple(_to,_to,_from,this) || erc.allowance(_to,_to) == origAllowanceToTo) &&
            (compareTwoTupple(this,this,_from,this) || erc.allowance(this,this) == origAllowanceThisThis)
            );

        assert(postcon);	
	}
    
    function testTransferFrom2(address _from, address _to, uint256 _value) public {
        testTransferFrom2part1(_from, _to, _value);
        testTransferFrom2part2(_from, _to, _value);
        testTransferFrom2part3(_from, _to, _value);
    }
    
    function runTestTransferFrom2() public {
	    testTransferFrom2(otherAccount,addr1,10);
	    testTransferFrom2(otherAccount,addr1,1000);
	}
    
    function testTransferFrom3(address _from, address _to, uint256 _value) public {
		bool precon = (_to == _from);
        if (!precon) {
            return;
        }

        uint256 origBalanceOfTo = erc.balanceOf(_to);
		uint256 origAllowanceFromThis = erc.allowance(_from, this);

        bool retCall = address(erc).call(bytes4(keccak256("transferFrom(address,address,uint256)")),_from,_to,_value);
        emit debugBool(retCall);
        if (!retCall) {
            return;
        }
    
        bool postcon = ((erc.allowance(_from, this) == origAllowanceFromThis || erc.allowance(_from, this) == origAllowanceFromThis - _value) &&
            erc.balanceOf(_to) == origBalanceOfTo);
        assert(postcon);		
    }
    
    function runTestTransferFrom3() public {
	    testTransferFrom3(otherAccount,otherAccount,10);
	    testTransferFrom3(otherAccount,otherAccount,1000);
	}
    
    function testTransferFrom4(address _from, address _to, uint256 _value) public {
		bool precon = (_to != _from && erc.balanceOf(_from) < _value);
        if (!precon) {
            return;
        }

        uint256 origBalanceOfTo = erc.balanceOf(_to);
        uint256 origBalanceOfFrom = erc.balanceOf(_from);
		uint256 origAllowanceFromThis = erc.allowance(_from, this);

        bool retCall = address(erc).call(bytes4(keccak256("transferFrom(address,address,uint256)")),_from,_to,_value);
        emit debugBool(retCall);
        if (!retCall) {
            return;
        }
        
        //we run it again but it is OK
        assert(erc.balanceOf(_from) < _value);
        bool ret = erc.transferFrom(_from, _to, _value);
        
        bool postcon = (ret == false &&
            erc.allowance(_from,this) == origAllowanceFromThis && 
            erc.balanceOf(_from) == origBalanceOfFrom && 
            erc.balanceOf(_to) == origBalanceOfTo);
        assert(postcon);		
    }
    
    function runTestTransferFrom4() public {
	    testTransferFrom4(otherAccount,addr1,1000);
	}
	
	function testTransferFrom5(address _from, address _to, uint256 _value) public {
		bool precon = (_to != _from && erc.balanceOf(_to) + _value < erc.balanceOf(_to));
        if (!precon) {
            return;
        }

        uint256 origBalanceOfTo = erc.balanceOf(_to);
        uint256 origBalanceOfFrom = erc.balanceOf(_from);
		uint256 origAllowanceFromThis = erc.allowance(_from, this);

        bool retCall = address(erc).call(bytes4(keccak256("transferFrom(address,address,uint256)")),_from,_to,_value);
        emit debugBool(retCall);
        if (!retCall) {
            return;
        }
        
        //we run it again but it is OK
        assert(erc.balanceOf(_to) + _value < erc.balanceOf(_to));
        bool ret = erc.transferFrom(_from, _to, _value);
        
        bool postcon = (ret == false &&
            erc.allowance(_from,this) == origAllowanceFromThis && 
            erc.balanceOf(_from) == origBalanceOfFrom && 
            erc.balanceOf(_to) == origBalanceOfTo);
        assert(postcon);		
    }
    
    function runTestTransferFrom5() public {
	    testTransferFrom5(otherAccount,addr1,MAX_UINT256);
	}
	
    function testTransferFrom6(address _from, address _to, uint256 _value) public {
		bool precon = (erc.allowance(_from, this) < _value);
        if (!precon) {
            return;
        }

        uint256 origBalanceOfTo = erc.balanceOf(_to);
        uint256 origBalanceOfFrom = erc.balanceOf(_from);
		uint256 origAllowanceFromThis = erc.allowance(_from, this);

        bool retCall = address(erc).call(bytes4(keccak256("transferFrom(address,address,uint256)")),_from,_to,_value);
        emit debugBool(retCall);
        if (!retCall) {
            return;
        }
        
        //we run it again but it is OK
        assert(erc.allowance(_from, this) < _value);
        bool ret = erc.transferFrom(_from, _to, _value);
        
        bool postcon = (ret == false &&
            erc.allowance(_from,this) == origAllowanceFromThis && 
            erc.balanceOf(_from) == origBalanceOfFrom && 
            erc.balanceOf(_to) == origBalanceOfTo);
        assert(postcon);		
    }
    
    function runTestTransferFrom6() public {
	    testTransferFrom6(otherAccount,addr1,60);
	}
	
	
	function testApprove(address _spender, uint256 _value) public {
	    //no precon

        uint256 origTotalSupply = erc.totalSupply();
        uint256 origBalanceOfSpender = erc.balanceOf(_spender);
        uint256 origBalanceOfThis = erc.balanceOf(this);
		uint256 origAllowanceSpenderThis = erc.allowance(_spender, this);
		uint256 origAllowanceThisThis = erc.allowance(this, this);
		uint256 origAllowanceSpenderSpender = erc.allowance(_spender, _spender);

        bool ret = erc.approve(_spender, _value);
        
        bool postcon = (erc.allowance(this,_spender) == _value &&
	        ret == true && 
            erc.totalSupply() == origTotalSupply && 
            erc.balanceOf(_spender) == origBalanceOfSpender && 
            erc.balanceOf(this) == origBalanceOfThis && 
            (address(this) == _spender || erc.allowance(_spender,this) == origAllowanceSpenderThis) && 
            (address(this) == _spender || erc.allowance(this,this) == origAllowanceThisThis) && 
            (address(this) == _spender || erc.allowance(_spender,_spender) == origAllowanceSpenderSpender));
        assert(postcon);		
    }
    
}
