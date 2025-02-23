contract Test {
    function test(
        address target,
        bytes memory data,
        uint256 weiValue,
        string memory errorMessage
    ) public returns (bytes memory) {
        //        require(isContract(target), "Address: call to non-contract");        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value: weiValue}(data);
        // SG: Here: first puts in stack the value of success (1 if success 0 otherwise). Then, if returnsize is 0, sets a pointer to 0x60, otherwise copies returndata to memory to a newly allocated pointer.
        // SG: So we have stack variable V pointing to an array in memory that's either real copied return data or the empty array 0x60. Now, in case success=0, we go to the else...
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            // SG: To read returndata.length, we read M[V]. so if success=0, we read M[0x60]. That's where points to analysis complains.
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}
