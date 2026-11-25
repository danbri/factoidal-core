// SPDX-License-Identifier: Apache-2.0
pragma solidity 0.8.30;

contract PureCompare {
    function ge(uint256 a, uint256 b) external pure returns (bool) {
        return a >= b;
    }
}
