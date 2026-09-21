// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// Minimal ERC20, honest. Used as the positive control for the falsifier.
contract ERC20 {
    mapping(address => uint256) public balanceOf;          // slot 0
    mapping(address => mapping(address => uint256)) public allowance; // slot 1
    uint256 public totalSupply;                            // slot 2

    function transfer(address to, uint256 amount) external returns (bool) {
        uint256 b = balanceOf[msg.sender];
        require(b >= amount, "insufficient");
        unchecked { balanceOf[msg.sender] = b - amount; }
        balanceOf[to] += amount;
        return true;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        uint256 a = allowance[from][msg.sender];
        require(a >= amount, "allowance");
        uint256 b = balanceOf[from];
        require(b >= amount, "insufficient");
        unchecked {
            allowance[from][msg.sender] = a - amount;
            balanceOf[from] = b - amount;
        }
        balanceOf[to] += amount;
        return true;
    }
}
