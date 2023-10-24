#include <iostream>

#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"

#include "SymbolicInterpreter.h"

extern SymbolicInterpreter SI;

// helper function for the stack-based arithmetic
z3::expr pop(MemoryTy &Mem) {
  z3::expr SE = SI.getStack().top();
  SI.getStack().pop();
  if (SE.to_string().at(0) == 'R') {
    int RID = std::stoi(SE.to_string().substr(1));
    return Mem.at(Address(RID));
  } else
    return SE;
}

/*
 * Implement your transfer functions.
 */
extern "C" void __DSE_Alloca__(int R, int *Ptr) {
  MemoryTy &Mem = SI.getMemory();
  Address Addr(R);
  z3::expr SE = SI.getContext().int_val((intptr_t)Ptr);
  Mem.insert(std::make_pair(Addr, SE));
}

extern "C" void __DSE_Store__(int R) {
  MemoryTy &Mem = SI.getMemory();
  z3::expr Addr = Mem.at(Address(R)); // get value from symbolic register
  Address MAddr =
      Address((int *)std::stoll(Addr.to_string())); // create symbolic memory
  Mem.insert(std::make_pair(MAddr, pop(Mem)));
}

extern "C" void __DSE_Load__(int Y, int *X) {
  MemoryTy &Mem = SI.getMemory();
  Address Addr(Y);
  z3::expr SE = Mem.at(Address(X));
  Mem.insert(std::make_pair(Addr, SE));
}

extern "C" void __DSE_ICmp__(int R, int Op) {
  MemoryTy &Mem = SI.getMemory();
  z3::expr RHS = pop(Mem);
  z3::expr LHS = pop(Mem);
  switch (Op) {
  case llvm::CmpInst::ICMP_EQ:
    SI.getPathCondition().push_back(std::make_pair(R, LHS == RHS));
    break;
  case llvm::CmpInst::ICMP_SGT:
    SI.getPathCondition().push_back(std::make_pair(R, LHS > RHS));
    break;
  }
}

extern "C" void __DSE_BinOp__(int R, int Op) {
  MemoryTy &Mem = SI.getMemory();
  z3::expr RHS = pop(Mem);
  z3::expr LHS = pop(Mem);
  switch (Op) {
  case llvm::Instruction::Add:
    Mem.insert(std::make_pair(Address(R), LHS + RHS));
    break;
  case llvm::Instruction::Mul:
    Mem.insert(std::make_pair(Address(R), LHS * RHS));
    break;
  case llvm::Instruction::SRem:
    Mem.insert(std::make_pair(Address(R), z3::rem(LHS, RHS)));
    break;
  default:
    return;
  }
}
