#include <iostream>

#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"

#include "SymbolicInterpreter.h"

extern SymbolicInterpreter SI;

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
  z3::expr SE = SI.getStack().top();
  SI.getStack().pop();
  if (SE.to_string().at(0) == 'R') {
    int RID = std::stoi(SE.to_string().substr(1));
    z3::expr RSE = Mem.at(Address(RID));
    Mem.insert(std::make_pair(MAddr, RSE));
  } else
    Mem.insert(std::make_pair(MAddr, SE));
}

extern "C" void __DSE_Load__(int Y, int *X) {
  MemoryTy &Mem = SI.getMemory();
  Address Addr(Y);
  z3::expr SE = Mem.at(Address(X));
  Mem.insert(std::make_pair(Addr, SE));
}

extern "C" void __DSE_ICmp__(int R, int Op) { /* Add your code here */
}

extern "C" void __DSE_BinOp__(int R, int Op) {
  switch (Op) {
  case llvm::Instruction::Add:
  default:
    return;
  }
}
