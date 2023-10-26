#include "Extractor.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.h"
#include <algorithm>

#include "Utils.h"

// Given the context C, and a LLVM value V, this function evalues V
// as a Z3 expression depending on its type. (constant, int, bool, etc.)
z3::expr eval(z3::context &C, Value *V) {
  if (ConstantInt *CI = dyn_cast<ConstantInt>(V)) {
    return C.int_val(CI->getSExtValue());
  } else {
    if (V->getType()->isIntegerTy(32)) {
      z3::expr X = C.int_const(toString(V).c_str());
      return X;
    } else if (V->getType()->isIntegerTy(1)) {
      z3::expr X = C.bool_const(toString(V).c_str());
      return X;
    } else {
      z3::expr X = C.bool_const("unknown");
      return X;
    }
  }
}

// This function encodes an individual instruction I.
void Extractor::extractConstraints(Instruction *I,
                                   z3::expr_vector &Assertions) {
  z3::func_decl NodeRel = BBRelations.at(I->getParent());
  if (CallInst *CI = dyn_cast<CallInst>(I)) {
    if (isAssertFail(CI)) {
      addQuery(NodeRel);
    } else if (isAssume(CI)) {
      z3::expr X = eval(C, CI->getArgOperand(0));
      Assertions.push_back(X > 0);
    }
  } else if (ICmpInst *II = dyn_cast<ICmpInst>(I)) {
    z3::expr X = eval(C, II);
    z3::expr Y = eval(C, II->getOperand(0));
    z3::expr Z = eval(C, II->getOperand(1));

    switch (II->getPredicate()) {
    case CmpInst::ICMP_EQ:
      Assertions.push_back(X == (Y == Z));
      break;
    case CmpInst::ICMP_NE:
      Assertions.push_back(X == (Y != Z));
      break;
    /* =========================== Exercise ============================*/
    // ICmpInst have multiple CmpInst kinds, e.g, ICMP_SGE, ICMP_SGT, ICMP_SLT,
    // and ICMP_SLE Follow the two examples above to fill in the rest
    case CmpInst::ICMP_SGE:
      Assertions.push_back(X == (Y >= Z));
      break;
    case CmpInst::ICMP_SGT:
      Assertions.push_back(X == (Y > Z));
      break;
    case CmpInst::ICMP_SLT:
      Assertions.push_back(X == (Y < Z));
      break;
    case CmpInst::ICMP_SLE:
      Assertions.push_back(X == (Y <= Z));
      break;
    default:;
    }
  } else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(I)) {
    /* =========================== Exercise ============================*/
    // BinaryOperators have multiple operands, e.g, BO->getOperand(0),
    // BO->getOperand(1) Get the opcode using BO->getOpcode(). The possible
    // opcodes are BinaryOps::Add, BinaryOps::Sub, BinaryOps::Mul,
    //                          BinaryOps::SDiv, BinaryOps::UDiv
    // Follow the previous branch to fill in the rest
    z3::expr R = eval(C, BO);
    z3::expr LHS = eval(C, BO->getOperand(0));
    z3::expr RHS = eval(C, BO->getOperand(1));
    switch (BO->getOpcode()) {
    case Instruction::Add:
      Assertions.push_back(R == (LHS + RHS));
      break;
    case Instruction::Sub:
      Assertions.push_back(R == (LHS - RHS));
      break;
    case Instruction::Mul:
      Assertions.push_back(R == (LHS * RHS));
      break;
    case Instruction::SDiv:
      Assertions.push_back(R == (LHS / RHS));
      break;
    case Instruction::UDiv:
      Assertions.push_back(R == z3::udiv(LHS, RHS));
      break;
    default:;
    }
  } else if (CastInst *CI = dyn_cast<CastInst>(I)) {
    z3::expr X = eval(C, CI);
    z3::expr Y = eval(C, CI->getOperand(0));

    if (CI->getSrcTy()->isIntegerTy(32) && CI->getDestTy()->isIntegerTy(1)) {
      Assertions.push_back(
          X == z3::ite(Y > C.int_val(0), C.bool_val(true), C.bool_val(false)));
    } else if (CI->getSrcTy()->isIntegerTy(1) &&
               CI->getDestTy()->isIntegerTy(32)) {
      Assertions.push_back(
          X == z3::ite(Y, C.int_val(1), C.int_val(0))); // ite: if-then-else
    }
  }
}

bool isVariable(Value *V) {
  return !isa<Constant>(V) && !V->getType()->isVoidTy() &&
         !V->getType()->isLabelTy();
}

bool isPHINode(Value *V) { return isa<PHINode>(V); }

// In this function, the main tasks are collecting variables, computing free
// variables, etc., and adding them to the solver. The data structures that are
// used in this function are defined in Extractor.h.
void Extractor::initialize(Function &F) {
  std::set<Value *> AllVariables;
  z3::sort_vector SortVector(C);
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (isVariable(&I) || isPHINode(&I)) {
        AllVariables.insert(&I);
        if (I.getType()->isIntegerTy(32)) {
          SortVector.push_back(C.int_sort());
          AllVariableVector.push_back(C.int_const(toString(&I).c_str()));
        } else if (I.getType()->isIntegerTy(1)) {
          SortVector.push_back(C.bool_sort());
          AllVariableVector.push_back(C.bool_const(toString(&I).c_str()));
        }
      }
    }
  }

  for (auto &BB : F) {
    std::set<Value *> BindVars;
    for (auto &I : BB) {
      if (isVariable(&I) && !isPHINode(&I)) {
        BindVars.insert(&I);
      }
    }
    // free variable here means the variables outside the current basic block
    // and PHI nodes
    std::set<Value *> &FreeVars = FreeVariables[&BB];
    std::set_difference(AllVariables.begin(), AllVariables.end(),
                        BindVars.begin(), BindVars.end(),
                        std::inserter(FreeVars, FreeVars.begin()));
    z3::sort_vector SortVector(C);
    z3::expr_vector VariableVector(C);
    for (auto &V : FreeVars) {
      if (V->getType()->isIntegerTy(32)) {
        SortVector.push_back(C.int_sort());
        VariableVector.push_back(C.int_const(toString(V).c_str()));
      } else if (V->getType()->isIntegerTy(1)) {
        SortVector.push_back(C.bool_sort());
        VariableVector.push_back(C.bool_const(toString(V).c_str()));
      }
    }
    FreeVariableVector.insert(std::make_pair(&BB, VariableVector));
    // each basic block is related to free variables
    z3::func_decl NodeRel =
        C.function(BB.getName().str().c_str(), SortVector, C.bool_sort());
    Solver->register_relation(NodeRel);
    BBRelations.insert(std::make_pair(&BB, NodeRel));
  }
  // define the entry rule
  BasicBlock *Entry = &F.getEntryBlock();
  z3::func_decl Rel = BBRelations.at(Entry);
  z3::expr_vector Vec = FreeVariableVector.at(Entry);
  try {
    z3::expr R0 = z3::forall(Vec, Rel(Vec));
    Solver->add_rule(R0, C.str_symbol(""));
  } catch (z3::exception e) {
    std::cerr << "z3::exception: " << e.msg() << std::endl;
  }
}

// get the free variable of Succ with the affect from BB
z3::expr_vector Extractor::transition(BasicBlock *BB, BasicBlock *Succ) {
  z3::expr_vector Vec(C);
  int Idx = 0;
  for (auto &FV : FreeVariables[Succ]) {
    if (PHINode *Phi = dyn_cast<PHINode>(FV)) {
      // This free variable is a phinode of either Succ or some other blocks
      if (Phi->getBasicBlockIndex(BB) >= 0) {
        // substitude the free variable with its source variable from BB
        z3::expr E = eval(C, Phi->getIncomingValueForBlock(BB));
        Vec.push_back(E);
        Idx++;
        continue;
      }
    }
    Vec.push_back(FreeVariableVector.at(Succ)[Idx]);
    Idx++;
  }
  return Vec;
}

// This function encodes the basic block BB as Constrained Horn Clause.
void Extractor::extractConstraints(BasicBlock *BB) {
  z3::func_decl &BBRel = BBRelations.at(BB);
  z3::expr_vector Vec = FreeVariableVector.at(BB);
  z3::expr BBTuple = BBRel(Vec);
  z3::expr_vector Assertions(C);

  // We need to get the encoded instructions for the current basic block
  // using Extractor::extractConstraints(Instruction ...). The encodings
  // are recorded in Assertions vector.
  for (auto &I : *BB) {
    extractConstraints(&I, Assertions);
  }
  // Next, we compute the conjunction of the instructions. We will later add
  // this as a conjunction term in the CHC formulation.
  z3::expr And = z3::mk_and(Assertions);

  // BranchInst has two different cases: unconditional or conditional.
  if (BranchInst *BI = dyn_cast<BranchInst>(&BB->back())) {
    if (BI->isUnconditional()) {
      BasicBlock *Succ = BI->getSuccessor(0);
      z3::func_decl &SuccRel = BBRelations.at(Succ);
      z3::expr_vector TPropagation = transition(BB, Succ);
      z3::expr SuccTuple = SuccRel(TPropagation);
      z3::expr R0 =
          z3::forall(AllVariableVector, z3::implies(BBTuple && And, SuccTuple));
      Solver->add_rule(R0, C.str_symbol(""));
    } else {
      std::string Cond = toString(BI->getCondition());
      z3::expr CondExpr = C.bool_const(Cond.c_str());

      /* =================================== Exercise
       * =======================================*/
      // Follow the unconditional case above and complete the conditional case.
      // What is different in this case?

      // True Branch
      BasicBlock *TSucc = BI->getSuccessor(0);
      z3::func_decl &TSuccRel = BBRelations.at(TSucc);
      z3::expr_vector TPropagation = transition(BB, TSucc);
      z3::expr TSuccTuple = TSuccRel(TPropagation);
      z3::expr TR0 =
          z3::forall(AllVariableVector,
                     z3::implies(CondExpr && BBTuple && And, TSuccTuple));
      Solver->add_rule(TR0, C.str_symbol(""));

      // False Branch
      BasicBlock *FSucc = BI->getSuccessor(1);
      z3::func_decl &FSuccRel = BBRelations.at(FSucc);
      z3::expr_vector FPropagation = transition(BB, FSucc);
      z3::expr FSuccTuple = FSuccRel(FPropagation);
      z3::expr FR0 =
          z3::forall(AllVariableVector,
                     z3::implies(!CondExpr && BBTuple && And, FSuccTuple));
      Solver->add_rule(FR0, C.str_symbol(""));
    }
  }
}