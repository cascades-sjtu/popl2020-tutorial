#include "Extractor.h"

#include "llvm/IR/Instruction.h"

void Extractor::initialize() {
  /* Relations for Def and Use */
  Solver->register_relation(Def);
  Solver->register_relation(Use);

  /* Relations for Reaching Definition Analysis */
  Solver->register_relation(Kill);
  Solver->register_relation(Gen);
  Solver->register_relation(Next);
  Solver->register_relation(In);
  Solver->register_relation(Out);

  /* Relations for Taint Analysis */
  Solver->register_relation(Taint);
  Solver->register_relation(Edge);
  Solver->register_relation(Path);
  Solver->register_relation(Sanitizer);
  Solver->register_relation(Div);
  Solver->register_relation(Alarm);

  /*
   * Add your code here:
   * Define your analysis rules for taint analysis and add the rules to the
   * solver.
   */
  // declare variable
  z3::expr X = C.bv_const("X", 32);
  z3::expr Y = C.bv_const("Y", 32);
  z3::expr Z = C.bv_const("Z", 32);

  // kill_rule: Kill(Y, Z) := Def(X, Y) & Def(X, Z)
  z3::expr kill_rule =
      z3::forall(X, Y, Z, z3::implies(Def(X, Y) && Def(X, Z), Kill(Y, Z)));
  Solver->add_rule(kill_rule, C.str_symbol("kill_rule"));

  // out_rule1: Out(X, Y) := Gen(X, Y)
  z3::expr out_rule1 = z3::forall(X, Y, z3::implies(Gen(X, Y), Out(X, Y)));
  Solver->add_rule(out_rule1, C.str_symbol("out_rule1"));

  // out_rule2: Out(X, Y) := In(X, Y) & !Kill(Y, X)
  z3::expr out_rule2 =
      z3::forall(X, Y, z3::implies(In(X, Y) && !Kill(Y, X), Out(X, Y)));
  Solver->add_rule(out_rule2, C.str_symbol("out_rule2"));

  // in_rule: In(X, Y) := Out(Z, Y) & Next(Z, X)
  z3::expr in_rule =
      z3::forall(X, Y, Z, z3::implies(Out(Z, Y) && Next(Z, X), In(X, Y)));
  Solver->add_rule(in_rule, C.str_symbol("in_rule"));

  // edge_rule: Edge(Y, Z) := Def(X, Y) & Use(X, Z) & In(Z, Y)
  z3::expr edge_rule = z3::forall(
      X, Y, Z, z3::implies(Def(X, Y) && Use(X, Z) && In(Z, Y), Edge(Y, Z)));
  Solver->add_rule(edge_rule, C.str_symbol("edge_rule"));

  // path_rule1: Path(X, Y) := Edge(X, Y) & Taint(X)
  z3::expr path_rule1 =
      z3::forall(X, Y, z3::implies(Edge(X, Y) && Taint(X), Path(X, Y)));
  Solver->add_rule(path_rule1, C.str_symbol("path_rule1"));

  // path_rule2: Path(X, Z) := Path(X, Y) & Edge(Y, Z) & !Sanitizer(Y)
  z3::expr path_rule2 = z3::forall(
      X, Y, Z,
      z3::implies(Path(X, Y) && Edge(Y, Z) && !Sanitizer(Y), Path(X, Z)));
  Solver->add_rule(path_rule2, C.str_symbol("path_rule2"));

  // alarm_rule: Alarm(Z) := Path(X, Z) & Def(Y, X) & Div(Y, Z)
  z3::expr alarm_rule = z3::forall(
      X, Y, Z, z3::implies(Taint(X) && Path(X, Z) && Div(Y, Z), Alarm(Z)));
  Solver->add_rule(alarm_rule, C.str_symbol("alarm_rule"));
}

void Extractor::addDef(const InstMapTy &InstMap, Value *X, Instruction *L) {
  if (InstMap.find(X) == InstMap.end())
    return;
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(L)};
  Solver->add_fact(Def, Arr);
}

void Extractor::addUse(const InstMapTy &InstMap, Value *X, Instruction *L) {
  if (Constant *C = dyn_cast<Constant>(X))
    return;
  if (InstMap.find(X) == InstMap.end())
    return;
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(L)};
  Solver->add_fact(Use, Arr);
}

void Extractor::addDiv(const InstMapTy &InstMap, Value *X, Instruction *L) {
  if (Constant *C = dyn_cast<Constant>(X))
    return;
  if (InstMap.find(X) == InstMap.end())
    return;
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(L)};
  Solver->add_fact(Div, Arr);
}

void Extractor::addTaint(const InstMapTy &InstMap, Instruction *L) {
  unsigned int Arr[1] = {InstMap.at(L)};
  Solver->add_fact(Taint, Arr);
}

void Extractor::addSanitizer(const InstMapTy &InstMap, Instruction *L) {
  unsigned int Arr[1] = {InstMap.at(L)};
  Solver->add_fact(Sanitizer, Arr);
}

void Extractor::addGen(const InstMapTy &InstMap, Instruction *X, Value *Y) {
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(Y)};
  Solver->add_fact(Gen, Arr);
}

void Extractor::addNext(const InstMapTy &InstMap, Instruction *X,
                        Instruction *Y) {
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(Y)};
  Solver->add_fact(Next, Arr);
};

/*
 * Implement the following function that collects Datalog facts for each
 * instruction.
 */
void Extractor::extractConstraints(const InstMapTy &InstMap, Instruction *I) {
  /* Add your code here */
  if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
    Value *From = SI->getValueOperand();
    Value *To = SI->getPointerOperand();
    addGen(InstMap, SI, SI);
    addDef(InstMap, To, SI);
    addUse(InstMap, From, SI);
    if (Constant *C = dyn_cast<Constant>(From))
      if (C->isZeroValue())
        addTaint(InstMap, SI);
  } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
    Value *V = LI->getPointerOperand();
    addGen(InstMap, LI, LI);
    addDef(InstMap, LI, LI);
    addUse(InstMap, V, LI);
  } else if (CallInst *CI = dyn_cast<CallInst>(I)) {
    if (isTaintedInput(CI))
      addTaint(InstMap, CI);
    else if (isSanitizer(CI))
      addSanitizer(InstMap, CI);
    else
      for (Value *A : CI->args())
        addUse(InstMap, A, CI);
    addDef(InstMap, CI, CI);
    addGen(InstMap, CI, CI);
  } else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(I)) {
    if (BO->getOpcode() == Instruction::SDiv)
      addDiv(InstMap, BO->getOperand(1), BO);
    addUse(InstMap, BO->getOperand(0), BO);
    addUse(InstMap, BO->getOperand(1), BO);
  }

  std::vector<Instruction *> Preds = getPredecessors(I);
  for (Instruction *P : Preds) {
    addNext(InstMap, P, I);
  }
}
