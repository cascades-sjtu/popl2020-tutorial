#include "Instrument.h"

using namespace llvm;

namespace instrument {

// declare DSE instrument functions
void declare(Module *M, LLVMContext &C, IRBuilder<> Builder) {
  // declare void __DSE_Init__()
  FunctionType *DSEInitFT = FunctionType::get(Type::getVoidTy(C), false);
  Function *DSEInitFunction = Function::Create(
      DSEInitFT, Function::ExternalLinkage, DSEInitFunctionName, M);
  DSEInitFunction->setDSOLocal(true);

  // declare void __DSE_Branch__(int R, int *Ptr)
  FunctionType *DSEBranchFT = FunctionType::get(
      Type::getVoidTy(C),
      {Type::getInt32Ty(C), Type::getInt32Ty(C), Type::getInt32Ty(C)}, false);
  Function *DSEBranchFuntion = Function::Create(
      DSEBranchFT, Function::ExternalLinkage, DSEBranchFunctionName, M);
  DSEBranchFuntion->setDSOLocal(true);

  // declare void __DSE_Const__(int X)
  FunctionType *DSEConstFT =
      FunctionType::get(Type::getVoidTy(C), Type::getInt32Ty(C), false);
  Function *DSEConstFuntion = Function::Create(
      DSEConstFT, Function::ExternalLinkage, DSEConstFunctionName, M);
  DSEConstFuntion->setDSOLocal(true);

  // declare void _DSE_Register_(int X)
  FunctionType *DSERegisterFT =
      FunctionType::get(Type::getVoidTy(C), Type::getInt32Ty(C), false);
  Function *DSERegisterFuntion = Function::Create(
      DSERegisterFT, Function::ExternalLinkage, DSERegisterFunctionName, M);
  DSERegisterFuntion->setDSOLocal(true);

  // declare void __DSE_Alloca__(int R, int *Ptr)
  FunctionType *DSEAllocaFT = FunctionType::get(
      Type::getVoidTy(C), {Type::getInt32Ty(C), Type::getInt32PtrTy(C)}, false);
  Function *DSEAllocaFuntion = Function::Create(
      DSEAllocaFT, Function::ExternalLinkage, DSEAllocaFunctionName, M);
  DSEAllocaFuntion->setDSOLocal(true);

  // declare void __DSE_Store__(int X)
  FunctionType *DSEStoreFT =
      FunctionType::get(Type::getVoidTy(C), Type::getInt32Ty(C), false);
  Function *DSEStoreFuntion = Function::Create(
      DSEStoreFT, Function::ExternalLinkage, DSEStoreFunctionName, M);
  DSEStoreFuntion->setDSOLocal(true);

  // declare void __DSE_Load__(int Y, int *X)
  FunctionType *DSELoadFT = FunctionType::get(
      Type::getVoidTy(C), {Type::getInt32Ty(C), Type::getInt32PtrTy(C)}, false);
  Function *DSELoadFuntion = Function::Create(
      DSELoadFT, Function::ExternalLinkage, DSELoadFunctionName, M);
  DSELoadFuntion->setDSOLocal(true);

  // declare void __DSE_ICmp__(int R, int Op)
  FunctionType *DSEICmpFT = FunctionType::get(
      Type::getVoidTy(C), {Type::getInt32Ty(C), Type::getInt32Ty(C)}, false);
  Function *DSEICmpFuntion = Function::Create(
      DSEICmpFT, Function::ExternalLinkage, DSEICmpFunctionName, M);
  DSEICmpFuntion->setDSOLocal(true);

  // declare void __DSE_BinOp__(int R, int Op)
  FunctionType *DSEBinOpFT = FunctionType::get(
      Type::getVoidTy(C), {Type::getInt32Ty(C), Type::getInt32Ty(C)}, false);
  Function *DSEBinOpFuntion = Function::Create(
      DSEBinOpFT, Function::ExternalLinkage, DSEBinOpFunctionName, M);
  DSEBinOpFuntion->setDSOLocal(true);
}

void push(Value *V, Module *M, LLVMContext &C, IRBuilder<> Builder) {
  // push constant
  if (ConstantInt *CI = dyn_cast<ConstantInt>(V))
    Builder.CreateCall(M->getFunction(DSEConstFunctionName), V);
  // push register
  else
    Builder.CreateCall(M->getFunction(DSERegisterFunctionName),
                       ConstantInt::get(Type::getInt32Ty(C), getRegisterID(V)));
}

/*
 * Implement your instrumentation for dynamic symbolic execution engine
 */
bool Instrument::runOnFunction(Function &F) {
  /* Add your code here */
  Module *M = F.getParent();
  LLVMContext &C = M->getContext();
  IRBuilder<> Builder(C);
  declare(M, C, Builder);

  // insert call to __DSE_Init__()
  Builder.SetInsertPoint(F.getEntryBlock().getFirstNonPHI());
  Builder.CreateCall(M->getFunction(DSEInitFunctionName));

  // instrument DSE code on instruction level
  for (BasicBlock &B : F) {
    for (Instruction &I : B) {
      IRBuilder<> Builder(&I);
      if (AllocaInst *AI = dyn_cast<AllocaInst>(&I)) {
        Builder.SetInsertPoint(AI->getNextNode());
        Builder.CreateCall(
            M->getFunction(DSEAllocaFunctionName),
            {ConstantInt::get(Type::getInt32Ty(C), getRegisterID(AI)), AI});
      } else if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
        Value *From = SI->getValueOperand();
        Value *To = SI->getPointerOperand();
        Builder.SetInsertPoint(SI->getNextNode());
        push(From, M, C, Builder);
        Builder.CreateCall(
            M->getFunction(DSEStoreFunctionName),
            ConstantInt::get(Type::getInt32Ty(C), getRegisterID(To)));
      } else if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
        Value *From = LI->getPointerOperand();
        Builder.SetInsertPoint(LI->getNextNode());
        Builder.CreateCall(
            M->getFunction(DSELoadFunctionName),
            {ConstantInt::get(Type::getInt32Ty(C), getRegisterID(LI)), From});
      } else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(&I)) {
        Builder.SetInsertPoint(BO->getNextNode());
        push(BO->getOperand(0), M, C, Builder);
        push(BO->getOperand(1), M, C, Builder);
        Builder.CreateCall(
            M->getFunction(DSEBinOpFunctionName),
            {ConstantInt::get(Type::getInt32Ty(C), getRegisterID(BO)),
             ConstantInt::get(Type::getInt32Ty(C), BO->getOpcode())});

      } else if (ICmpInst *IC = dyn_cast<ICmpInst>(&I)) {
      }
    }
  }
  return true;
}

char Instrument::ID = 1;
static RegisterPass<Instrument>
    X("Instrument", "Instrumentations for Dynamic Symbolic Execution", false,
      false);

} // namespace instrument
