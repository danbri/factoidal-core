import L4Factoidal.JS.FuelMonoStepsBEvalExpr

namespace L4Factoidal.JS.FuelMono
open L4Factoidal.JS

/-- Out of fuel at 0: every function of the block but `iterResult`, which uses no fuel
(`vmLoop` puts the registers back in the heap first). -/
theorem IH_zero {H : Type} (t1 t2 : Mode) (m : Nat) : IH H t1 t2 0 m where
  h_getV := fun a0 a1 => Le.unfold (getV.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_getProto := fun a0 a1 a2 => Le.unfold (getProto.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_proxyTrap := fun a0 a1 => Le.unfold (proxyTrap.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_hasProp := fun a0 a1 => Le.unfold (hasProp.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_getRecv := fun a0 a1 a2 => Le.unfold (getRecv.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_ownKeysOf := fun a0 => Le.unfold (ownKeysOf.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_ownDesc := fun a0 a1 => Le.unfold (ownDesc.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_putV := fun a0 a1 a2 a3 => Le.unfold (putV.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_toPrim := fun a0 a1 => Le.unfold (toPrim.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_tryMethods := fun a0 a1 => Le.unfold (tryMethods.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_toNum := fun a0 => Le.unfold (toNum.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_toBigInt := fun a0 => Le.unfold (toBigInt.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_typedConv := fun a0 a1 => Le.unfold (typedConv.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_toStr := fun a0 => Le.unfold (toStr.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_toKey := fun a0 => Le.unfold (toKey.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_toObj := fun a0 => Le.unfold (toObj.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_looseEq := fun a0 a1 => Le.unfold (looseEq.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_lessThan := fun a0 a1 a2 => Le.unfold (lessThan.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_instOf := fun a0 a1 => Le.unfold (instOf.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_binop := fun a0 a1 a2 => Le.unfold (binop.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_callV := fun a0 a1 a2 => Le.unfold (callV.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_callClosure := fun a0 a1 a2 a3 a4 a5 a6 a7 a8 => Le.unfold (callClosure.eq_def (md := t1) _ _ _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_callBody := fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 => Le.unfold (callBody.eq_def (md := t1) _ _ _ _ _ _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_bindParams := fun a0 a1 a2 a3 => Le.unfold (bindParams.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_evalNamed := fun a0 a1 a2 => Le.unfold (evalNamed.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_initFields := fun a0 a1 a2 => Le.unfold (initFields.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_protoFromCtor := fun a0 a1 => Le.unfold (protoFromCtor.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_constructNative := fun a0 a1 a2 a3 => Le.unfold (constructNative.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_construct := fun a0 a1 a2 => Le.unfold (construct.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_evalBody := fun a0 a1 => Le.unfold (evalBody.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_enterBlock := fun a0 a1 => Le.unfold (enterBlock.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_declareLexical := fun a0 a1 => Le.unfold (declareLexical.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_evalStmts := fun a0 a1 => Le.unfold (evalStmts.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_evalBlock := fun a0 a1 => Le.unfold (evalBlock.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_assignName := fun a0 a1 a2 => Le.unfold (assignName.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_lookupLocal := fun a0 a1 a2 a3 => Le.unfold (lookupLocal.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_assignLocal := fun a0 a1 a2 a3 a4 => Le.unfold (assignLocal.eq_def (md := t1) _ _ _ _ _ _) rfl (Le.fuel _)
  h_namedGlobal := fun a0 => Le.unfold (namedGlobal.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_lookup := fun a0 a1 => Le.unfold (lookup.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_putTarget := fun a0 a1 a2 a3 a4 => Le.unfold (putTarget.eq_def (md := t1) _ _ _ _ _ _) rfl (Le.fuel _)
  h_evalRef := fun a0 a1 => Le.unfold (evalRef.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_getRef := fun a0 a1 a2 a3 => Le.unfold (getRef.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_evalArgs := fun a0 a1 a2 => Le.unfold (evalArgs.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_evalArg := fun a0 a1 a2 a3 => Le.unfold (evalArg.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_evalProps := fun a0 a1 a2 => Le.unfold (evalProps.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_evalExpr := fun a0 a1 => Le.unfold (evalExpr.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_whileLoop := fun a0 a1 a2 a3 => Le.unfold (whileLoop.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_doLoop := fun a0 a1 a2 a3 => Le.unfold (doLoop.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_forLoop := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (forLoop.eq_def (md := t1) _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_copyEnv := fun a0 a1 => Le.unfold (copyEnv.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_forInLoop := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (forInLoop.eq_def (md := t1) _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_bindIter := fun a0 a1 a2 a3 => Le.unfold (bindIter.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_forOfLoop := fun a0 a1 a2 a3 a4 a5 => Le.unfold (forOfLoop.eq_def (md := t1) _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_switchFind := fun a0 a1 a2 a3 => Le.unfold (switchFind.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_runCases := fun a0 a1 => Le.unfold (runCases.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_evalDecls := fun a0 a1 a2 => Le.unfold (evalDecls.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_evalStmt := fun a0 a1 a2 => Le.unfold (evalStmt.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_bindPat := fun a0 a1 a2 a3 => Le.unfold (bindPat.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_bindProps := fun a0 a1 a2 a3 a4 => Le.unfold (bindProps.eq_def (md := t1) _ _ _ _ _ _) rfl (Le.fuel _)
  h_bindElems := fun a0 a1 a2 a3 a4 => Le.unfold (bindElems.eq_def (md := t1) _ _ _ _ _ _) rfl (Le.fuel _)
  h_copyDataProps := fun a0 a1 a2 => Le.unfold (copyDataProps.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_getIterator := fun a0 => Le.unfold (getIterator.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_iterStep := fun a0 => Le.unfold (iterStep.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_iterClose := fun a0 => Le.unfold (iterClose.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_iterToArray := fun a0 a1 => Le.unfold (iterToArray.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_iterCloseAbrupt := fun a0 a1 => Le.unfold (iterCloseAbrupt.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_getSuper := fun a0 a1 a2 => Le.unfold (getSuper.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_superCall := fun a0 a1 => Le.unfold (superCall.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_evalClass := fun a0 a1 a2 => Le.unfold (evalClass.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_defineMembers := fun a0 a1 a2 a3 a4 => Le.unfold (defineMembers.eq_def (md := t1) _ _ _ _ _ _) rfl (Le.fuel _)
  h_directEval := fun a0 a1 => Le.unfold (directEval.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_evalCompletion := fun a0 a1 a2 => Le.unfold (evalCompletion.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_genRun := fun a0 a1 => Le.unfold (genRun.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_genEval := fun a0 a1 => Le.unfold (genEval.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_genEnter := fun a0 a1 a2 a3 => Le.unfold (genEnter.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_genUnsupported := fun a0 => Le.unfold (genUnsupported.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_genLift := fun a0 a1 a2 => Le.unfold (genLift.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_genUnwind := fun a0 a1 => Le.unfold (genUnwind.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_asyncStep := fun a0 a1 => Le.unfold (asyncStep.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_promiseResolve := fun a0 => Le.unfold (promiseResolve.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_resolvePromise := fun a0 a1 => Le.unfold (resolvePromise.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_rejectPromise := fun a0 a1 => Le.unfold (rejectPromise.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_settlePromise := fun a0 a1 a2 => Le.unfold (settlePromise.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_performThen := fun a0 a1 a2 a3 => Le.unfold (performThen.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_runJobs := Le.unfold (runJobs.eq_def (md := t1) _ ) rfl (Le.fuel _)
  h_iterResult := fun a0 a1 => Le.unfold (iterResult.eq_def (md := t1) _ _ _) (iterResult.eq_def (md := t2) _ _ _) (by cases m <;> exact Le.refl _)
  h_agenDrain := fun a0 => Le.unfold (agenDrain.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_agenAwait := fun a0 a1 a2 a3 => Le.unfold (agenAwait.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_agenRun := fun a0 a1 a2 => Le.unfold (agenRun.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_coreRun := fun a0 => Le.unfold (coreRun.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_callNative := fun a0 a1 a2 a3 => Le.unfold (callNative.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_vmGlobalMiss := fun a0 a1 a2 a3 => Le.unfold (vmGlobalMiss.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_vmUnary := fun a0 a1 => Le.unfold (vmUnary.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_vmGetIndex := fun a0 a1 => Le.unfold (vmGetIndex.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_vmLoop := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (vmLoop.eq_def (md := t1) _ _ _ _ _ _ _ _) rfl (Le.of_out fun _ => ⟨_, rfl⟩)
  h_vmEnter := fun a0 a1 a2 a3 a4 => Le.unfold (vmEnter.eq_def (md := t1) _ _ _ _ _ _) rfl (Le.fuel _)
  h_genericPush := fun a0 a1 => Le.unfold (genericPush.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_arraySpliceGeneric := fun a0 a1 => Le.unfold (arraySpliceGeneric.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_deleteProp := fun a0 a1 => Le.unfold (deleteProp.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_deleteOrThrow := fun a0 a1 => Le.unfold (deleteOrThrow.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_jsonRevive := fun a0 a1 a2 a3 a4 => Le.unfold (jsonRevive.eq_def (md := t1) _ _ _ _ _ _) rfl (Le.fuel _)
  h_arrayGeneric := fun a0 a1 a2 => Le.unfold (arrayGeneric.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_speciesFrom := fun a0 a1 => Le.unfold (speciesFrom.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_speciesFill := fun a0 a1 a2 => Le.unfold (speciesFill.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_elemsOf := fun a0 => Le.unfold (elemsOf.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_elemAt := fun a0 a1 a2 => Le.unfold (elemAt.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_iterArray := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (iterArray.eq_def (md := t1) _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_reduceArray := fun a0 a1 a2 a3 a4 => Le.unfold (reduceArray.eq_def (md := t1) _ _ _ _ _ _) rfl (Le.fuel _)
  h_arrayLikeLength := fun a0 => Le.unfold (arrayLikeLength.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_sortGt := fun a0 a1 a2 => Le.unfold (sortGt.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_mergeSort := fun a0 a1 => Le.unfold (mergeSort.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_merge := fun a0 a1 a2 a3 => Le.unfold (merge.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_toPropDesc := fun a0 => Le.unfold (toPropDesc.eq_def (md := t1) _ _) rfl (Le.fuel _)
  h_defineOwnProp := fun a0 a1 a2 => Le.unfold (defineOwnProp.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_defineFromDescriptor := fun a0 a1 a2 => Le.unfold (defineFromDescriptor.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_jsonSer := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (jsonSer.eq_def (md := t1) _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_jsonStr := fun a0 a1 => Le.unfold (jsonStr.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_regexExec := fun a0 a1 => Le.unfold (regexExec.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_regExpExecG := fun a0 a1 => Le.unfold (regExpExecG.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_speciesCtor := fun a0 a1 => Le.unfold (speciesCtor.eq_def (md := t1) _ _ _) rfl (Le.fuel _)
  h_matchArray := fun a0 a1 a2 => Le.unfold (matchArray.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_stringSymDispatch := fun a0 a1 a2 => Le.unfold (stringSymDispatch.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_regexpSymbol := fun a0 a1 a2 => Le.unfold (regexpSymbol.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_extraNative := fun a0 a1 a2 a3 => Le.unfold (extraNative.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)
  h_stringOrMath := fun a0 a1 a2 => Le.unfold (stringOrMath.eq_def (md := t1) _ _ _ _) rfl (Le.fuel _)
  h_moreNative := fun a0 a1 a2 a3 => Le.unfold (moreNative.eq_def (md := t1) _ _ _ _ _) rfl (Le.fuel _)

/-- Fuel monotonicity of the whole block: every function at fuel `n` against every `m ≥ n`. -/
theorem IH_all {H : Type} (t1 t2 : Mode) (hb : t1.tier1 = true → t2.tier1 = true) :
    (m n : Nat) → n ≤ m → IH H t1 t2 n m
  | m, 0, _ => IH_zero t1 t2 m
  | 0, _ + 1, h => absurd h (by omega)
  | m + 1, n + 1, h =>
    have ih := IH_all t1 t2 hb m n (by omega)
    have ihs : ∀ k, k ≤ n → IH H t1 t2 k m := fun k hk => IH_all t1 t2 hb m k (by omega)
    { h_getV := getV_step t1 t2 hb n m ih ihs,
      h_getProto := getProto_step t1 t2 hb n m ih ihs,
      h_proxyTrap := proxyTrap_step t1 t2 hb n m ih ihs,
      h_hasProp := hasProp_step t1 t2 hb n m ih ihs,
      h_getRecv := getRecv_step t1 t2 hb n m ih ihs,
      h_ownKeysOf := ownKeysOf_step t1 t2 hb n m ih ihs,
      h_ownDesc := ownDesc_step t1 t2 hb n m ih ihs,
      h_putV := putV_step t1 t2 hb n m ih ihs,
      h_toPrim := toPrim_step t1 t2 hb n m ih ihs,
      h_tryMethods := tryMethods_step t1 t2 hb n m ih ihs,
      h_toNum := toNum_step t1 t2 hb n m ih ihs,
      h_toBigInt := toBigInt_step t1 t2 hb n m ih ihs,
      h_typedConv := typedConv_step t1 t2 hb n m ih ihs,
      h_toStr := toStr_step t1 t2 hb n m ih ihs,
      h_toKey := toKey_step t1 t2 hb n m ih ihs,
      h_toObj := toObj_step t1 t2 hb n m ih ihs,
      h_looseEq := looseEq_step t1 t2 hb n m ih ihs,
      h_lessThan := lessThan_step t1 t2 hb n m ih ihs,
      h_instOf := instOf_step t1 t2 hb n m ih ihs,
      h_binop := binop_step t1 t2 hb n m ih ihs,
      h_callV := callV_step t1 t2 hb n m ih ihs,
      h_callClosure := callClosure_step t1 t2 hb n m ih ihs,
      h_callBody := callBody_step t1 t2 hb n m ih ihs,
      h_bindParams := bindParams_step t1 t2 hb n m ih ihs,
      h_evalNamed := evalNamed_step t1 t2 hb n m ih ihs,
      h_initFields := initFields_step t1 t2 hb n m ih ihs,
      h_protoFromCtor := protoFromCtor_step t1 t2 hb n m ih ihs,
      h_constructNative := constructNative_step t1 t2 hb n m ih ihs,
      h_construct := construct_step t1 t2 hb n m ih ihs,
      h_evalBody := evalBody_step t1 t2 hb n m ih ihs,
      h_enterBlock := enterBlock_step t1 t2 hb n m ih ihs,
      h_declareLexical := declareLexical_step t1 t2 hb n m ih ihs,
      h_evalStmts := evalStmts_step t1 t2 hb n m ih ihs,
      h_evalBlock := evalBlock_step t1 t2 hb n m ih ihs,
      h_assignName := assignName_step t1 t2 hb n m ih ihs,
      h_lookupLocal := lookupLocal_step t1 t2 hb n m ih ihs,
      h_assignLocal := assignLocal_step t1 t2 hb n m ih ihs,
      h_namedGlobal := namedGlobal_step t1 t2 hb n m ih ihs,
      h_lookup := lookup_step t1 t2 hb n m ih ihs,
      h_putTarget := putTarget_step t1 t2 hb n m ih ihs,
      h_evalRef := evalRef_step t1 t2 hb n m ih ihs,
      h_getRef := getRef_step t1 t2 hb n m ih ihs,
      h_evalArgs := evalArgs_step t1 t2 hb n m ih ihs,
      h_evalArg := evalArg_step t1 t2 hb n m ih ihs,
      h_evalProps := evalProps_step t1 t2 hb n m ih ihs,
      h_evalExpr := evalExpr_step t1 t2 hb n m ih ihs,
      h_whileLoop := whileLoop_step t1 t2 hb n m ih ihs,
      h_doLoop := doLoop_step t1 t2 hb n m ih ihs,
      h_forLoop := forLoop_step t1 t2 hb n m ih ihs,
      h_copyEnv := copyEnv_step t1 t2 hb n m ih ihs,
      h_forInLoop := forInLoop_step t1 t2 hb n m ih ihs,
      h_bindIter := bindIter_step t1 t2 hb n m ih ihs,
      h_forOfLoop := forOfLoop_step t1 t2 hb n m ih ihs,
      h_switchFind := switchFind_step t1 t2 hb n m ih ihs,
      h_runCases := runCases_step t1 t2 hb n m ih ihs,
      h_evalDecls := evalDecls_step t1 t2 hb n m ih ihs,
      h_evalStmt := evalStmt_step t1 t2 hb n m ih ihs,
      h_bindPat := bindPat_step t1 t2 hb n m ih ihs,
      h_bindProps := bindProps_step t1 t2 hb n m ih ihs,
      h_bindElems := bindElems_step t1 t2 hb n m ih ihs,
      h_copyDataProps := copyDataProps_step t1 t2 hb n m ih ihs,
      h_getIterator := getIterator_step t1 t2 hb n m ih ihs,
      h_iterStep := iterStep_step t1 t2 hb n m ih ihs,
      h_iterClose := iterClose_step t1 t2 hb n m ih ihs,
      h_iterToArray := iterToArray_step t1 t2 hb n m ih ihs,
      h_iterCloseAbrupt := iterCloseAbrupt_step t1 t2 hb n m ih ihs,
      h_getSuper := getSuper_step t1 t2 hb n m ih ihs,
      h_superCall := superCall_step t1 t2 hb n m ih ihs,
      h_evalClass := evalClass_step t1 t2 hb n m ih ihs,
      h_defineMembers := defineMembers_step t1 t2 hb n m ih ihs,
      h_directEval := directEval_step t1 t2 hb n m ih ihs,
      h_evalCompletion := evalCompletion_step t1 t2 hb n m ih ihs,
      h_genRun := genRun_step t1 t2 hb n m ih ihs,
      h_genEval := genEval_step t1 t2 hb n m ih ihs,
      h_genEnter := genEnter_step t1 t2 hb n m ih ihs,
      h_genUnsupported := genUnsupported_step t1 t2 hb n m ih ihs,
      h_genLift := genLift_step t1 t2 hb n m ih ihs,
      h_genUnwind := genUnwind_step t1 t2 hb n m ih ihs,
      h_asyncStep := asyncStep_step t1 t2 hb n m ih ihs,
      h_promiseResolve := promiseResolve_step t1 t2 hb n m ih ihs,
      h_resolvePromise := resolvePromise_step t1 t2 hb n m ih ihs,
      h_rejectPromise := rejectPromise_step t1 t2 hb n m ih ihs,
      h_settlePromise := settlePromise_step t1 t2 hb n m ih ihs,
      h_performThen := performThen_step t1 t2 hb n m ih ihs,
      h_runJobs := runJobs_step t1 t2 hb n m ih ihs,
      h_iterResult := iterResult_step t1 t2 hb n m ih ihs,
      h_agenDrain := agenDrain_step t1 t2 hb n m ih ihs,
      h_agenAwait := agenAwait_step t1 t2 hb n m ih ihs,
      h_agenRun := agenRun_step t1 t2 hb n m ih ihs,
      h_coreRun := coreRun_step t1 t2 hb n m ih ihs,
      h_callNative := callNative_step t1 t2 hb n m ih ihs,
      h_vmGlobalMiss := vmGlobalMiss_step t1 t2 hb n m ih ihs,
      h_vmUnary := vmUnary_step t1 t2 hb n m ih ihs,
      h_vmGetIndex := vmGetIndex_step t1 t2 hb n m ih ihs,
      h_vmLoop := vmLoop_step t1 t2 hb n m ih ihs,
      h_vmEnter := vmEnter_step t1 t2 hb n m ih ihs,
      h_genericPush := genericPush_step t1 t2 hb n m ih ihs,
      h_arraySpliceGeneric := arraySpliceGeneric_step t1 t2 hb n m ih ihs,
      h_deleteProp := deleteProp_step t1 t2 hb n m ih ihs,
      h_deleteOrThrow := deleteOrThrow_step t1 t2 hb n m ih ihs,
      h_jsonRevive := jsonRevive_step t1 t2 hb n m ih ihs,
      h_arrayGeneric := arrayGeneric_step t1 t2 hb n m ih ihs,
      h_speciesFrom := speciesFrom_step t1 t2 hb n m ih ihs,
      h_speciesFill := speciesFill_step t1 t2 hb n m ih ihs,
      h_elemsOf := elemsOf_step t1 t2 hb n m ih ihs,
      h_elemAt := elemAt_step t1 t2 hb n m ih ihs,
      h_iterArray := iterArray_step t1 t2 hb n m ih ihs,
      h_reduceArray := reduceArray_step t1 t2 hb n m ih ihs,
      h_arrayLikeLength := arrayLikeLength_step t1 t2 hb n m ih ihs,
      h_sortGt := sortGt_step t1 t2 hb n m ih ihs,
      h_mergeSort := mergeSort_step t1 t2 hb n m ih ihs,
      h_merge := merge_step t1 t2 hb n m ih ihs,
      h_toPropDesc := toPropDesc_step t1 t2 hb n m ih ihs,
      h_defineOwnProp := defineOwnProp_step t1 t2 hb n m ih ihs,
      h_defineFromDescriptor := defineFromDescriptor_step t1 t2 hb n m ih ihs,
      h_jsonSer := jsonSer_step t1 t2 hb n m ih ihs,
      h_jsonStr := jsonStr_step t1 t2 hb n m ih ihs,
      h_regexExec := regexExec_step t1 t2 hb n m ih ihs,
      h_regExpExecG := regExpExecG_step t1 t2 hb n m ih ihs,
      h_speciesCtor := speciesCtor_step t1 t2 hb n m ih ihs,
      h_matchArray := matchArray_step t1 t2 hb n m ih ihs,
      h_stringSymDispatch := stringSymDispatch_step t1 t2 hb n m ih ihs,
      h_regexpSymbol := regexpSymbol_step t1 t2 hb n m ih ihs,
      h_extraNative := extraNative_step t1 t2 hb n m ih ihs,
      h_stringOrMath := stringOrMath_step t1 t2 hb n m ih ihs,
      h_moreNative := moreNative_step t1 t2 hb n m ih ihs }

/-- Fuel monotonicity of statement lists, in the words of a run: in any mode `t` and from any
heap (the register machine on or off, any host and `hostCall`), if `evalStmts` at fuel `n` ends
with anything but `halt "fuel"`, it ends with the same result at every fuel `m ≥ n`: the same
value or completion and the same heap, so the same output, jobs, host state and steps left (a
host call receives the steps left, so it sees the same count at every call). -/
theorem evalStmts_fuel_mono {H : Type} (t : Mode) {n m : Nat} (h : n ≤ m) (ctx : Ctx) (ss : List Stmt)
    (s : HeapOf H) (hn : ¬ Out (evalStmts (md := t) n ctx ss s)) :
    evalStmts (md := t) m ctx ss s = evalStmts (md := t) n ctx ss s :=
  ((IH_all t t id m n h).h_evalStmts ctx ss).eq_of_not_out s hn

/-- The same for a call of a function value. -/
theorem callV_fuel_mono {H : Type} (t : Mode) {n m : Nat} (h : n ≤ m) (f thisV : Value) (args : Array Value)
    (s : HeapOf H) (hn : ¬ Out (callV (md := t) n f thisV args s)) :
    callV (md := t) m f thisV args s = callV (md := t) n f thisV args s :=
  ((IH_all t t id m n h).h_callV f thisV args).eq_of_not_out s hn

/-- The same for an expression. -/
theorem evalExpr_fuel_mono {H : Type} (t : Mode) {n m : Nat} (h : n ≤ m) (ctx : Ctx) (e : Expr)
    (s : HeapOf H) (hn : ¬ Out (evalExpr (md := t) n ctx e s)) :
    evalExpr (md := t) m ctx e s = evalExpr (md := t) n ctx e s :=
  ((IH_all t t id m n h).h_evalExpr ctx e).eq_of_not_out s hn

/-- **Tier 1 composes.** For every host, heap `s`, context and statement list: if the reference
(`Mode.ref`, the evaluator with no tier on) at fuel `n` ends with anything but `halt "fuel"`,
then the engine with tier 1 on (`Mode.engine`) ends at every fuel `m ≥ n` with the same result:
the same value or completion and the same heap, so the same output, jobs, host state and steps
left at every host call. The two runs start from the same heap: the mode is a parameter of the
evaluator, not a field of the heap, and the function bodies in the heap are the same. -/
theorem tier1_evalStmts_refines {H : Type} {n m : Nat} (h : n ≤ m) (ctx : Ctx) (ss : List Stmt)
    (s : HeapOf H) (hn : ¬ Out (evalStmts (md := Mode.ref) n ctx ss s)) :
    evalStmts (md := Mode.engine) m ctx ss s = evalStmts (md := Mode.ref) n ctx ss s :=
  ((IH_all Mode.ref Mode.engine (fun h => Bool.noConfusion h) m n h).h_evalStmts ctx ss).eq_of_not_out s hn

/-- The same for a call of a function value. -/
theorem tier1_callV_refines {H : Type} {n m : Nat} (h : n ≤ m) (f thisV : Value) (args : Array Value)
    (s : HeapOf H) (hn : ¬ Out (callV (md := Mode.ref) n f thisV args s)) :
    callV (md := Mode.engine) m f thisV args s = callV (md := Mode.ref) n f thisV args s :=
  ((IH_all Mode.ref Mode.engine (fun h => Bool.noConfusion h) m n h).h_callV f thisV args).eq_of_not_out s hn

/-- The same for an expression. -/
theorem tier1_evalExpr_refines {H : Type} {n m : Nat} (h : n ≤ m) (ctx : Ctx) (e : Expr)
    (s : HeapOf H) (hn : ¬ Out (evalExpr (md := Mode.ref) n ctx e s)) :
    evalExpr (md := Mode.engine) m ctx e s = evalExpr (md := Mode.ref) n ctx e s :=
  ((IH_all Mode.ref Mode.engine (fun h => Bool.noConfusion h) m n h).h_evalExpr ctx e).eq_of_not_out s hn

#print axioms IH_all
#print axioms evalStmts_fuel_mono
#print axioms callV_fuel_mono
#print axioms evalExpr_fuel_mono
#print axioms tier1_evalStmts_refines
#print axioms tier1_callV_refines
#print axioms tier1_evalExpr_refines

end L4Factoidal.JS.FuelMono
