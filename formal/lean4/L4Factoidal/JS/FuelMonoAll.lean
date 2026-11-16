import L4Factoidal.JS.FuelMonoStepsBDefineOwnProp

namespace L4Factoidal.JS.FuelMono
open L4Factoidal.JS

/-- Out of fuel at 0: every function of the block but `iterResult`, which uses no fuel. -/
theorem IH_zero {H : Type} (m : Nat) : IH H 0 m where
  h_getV := fun a0 a1 => Le.unfold (getV.eq_def _ _ _) rfl (Le.fuel _)
  h_getProto := fun a0 a1 a2 => Le.unfold (getProto.eq_def _ _ _ _) rfl (Le.fuel _)
  h_proxyTrap := fun a0 a1 => Le.unfold (proxyTrap.eq_def _ _ _) rfl (Le.fuel _)
  h_hasProp := fun a0 a1 => Le.unfold (hasProp.eq_def _ _ _) rfl (Le.fuel _)
  h_getRecv := fun a0 a1 a2 => Le.unfold (getRecv.eq_def _ _ _ _) rfl (Le.fuel _)
  h_ownKeysOf := fun a0 => Le.unfold (ownKeysOf.eq_def _ _) rfl (Le.fuel _)
  h_ownDesc := fun a0 a1 => Le.unfold (ownDesc.eq_def _ _ _) rfl (Le.fuel _)
  h_putV := fun a0 a1 a2 a3 => Le.unfold (putV.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_toPrim := fun a0 a1 => Le.unfold (toPrim.eq_def _ _ _) rfl (Le.fuel _)
  h_tryMethods := fun a0 a1 => Le.unfold (tryMethods.eq_def _ _ _) rfl (Le.fuel _)
  h_toNum := fun a0 => Le.unfold (toNum.eq_def _ _) rfl (Le.fuel _)
  h_toBigInt := fun a0 => Le.unfold (toBigInt.eq_def _ _) rfl (Le.fuel _)
  h_typedConv := fun a0 a1 => Le.unfold (typedConv.eq_def _ _ _) rfl (Le.fuel _)
  h_toStr := fun a0 => Le.unfold (toStr.eq_def _ _) rfl (Le.fuel _)
  h_toKey := fun a0 => Le.unfold (toKey.eq_def _ _) rfl (Le.fuel _)
  h_toObj := fun a0 => Le.unfold (toObj.eq_def _ _) rfl (Le.fuel _)
  h_looseEq := fun a0 a1 => Le.unfold (looseEq.eq_def _ _ _) rfl (Le.fuel _)
  h_lessThan := fun a0 a1 a2 => Le.unfold (lessThan.eq_def _ _ _ _) rfl (Le.fuel _)
  h_instOf := fun a0 a1 => Le.unfold (instOf.eq_def _ _ _) rfl (Le.fuel _)
  h_binop := fun a0 a1 a2 => Le.unfold (binop.eq_def _ _ _ _) rfl (Le.fuel _)
  h_callV := fun a0 a1 a2 => Le.unfold (callV.eq_def _ _ _ _) rfl (Le.fuel _)
  h_callClosure := fun a0 a1 a2 a3 a4 a5 a6 a7 a8 => Le.unfold (callClosure.eq_def _ _ _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_callBody := fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 => Le.unfold (callBody.eq_def _ _ _ _ _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_bindParams := fun a0 a1 a2 a3 => Le.unfold (bindParams.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_evalNamed := fun a0 a1 a2 => Le.unfold (evalNamed.eq_def _ _ _ _) rfl (Le.fuel _)
  h_initFields := fun a0 a1 a2 => Le.unfold (initFields.eq_def _ _ _ _) rfl (Le.fuel _)
  h_protoFromCtor := fun a0 a1 => Le.unfold (protoFromCtor.eq_def _ _ _) rfl (Le.fuel _)
  h_constructNative := fun a0 a1 a2 a3 => Le.unfold (constructNative.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_construct := fun a0 a1 a2 => Le.unfold (construct.eq_def _ _ _ _) rfl (Le.fuel _)
  h_evalBody := fun a0 a1 => Le.unfold (evalBody.eq_def _ _ _) rfl (Le.fuel _)
  h_enterBlock := fun a0 a1 => Le.unfold (enterBlock.eq_def _ _ _) rfl (Le.fuel _)
  h_declareLexical := fun a0 a1 => Le.unfold (declareLexical.eq_def _ _ _) rfl (Le.fuel _)
  h_evalStmts := fun a0 a1 => Le.unfold (evalStmts.eq_def _ _ _) rfl (Le.fuel _)
  h_evalBlock := fun a0 a1 => Le.unfold (evalBlock.eq_def _ _ _) rfl (Le.fuel _)
  h_assignName := fun a0 a1 a2 => Le.unfold (assignName.eq_def _ _ _ _) rfl (Le.fuel _)
  h_lookupLocal := fun a0 a1 a2 a3 => Le.unfold (lookupLocal.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_assignLocal := fun a0 a1 a2 a3 a4 => Le.unfold (assignLocal.eq_def _ _ _ _ _ _) rfl (Le.fuel _)
  h_namedGlobal := fun a0 => Le.unfold (namedGlobal.eq_def _ _) rfl (Le.fuel _)
  h_lookup := fun a0 a1 => Le.unfold (lookup.eq_def _ _ _) rfl (Le.fuel _)
  h_putTarget := fun a0 a1 a2 a3 a4 => Le.unfold (putTarget.eq_def _ _ _ _ _ _) rfl (Le.fuel _)
  h_evalRef := fun a0 a1 => Le.unfold (evalRef.eq_def _ _ _) rfl (Le.fuel _)
  h_getRef := fun a0 a1 a2 a3 => Le.unfold (getRef.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_evalArgs := fun a0 a1 a2 => Le.unfold (evalArgs.eq_def _ _ _ _) rfl (Le.fuel _)
  h_evalArg := fun a0 a1 a2 a3 => Le.unfold (evalArg.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_evalProps := fun a0 a1 a2 => Le.unfold (evalProps.eq_def _ _ _ _) rfl (Le.fuel _)
  h_evalExpr := fun a0 a1 => Le.unfold (evalExpr.eq_def _ _ _) rfl (Le.fuel _)
  h_whileLoop := fun a0 a1 a2 a3 => Le.unfold (whileLoop.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_doLoop := fun a0 a1 a2 a3 => Le.unfold (doLoop.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_forLoop := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (forLoop.eq_def _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_copyEnv := fun a0 a1 => Le.unfold (copyEnv.eq_def _ _ _) rfl (Le.fuel _)
  h_forInLoop := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (forInLoop.eq_def _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_bindIter := fun a0 a1 a2 a3 => Le.unfold (bindIter.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_forOfLoop := fun a0 a1 a2 a3 a4 a5 => Le.unfold (forOfLoop.eq_def _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_switchFind := fun a0 a1 a2 a3 => Le.unfold (switchFind.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_runCases := fun a0 a1 => Le.unfold (runCases.eq_def _ _ _) rfl (Le.fuel _)
  h_evalDecls := fun a0 a1 a2 => Le.unfold (evalDecls.eq_def _ _ _ _) rfl (Le.fuel _)
  h_evalStmt := fun a0 a1 a2 => Le.unfold (evalStmt.eq_def _ _ _ _) rfl (Le.fuel _)
  h_bindPat := fun a0 a1 a2 a3 => Le.unfold (bindPat.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_bindProps := fun a0 a1 a2 a3 a4 => Le.unfold (bindProps.eq_def _ _ _ _ _ _) rfl (Le.fuel _)
  h_bindElems := fun a0 a1 a2 a3 a4 => Le.unfold (bindElems.eq_def _ _ _ _ _ _) rfl (Le.fuel _)
  h_copyDataProps := fun a0 a1 a2 => Le.unfold (copyDataProps.eq_def _ _ _ _) rfl (Le.fuel _)
  h_getIterator := fun a0 => Le.unfold (getIterator.eq_def _ _) rfl (Le.fuel _)
  h_iterStep := fun a0 => Le.unfold (iterStep.eq_def _ _) rfl (Le.fuel _)
  h_iterClose := fun a0 => Le.unfold (iterClose.eq_def _ _) rfl (Le.fuel _)
  h_iterToArray := fun a0 a1 => Le.unfold (iterToArray.eq_def _ _ _) rfl (Le.fuel _)
  h_iterCloseAbrupt := fun a0 a1 => Le.unfold (iterCloseAbrupt.eq_def _ _ _) rfl (Le.fuel _)
  h_getSuper := fun a0 a1 a2 => Le.unfold (getSuper.eq_def _ _ _ _) rfl (Le.fuel _)
  h_superCall := fun a0 a1 => Le.unfold (superCall.eq_def _ _ _) rfl (Le.fuel _)
  h_evalClass := fun a0 a1 a2 => Le.unfold (evalClass.eq_def _ _ _ _) rfl (Le.fuel _)
  h_defineMembers := fun a0 a1 a2 a3 a4 => Le.unfold (defineMembers.eq_def _ _ _ _ _ _) rfl (Le.fuel _)
  h_directEval := fun a0 a1 => Le.unfold (directEval.eq_def _ _ _) rfl (Le.fuel _)
  h_evalCompletion := fun a0 a1 a2 => Le.unfold (evalCompletion.eq_def _ _ _ _) rfl (Le.fuel _)
  h_genRun := fun a0 a1 => Le.unfold (genRun.eq_def _ _ _) rfl (Le.fuel _)
  h_genEval := fun a0 a1 => Le.unfold (genEval.eq_def _ _ _) rfl (Le.fuel _)
  h_genEnter := fun a0 a1 a2 a3 => Le.unfold (genEnter.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_genUnsupported := fun a0 => Le.unfold (genUnsupported.eq_def _ _) rfl (Le.fuel _)
  h_genLift := fun a0 a1 a2 => Le.unfold (genLift.eq_def _ _ _ _) rfl (Le.fuel _)
  h_genUnwind := fun a0 a1 => Le.unfold (genUnwind.eq_def _ _ _) rfl (Le.fuel _)
  h_asyncStep := fun a0 a1 => Le.unfold (asyncStep.eq_def _ _ _) rfl (Le.fuel _)
  h_promiseResolve := fun a0 => Le.unfold (promiseResolve.eq_def _ _) rfl (Le.fuel _)
  h_resolvePromise := fun a0 a1 => Le.unfold (resolvePromise.eq_def _ _ _) rfl (Le.fuel _)
  h_rejectPromise := fun a0 a1 => Le.unfold (rejectPromise.eq_def _ _ _) rfl (Le.fuel _)
  h_settlePromise := fun a0 a1 a2 => Le.unfold (settlePromise.eq_def _ _ _ _) rfl (Le.fuel _)
  h_performThen := fun a0 a1 a2 a3 => Le.unfold (performThen.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_runJobs := Le.unfold (runJobs.eq_def _ ) rfl (Le.fuel _)
  h_iterResult := fun a0 a1 => Le.unfold (iterResult.eq_def _ _ _) (iterResult.eq_def _ _ _) (by cases m <;> exact Le.refl _)
  h_agenDrain := fun a0 => Le.unfold (agenDrain.eq_def _ _) rfl (Le.fuel _)
  h_agenAwait := fun a0 a1 a2 a3 => Le.unfold (agenAwait.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_agenRun := fun a0 a1 a2 => Le.unfold (agenRun.eq_def _ _ _ _) rfl (Le.fuel _)
  h_coreRun := fun a0 => Le.unfold (coreRun.eq_def _ _) rfl (Le.fuel _)
  h_callNative := fun a0 a1 a2 a3 => Le.unfold (callNative.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_vmGlobalMiss := fun a0 a1 a2 a3 => Le.unfold (vmGlobalMiss.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_vmUnary := fun a0 a1 => Le.unfold (vmUnary.eq_def _ _ _) rfl (Le.fuel _)
  h_vmGetIndex := fun a0 a1 => Le.unfold (vmGetIndex.eq_def _ _ _) rfl (Le.fuel _)
  h_vmLoop := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (vmLoop.eq_def _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_vmEnter := fun a0 a1 a2 a3 a4 => Le.unfold (vmEnter.eq_def _ _ _ _ _ _) rfl (Le.fuel _)
  h_genericPush := fun a0 a1 => Le.unfold (genericPush.eq_def _ _ _) rfl (Le.fuel _)
  h_deleteOrThrow := fun a0 a1 => Le.unfold (deleteOrThrow.eq_def _ _ _) rfl (Le.fuel _)
  h_arrayGeneric := fun a0 a1 a2 => Le.unfold (arrayGeneric.eq_def _ _ _ _) rfl (Le.fuel _)
  h_speciesFrom := fun a0 a1 => Le.unfold (speciesFrom.eq_def _ _ _) rfl (Le.fuel _)
  h_speciesFill := fun a0 a1 a2 => Le.unfold (speciesFill.eq_def _ _ _ _) rfl (Le.fuel _)
  h_elemsOf := fun a0 => Le.unfold (elemsOf.eq_def _ _) rfl (Le.fuel _)
  h_elemAt := fun a0 a1 a2 => Le.unfold (elemAt.eq_def _ _ _ _) rfl (Le.fuel _)
  h_iterArray := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (iterArray.eq_def _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_reduceArray := fun a0 a1 a2 a3 a4 => Le.unfold (reduceArray.eq_def _ _ _ _ _ _) rfl (Le.fuel _)
  h_arrayLikeLength := fun a0 => Le.unfold (arrayLikeLength.eq_def _ _) rfl (Le.fuel _)
  h_sortGt := fun a0 a1 a2 => Le.unfold (sortGt.eq_def _ _ _ _) rfl (Le.fuel _)
  h_mergeSort := fun a0 a1 => Le.unfold (mergeSort.eq_def _ _ _) rfl (Le.fuel _)
  h_merge := fun a0 a1 a2 a3 => Le.unfold (merge.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_toPropDesc := fun a0 => Le.unfold (toPropDesc.eq_def _ _) rfl (Le.fuel _)
  h_defineOwnProp := fun a0 a1 a2 => Le.unfold (defineOwnProp.eq_def _ _ _ _) rfl (Le.fuel _)
  h_defineFromDescriptor := fun a0 a1 a2 => Le.unfold (defineFromDescriptor.eq_def _ _ _ _) rfl (Le.fuel _)
  h_jsonSer := fun a0 a1 a2 a3 a4 a5 a6 => Le.unfold (jsonSer.eq_def _ _ _ _ _ _ _ _) rfl (Le.fuel _)
  h_jsonStr := fun a0 a1 => Le.unfold (jsonStr.eq_def _ _ _) rfl (Le.fuel _)
  h_regexExec := fun a0 a1 => Le.unfold (regexExec.eq_def _ _ _) rfl (Le.fuel _)
  h_regExpExecG := fun a0 a1 => Le.unfold (regExpExecG.eq_def _ _ _) rfl (Le.fuel _)
  h_speciesCtor := fun a0 a1 => Le.unfold (speciesCtor.eq_def _ _ _) rfl (Le.fuel _)
  h_matchArray := fun a0 a1 a2 => Le.unfold (matchArray.eq_def _ _ _ _) rfl (Le.fuel _)
  h_stringSymDispatch := fun a0 a1 a2 => Le.unfold (stringSymDispatch.eq_def _ _ _ _) rfl (Le.fuel _)
  h_regexpSymbol := fun a0 a1 a2 => Le.unfold (regexpSymbol.eq_def _ _ _ _) rfl (Le.fuel _)
  h_extraNative := fun a0 a1 a2 a3 => Le.unfold (extraNative.eq_def _ _ _ _ _) rfl (Le.fuel _)
  h_stringOrMath := fun a0 a1 a2 => Le.unfold (stringOrMath.eq_def _ _ _ _) rfl (Le.fuel _)
  h_moreNative := fun a0 a1 a2 a3 => Le.unfold (moreNative.eq_def _ _ _ _ _) rfl (Le.fuel _)

/-- Fuel monotonicity of the whole block: every function at fuel `n` against every `m ≥ n`. -/
theorem IH_all {H : Type} : (n m : Nat) → n ≤ m → IH H n m
  | 0, m, _ => IH_zero m
  | _ + 1, 0, h => absurd h (by omega)
  | n + 1, m + 1, h =>
    have ih := IH_all n m (by omega)
    { h_getV := getV_step n m ih,
      h_getProto := getProto_step n m ih,
      h_proxyTrap := proxyTrap_step n m ih,
      h_hasProp := hasProp_step n m ih,
      h_getRecv := getRecv_step n m ih,
      h_ownKeysOf := ownKeysOf_step n m ih,
      h_ownDesc := ownDesc_step n m ih,
      h_putV := putV_step n m ih,
      h_toPrim := toPrim_step n m ih,
      h_tryMethods := tryMethods_step n m ih,
      h_toNum := toNum_step n m ih,
      h_toBigInt := toBigInt_step n m ih,
      h_typedConv := typedConv_step n m ih,
      h_toStr := toStr_step n m ih,
      h_toKey := toKey_step n m ih,
      h_toObj := toObj_step n m ih,
      h_looseEq := looseEq_step n m ih,
      h_lessThan := lessThan_step n m ih,
      h_instOf := instOf_step n m ih,
      h_binop := binop_step n m ih,
      h_callV := callV_step n m ih,
      h_callClosure := callClosure_step n m ih,
      h_callBody := callBody_step n m ih,
      h_bindParams := bindParams_step n m ih,
      h_evalNamed := evalNamed_step n m ih,
      h_initFields := initFields_step n m ih,
      h_protoFromCtor := protoFromCtor_step n m ih,
      h_constructNative := constructNative_step n m ih,
      h_construct := construct_step n m ih,
      h_evalBody := evalBody_step n m ih,
      h_enterBlock := enterBlock_step n m ih,
      h_declareLexical := declareLexical_step n m ih,
      h_evalStmts := evalStmts_step n m ih,
      h_evalBlock := evalBlock_step n m ih,
      h_assignName := assignName_step n m ih,
      h_lookupLocal := lookupLocal_step n m ih,
      h_assignLocal := assignLocal_step n m ih,
      h_namedGlobal := namedGlobal_step n m ih,
      h_lookup := lookup_step n m ih,
      h_putTarget := putTarget_step n m ih,
      h_evalRef := evalRef_step n m ih,
      h_getRef := getRef_step n m ih,
      h_evalArgs := evalArgs_step n m ih,
      h_evalArg := evalArg_step n m ih,
      h_evalProps := evalProps_step n m ih,
      h_evalExpr := evalExpr_step n m ih,
      h_whileLoop := whileLoop_step n m ih,
      h_doLoop := doLoop_step n m ih,
      h_forLoop := forLoop_step n m ih,
      h_copyEnv := copyEnv_step n m ih,
      h_forInLoop := forInLoop_step n m ih,
      h_bindIter := bindIter_step n m ih,
      h_forOfLoop := forOfLoop_step n m ih,
      h_switchFind := switchFind_step n m ih,
      h_runCases := runCases_step n m ih,
      h_evalDecls := evalDecls_step n m ih,
      h_evalStmt := evalStmt_step n m ih,
      h_bindPat := bindPat_step n m ih,
      h_bindProps := bindProps_step n m ih,
      h_bindElems := bindElems_step n m ih,
      h_copyDataProps := copyDataProps_step n m ih,
      h_getIterator := getIterator_step n m ih,
      h_iterStep := iterStep_step n m ih,
      h_iterClose := iterClose_step n m ih,
      h_iterToArray := iterToArray_step n m ih,
      h_iterCloseAbrupt := iterCloseAbrupt_step n m ih,
      h_getSuper := getSuper_step n m ih,
      h_superCall := superCall_step n m ih,
      h_evalClass := evalClass_step n m ih,
      h_defineMembers := defineMembers_step n m ih,
      h_directEval := directEval_step n m ih,
      h_evalCompletion := evalCompletion_step n m ih,
      h_genRun := genRun_step n m ih,
      h_genEval := genEval_step n m ih,
      h_genEnter := genEnter_step n m ih,
      h_genUnsupported := genUnsupported_step n m ih,
      h_genLift := genLift_step n m ih,
      h_genUnwind := genUnwind_step n m ih,
      h_asyncStep := asyncStep_step n m ih,
      h_promiseResolve := promiseResolve_step n m ih,
      h_resolvePromise := resolvePromise_step n m ih,
      h_rejectPromise := rejectPromise_step n m ih,
      h_settlePromise := settlePromise_step n m ih,
      h_performThen := performThen_step n m ih,
      h_runJobs := runJobs_step n m ih,
      h_iterResult := iterResult_step n m ih,
      h_agenDrain := agenDrain_step n m ih,
      h_agenAwait := agenAwait_step n m ih,
      h_agenRun := agenRun_step n m ih,
      h_coreRun := coreRun_step n m ih,
      h_callNative := callNative_step n m ih,
      h_vmGlobalMiss := vmGlobalMiss_step n m ih,
      h_vmUnary := vmUnary_step n m ih,
      h_vmGetIndex := vmGetIndex_step n m ih,
      h_vmLoop := vmLoop_step n m ih,
      h_vmEnter := vmEnter_step n m ih,
      h_genericPush := genericPush_step n m ih,
      h_deleteOrThrow := deleteOrThrow_step n m ih,
      h_arrayGeneric := arrayGeneric_step n m ih,
      h_speciesFrom := speciesFrom_step n m ih,
      h_speciesFill := speciesFill_step n m ih,
      h_elemsOf := elemsOf_step n m ih,
      h_elemAt := elemAt_step n m ih,
      h_iterArray := iterArray_step n m ih,
      h_reduceArray := reduceArray_step n m ih,
      h_arrayLikeLength := arrayLikeLength_step n m ih,
      h_sortGt := sortGt_step n m ih,
      h_mergeSort := mergeSort_step n m ih,
      h_merge := merge_step n m ih,
      h_toPropDesc := toPropDesc_step n m ih,
      h_defineOwnProp := defineOwnProp_step n m ih,
      h_defineFromDescriptor := defineFromDescriptor_step n m ih,
      h_jsonSer := jsonSer_step n m ih,
      h_jsonStr := jsonStr_step n m ih,
      h_regexExec := regexExec_step n m ih,
      h_regExpExecG := regExpExecG_step n m ih,
      h_speciesCtor := speciesCtor_step n m ih,
      h_matchArray := matchArray_step n m ih,
      h_stringSymDispatch := stringSymDispatch_step n m ih,
      h_regexpSymbol := regexpSymbol_step n m ih,
      h_extraNative := extraNative_step n m ih,
      h_stringOrMath := stringOrMath_step n m ih,
      h_moreNative := moreNative_step n m ih }

/-- Fuel monotonicity of statement lists, in the words of a run: from any heap (the register
machine on or off, any host and `hostCall`), if `evalStmts` at fuel `n` ends with anything but
`halt "fuel"`, it ends with the same result at every fuel `m ≥ n`: the same value or completion
and the same heap, so the same output, jobs, host state and steps left (a host call receives the
steps left, so it sees the same count at every call). -/
theorem evalStmts_fuel_mono {H : Type} {n m : Nat} (h : n ≤ m) (ctx : Ctx) (ss : List Stmt)
    (s : HeapOf H) (hn : ¬ Out (evalStmts n ctx ss s)) :
    evalStmts m ctx ss s = evalStmts n ctx ss s :=
  ((IH_all n m h).h_evalStmts ctx ss).eq_of_not_out s hn

/-- The same for a call of a function value. -/
theorem callV_fuel_mono {H : Type} {n m : Nat} (h : n ≤ m) (f thisV : Value) (args : Array Value)
    (s : HeapOf H) (hn : ¬ Out (callV n f thisV args s)) :
    callV m f thisV args s = callV n f thisV args s :=
  ((IH_all n m h).h_callV f thisV args).eq_of_not_out s hn

/-- The same for an expression. -/
theorem evalExpr_fuel_mono {H : Type} {n m : Nat} (h : n ≤ m) (ctx : Ctx) (e : Expr)
    (s : HeapOf H) (hn : ¬ Out (evalExpr n ctx e s)) :
    evalExpr m ctx e s = evalExpr n ctx e s :=
  ((IH_all n m h).h_evalExpr ctx e).eq_of_not_out s hn

end L4Factoidal.JS.FuelMono
