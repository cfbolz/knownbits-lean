/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: dc27c2e9-054a-4f0a-80b2-91717f8a25de

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem and_force_membership {n} (kb₁ kb₂ : KnownBits n) (bv : BitVec n) (h : (kb₁.and kb₂).Contains bv) :
    (force_membership kb₁ bv &&& force_membership kb₂ bv) = bv

- theorem add_sound {bv₁ bv₂} {kb₁ kb₂ : KnownBits n} (h₁ : kb₁.Contains bv₁) (h₂ : kb₂.Contains bv₂) :
    (kb₁.add kb₂).Contains (bv₁ + bv₂)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Std.Tactic.BVDecide


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

/- bv lemmas, should be upstreamed -/

theorem and_xor_distrib_left {x y z : BitVec w} : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_xor_distrib_left])

theorem and_xor_distrib_right {x y z : BitVec w} : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_xor_distrib_right])

/- KnownBits -/

structure KnownBits (n : Nat) where
  ones     : BitVec n
  unknowns : BitVec n
  wf       : ones &&& unknowns = 0 := by first | bv_decide | grind

namespace KnownBits

theorem ext {n} (a b : KnownBits n) (h : a.ones = b.ones ∧ a.unknowns = b.unknowns) : a = b :=
by
  cases a; cases b; simp at *; exact h;

@[grind, simp]
def fromConst (bv : BitVec n) : KnownBits n where
  ones     := bv
  unknowns := 0

@[grind, simp]
def knowns (kb : KnownBits n) : BitVec n :=
  ~~~kb.unknowns

@[grind, simp]
def zeros (kb : KnownBits n) : BitVec n :=
  kb.knowns &&& ~~~kb.ones

@[grind, simp]
def Contains (kb : KnownBits n) (val : BitVec n) : Prop :=
  val &&& kb.knowns = kb.ones

@[grind, simp]
def Subset (kb₁ kb₂ : KnownBits n) : Prop :=
  ∀ bv, kb₁.Contains bv → kb₂.Contains bv

def IsConst {n} (kb : KnownBits n) : Prop :=
  kb.unknowns = 0

instance : Membership (BitVec n) (KnownBits n) where
  mem := Contains

theorem knowns_and_ones_equal_ones (kb : KnownBits n) : kb.knowns &&& kb.ones = kb.ones := by
  simp [knowns]; have h := kb.wf;
  have h₂ : 0 = kb.ones ^^^ kb.ones := by simp;
  rw [h₂] at h; have h₃ : kb.ones &&& kb.unknowns ^^^ kb.ones = kb.ones := by grind;
  have h₄ : kb.ones &&& kb.unknowns ^^^ kb.ones &&& (~~~0) = kb.ones := by grind;
  rw [←and_xor_distrib_left] at h₄;
  have h₅ : kb.ones &&& (~~~kb.unknowns) = kb.ones := by grind;
  rw [BitVec.and_comm] at h₅;
  exact h₅

theorem contains_ones {n} (kb : KnownBits n) : kb.Contains kb.ones := by
  grind [knowns_and_ones_equal_ones, Contains]

theorem const_implies_singleton_set {n} {kb : KnownBits n} (h : kb.IsConst) :
  ∀ {bv}, kb.Contains bv → bv = kb.ones := by
  intro bv hcontains;
  simp [Contains] at hcontains;
  simp [IsConst] at h;
  rw [h] at hcontains;
  simp at hcontains;
  exact hcontains

/- invert (bitwise not) -/

@[grind, simp]
def invert (kb : KnownBits n) : KnownBits n where
  ones     := kb.zeros
  unknowns := kb.unknowns

@[grind, simp]
def IsInversionOf (inv orig : KnownBits n) :=
  ∀ {bv}, orig.Contains bv → inv.Contains (~~~bv)

theorem invert_sound (kb : KnownBits n) : kb.invert.IsInversionOf kb := by
  grind

theorem xor_both_sides (x y z : BitVec n) (h : x = y ^^^ z) : x ^^^ z = y := by
  grind

theorem and_minus_one (x : BitVec n) : x &&& (~~~0) = x := by
  simp

theorem invert_invert_is_identity (kb : KnownBits n) : kb.invert.invert = kb := by
  rw [ext kb.invert.invert kb];
  have h := kb.wf; simp [invert];
  have h₁ : ~~~kb.unknowns &&& ~~~(~~~kb.unknowns &&& ~~~kb.ones) = ~~~kb.unknowns &&& kb.ones := by grind;
  rw [h₁]; rw [← knowns]; exact knowns_and_ones_equal_ones kb;

theorem invert_implies_original_set_contains_invert {n} (kb : KnownBits n) (x : BitVec n) (h : kb.invert.Contains x)
  :  kb.Contains (~~~x) := by
  have h₁ : kb.invert.invert.Contains (~~~x) := by grind;
  rw [invert_invert_is_identity] at h₁;
  exact h₁

theorem invert_precise_simple {kb inv : KnownBits n} (h : inv.IsInversionOf kb) :
  kb.invert.Subset inv := by
  intro bv hv;
  have h₁ : kb.Contains (~~~bv) := invert_implies_original_set_contains_invert kb bv hv;
  have h₂ : _ := h h₁; rw [BitVec.not_not] at h₂; exact h₂

theorem invert_precise {kb inv : KnownBits n} (h : inv.IsInversionOf kb) :
     kb.invert.Subset inv := by
     intro bv hv;
     unfold KnownBits.IsInversionOf at h;
     false_or_by_contra
     have hcontra : ¬ (∃ bv, kb.Contains bv ∧ ¬inv.Contains (~~~bv)) := by grind
     apply hcontra
     rename_i h
     exists ~~~bv;
     simp_all +decide [ KnownBits.Contains, KnownBits.invert ];
     ext i; replace hv := congrArg ( fun x => x.getLsbD i ) hv; simp_all +decide;
     cases h : kb.unknowns[i] <;> cases h' : kb.ones[i] <;> cases h'' : bv[i] <;> simp_all +decide [ Bool.and_comm ]
     · have := kb.wf; replace := congrArg ( fun x => x.getLsbD i ) this; simp_all +decide
     · have := kb.wf; replace := congrArg ( fun x => x.getLsbD i ) this; simp_all +decide

/- and -/

@[grind, simp]
def and (kb₁ kb₂ : KnownBits n) : KnownBits n :=
  let ones   := kb₁.ones &&& kb₂.ones
  let knowns := kb₁.zeros ||| kb₂.zeros ||| ones
  { ones, unknowns := ~~~knowns }

def force_membership {n} (kb : KnownBits n) (bv : BitVec n) : BitVec n :=
  kb.ones ||| (bv &&& kb.unknowns)

@[grind, simp]
def IsAndOf (and a b : KnownBits n) :=
  ∀ {bv₁ bv₂}, a.Contains bv₁ ∧ b.Contains bv₂ → and.Contains (bv₁ &&& bv₂)

theorem apply_is_and_of {n} (and a b : KnownBits n) (h : and.IsAndOf a b) {bv₁ bv₂} (h₁ : a.Contains bv₁) (h₂ : b.Contains bv₂) :
  and.Contains (bv₁ &&& bv₂) := by
  grind;

theorem and_sound {n} (kb₁ kb₂ : KnownBits n) : (kb₁.and kb₂).IsAndOf kb₁ kb₂ := by
  simp only [IsAndOf, and, Contains];
  grind

theorem and_constfolds {n} (kb₁ kb₂ : KnownBits n) (h₁ : kb₁.IsConst) (h₂ : kb₂.IsConst) :
    (kb₁.and kb₂).IsConst := by
  simp [IsConst, and] at *;
  rw [h₁, h₂];
  grind;

theorem force_membership_is_member {n} (kb : KnownBits n) (bv : BitVec n) :
    kb.Contains (force_membership kb bv) := by
  have h := kb.wf;
  rw [force_membership];
  rw [Contains];
  have h₁ := knowns_and_ones_equal_ones kb;
  rw [← h₁];
  grind

theorem and_force_membership {n} (kb₁ kb₂ : KnownBits n) (bv : BitVec n) (h : (kb₁.and kb₂).Contains bv) :
    (force_membership kb₁ bv &&& force_membership kb₂ bv) = bv := by
  simp [force_membership];
  simp [and] at h;
  -- By simplifying the expression using the properties of bitwise operations, we can show that the result is indeed `bv`.
  have h_simp : (kb₁.ones ||| bv &&& kb₁.unknowns) &&& (kb₂.ones ||| bv &&& kb₂.unknowns) = (kb₁.ones &&& kb₂.ones) ||| (bv &&& (kb₁.unknowns ||| kb₂.unknowns)) := by
    grind;
  grind

theorem and_precise {and a b : KnownBits n} (h : and.IsAndOf a b) : (a.and b).Subset and := by
  intro bv hv;
  simp only [IsAndOf] at h;
  have h₁ := force_membership_is_member a bv;
  have h₂ := force_membership_is_member b bv;
  have h₃ : (force_membership a bv &&& force_membership b bv) = bv := and_force_membership a b bv hv;
  have h₄ := apply_is_and_of and a b h h₁ h₂;
  rw [h₃] at h₄;
  exact h₄

/- add -/

@[grind, simp]
def add (kb₁ kb₂ : KnownBits n) : KnownBits n :=
  let sumOnes     := kb₁.ones + kb₂.ones
  let sumUnknowns := kb₁.unknowns + kb₂.unknowns
  let allCarriers := sumOnes + sumUnknowns
  let onesCarrier := allCarriers ^^^ sumOnes
  let unknowns    := kb₁.unknowns ||| kb₂.unknowns ||| onesCarrier
  let ones        := sumOnes &&& ~~~unknowns
  { ones, unknowns }

def IsAddOf (sum a b : KnownBits n) :=
  ∀ {bv₁ bv₂}, a.Contains bv₁ ∧ b.Contains bv₂ → sum.Contains (bv₁ + bv₂)

noncomputable section AristotleLemmas

/-
Monotonicity of the majority function (used in carry calculation).
-/
theorem Bool.majority_mono (a b c a' b' c' : Bool)
  (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
  ((a' && b') || (a' && c') || (b' && c')) ≤ ((a && b) || (a && c) || (b && c)) := by
    cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> simp +decide at ha hb hc ⊢

/-
If `x` is a submask of `y` (i.e., `x` has bits set only where `y` has bits set), then for any bit index `i`, `x[i] <= y[i]`.
-/
theorem getLsbD_le_of_submask {n} {x y : BitVec n} (h : x &&& ~~~y = 0) (i : Nat) :
  x.getLsbD i ≤ y.getLsbD i := by
    by_cases hi : i < n;
    · replace h := congr_arg ( fun z => z.getLsbD i ) h ; aesop;
    · aesop

/-
Auxiliary lemma: The carry at any index `i` is monotonic with respect to the input bitvectors (submask relation).
-/
theorem carry_le_aux {w} (x y x' y' : BitVec w) (c : Bool)
    (hx : x' &&& ~~~x = 0) (hy : y' &&& ~~~y = 0) (i : Nat) :
    BitVec.carry i x' y' c ≤ BitVec.carry i x y c := by
      -- By definition of carry, we know that if `x'` and `y'` are submasks of `x` and `y` respectively, then `BitVec.carry i x' y' c ≤ BitVec.carry i x y c` for all `i`.
      have h_carry_mono : ∀ i, (x'.getLsbD i).atLeastTwo (y'.getLsbD i) (BitVec.carry i x' y' c) ≤ (x.getLsbD i).atLeastTwo (y.getLsbD i) (BitVec.carry i x y c) := by
        intro i;
        have h_mono : ∀ i, x'.getLsbD i ≤ x.getLsbD i ∧ y'.getLsbD i ≤ y.getLsbD i := by
          exact fun i => ⟨ getLsbD_le_of_submask hx i, getLsbD_le_of_submask hy i ⟩;
        -- Apply the monotonicity of the majority function.
        have h_maj_mono : ∀ a b c a' b' c' : Bool, a' ≤ a → b' ≤ b → c' ≤ c → ((a' && b') || (a' && c') || (b' && c')) ≤ ((a && b) || (a && c) || (b && c)) := by
          exact?;
        exact h_maj_mono _ _ _ _ _ _ ( h_mono i |>.1 ) ( h_mono i |>.2 ) ( show BitVec.carry i x' y' c ≤ BitVec.carry i x y c from Nat.recOn i ( by aesop ) fun i hi => by simpa [ BitVec.carry_succ ] using h_maj_mono _ _ _ _ _ _ ( h_mono i |>.1 ) ( h_mono i |>.2 ) hi );
      induction i <;> simp_all +decide [ BitVec.carry_succ ]

/-
The carry generated by bitvector addition is monotonic: if `x'` is a submask of `x` and `y'` is a submask of `y`, then the carry generated by `x' + y'` is less than or equal to the carry generated by `x + y`.
-/
theorem carry_le {n} (x y x' y' : BitVec n) (c : Bool)
    (hx : x' &&& ~~~x = 0) (hy : y' &&& ~~~y = 0) :
    BitVec.carry n x' y' c ≤ BitVec.carry n x y c := by
      exact carry_le_aux x y x' y' c hx hy n

/-
If the sum bit at `i` is stable when adding `K` (which has 0 at `i`), then the carry into `i` must be the same.
-/
theorem carry_eq_of_stable {n} (O₁ O₂ K₁ K₂ : BitVec n) (i : Nat) (hi : i < n)
  (h_bit₁ : K₁.getLsbD i = false)
  (h_bit₂ : K₂.getLsbD i = false)
  (h_stable : ((O₁ ||| K₁) + (O₂ ||| K₂)).getLsbD i = (O₁ + O₂).getLsbD i) :
  BitVec.carry i (O₁ ||| K₁) (O₂ ||| K₂) false = BitVec.carry i O₁ O₂ false := by
    rw [ BitVec.getLsbD_add, BitVec.getLsbD_add ] at h_stable;
    · grind;
    · assumption;
    · assumption

/-
Helper lemma for `add_sound`. Uses `carry_le` and `carry_eq_of_stable` to show that if adding the full unknown mask doesn't disturb a bit (via carry), then adding a partial error mask won't either.
-/
theorem KnownBits.add_sound_bit_lemma {n} (O₁ O₂ K₁ K₂ e₁ e₂ : BitVec n) (i : Nat) (hi : i < n)
  (h_disj₁ : O₁ &&& K₁ = 0)
  (h_disj₂ : O₂ &&& K₂ = 0)
  (h_sub₁ : e₁ &&& ~~~K₁ = 0)
  (h_sub₂ : e₂ &&& ~~~K₂ = 0)
  (h_bit₁ : K₁.getLsbD i = false)
  (h_bit₂ : K₂.getLsbD i = false)
  (h_stable : ((O₁ + O₂) + (K₁ + K₂)).getLsbD i = (O₁ + O₂).getLsbD i) :
  ((O₁ + O₂) + (e₁ + e₂)).getLsbD i = (O₁ + O₂).getLsbD i := by
    -- Since `e₁` and `e₂` are submask of `K₁` and `K₂`, we have `(O₁ + O₂) + (e₁ + e₂) = (O₁ ||| e₁) + (O₂ ||| e₂)`.
    have h_sum_eq : (O₁ + O₂) + (e₁ + e₂) = (O₁ ||| e₁) + (O₂ ||| e₂) := by
      have h_disj_e₁ : O₁ &&& e₁ = 0 := by
        grind
      have h_disj_e₂ : O₂ &&& e₂ = 0 := by
        grind
      have h_sum_eq : ∀ (a b : BitVec n), a &&& b = 0 → a + b = a ||| b := by
        exact?;
      grind;
    have h_carry_eq : BitVec.carry i (O₁ ||| e₁) (O₂ ||| e₂) false = BitVec.carry i O₁ O₂ false := by
      have h_carry_eq : BitVec.carry i (O₁ ||| K₁) (O₂ ||| K₂) false = BitVec.carry i O₁ O₂ false := by
        apply carry_eq_of_stable;
        · assumption;
        · assumption;
        · assumption;
        · have h_sum_eq : ∀ (x y : BitVec n), x &&& y = 0 → x + y = x ||| y := by
            exact?
          generalize_proofs at *; (
          grind);
      have h_carry_le : BitVec.carry i (O₁ ||| e₁) (O₂ ||| e₂) false ≤ BitVec.carry i (O₁ ||| K₁) (O₂ ||| K₂) false := by
        apply carry_le_aux;
        · grind;
        · grind;
      have h_carry_ge : BitVec.carry i O₁ O₂ false ≤ BitVec.carry i (O₁ ||| e₁) (O₂ ||| e₂) false := by
        apply carry_le_aux;
        · aesop;
        · grind;
      exact le_antisymm ( h_carry_le.trans h_carry_eq.le ) h_carry_ge;
    -- Since `e₁` and `e₂` are submask of `K₁` and `K₂`, we have `(O₁ ||| e₁)[i] = O₁[i]` and `(O₂ ||| e₂)[i] = O₂[i]`.
    have h_bit_eq : (O₁ ||| e₁).getLsbD i = O₁.getLsbD i ∧ (O₂ ||| e₂).getLsbD i = O₂.getLsbD i := by
      have h_submask : e₁.getLsbD i ≤ K₁.getLsbD i ∧ e₂.getLsbD i ≤ K₂.getLsbD i := by
        have h_submask : ∀ (x y : BitVec n), x &&& ~~~y = 0 → ∀ i, x.getLsbD i ≤ y.getLsbD i := by
          exact?;
        exact ⟨ h_submask _ _ h_sub₁ _, h_submask _ _ h_sub₂ _ ⟩;
      cases h : e₁.getLsbD i <;> cases h' : e₂.getLsbD i <;> simp_all +decide [ BitVec.getLsbD_or ];
    rw [ h_sum_eq, BitVec.getLsbD_add ];
    · rw [ h_bit_eq.1, h_bit_eq.2, h_carry_eq, BitVec.getLsbD_add ];
      assumption;
    · assumption

end AristotleLemmas

theorem add_sound {bv₁ bv₂} {kb₁ kb₂ : KnownBits n} (h₁ : kb₁.Contains bv₁) (h₂ : kb₂.Contains bv₂) :
    (kb₁.add kb₂).Contains (bv₁ + bv₂) := by
  simp only [add, Contains, knowns] at *;
  -- From the hypotheses h₁ and h₂, we know that bv₁ and bv₂ are equal to the best possible approximation of themselves given the unknown bits. Therefore, bv₁ + bv₂ is also equal to the best possible approximation of itself given the unknown bits.
  have h_best_approx : bv₁ = kb₁.ones ||| (bv₁ &&& kb₁.unknowns) ∧ bv₂ = kb₂.ones ||| (bv₂ &&& kb₂.unknowns) := by
    grind;
  have h_add_approx : ((kb₁.ones ||| (bv₁ &&& kb₁.unknowns)) + (kb₂.ones ||| (bv₂ &&& kb₂.unknowns))) &&& ~~~(kb₁.unknowns ||| kb₂.unknowns ||| (kb₁.ones + kb₂.ones) + (kb₁.unknowns + kb₂.unknowns) ^^^ (kb₁.ones + kb₂.ones)) = (kb₁.ones + kb₂.ones) &&& ~~~(kb₁.unknowns ||| kb₂.unknowns ||| (kb₁.ones + kb₂.ones) + (kb₁.unknowns + kb₂.unknowns) ^^^ (kb₁.ones + kb₂.ones)) := by
    have h_add_approx : ((kb₁.ones + kb₂.ones) + ((bv₁ &&& kb₁.unknowns) + (bv₂ &&& kb₂.unknowns))) &&& ~~~(kb₁.unknowns ||| kb₂.unknowns ||| (kb₁.ones + kb₂.ones) + (kb₁.unknowns + kb₂.unknowns) ^^^ (kb₁.ones + kb₂.ones)) = (kb₁.ones + kb₂.ones) &&& ~~~(kb₁.unknowns ||| kb₂.unknowns ||| (kb₁.ones + kb₂.ones) + (kb₁.unknowns + kb₂.unknowns) ^^^ (kb₁.ones + kb₂.ones)) := by
      apply BitVec.eq_of_getLsbD_eq;
      intro i hi;
      by_cases hi' : ( kb₁.unknowns ||| kb₂.unknowns ||| kb₁.ones + kb₂.ones + ( kb₁.unknowns + kb₂.unknowns ) ^^^ kb₁.ones + kb₂.ones ).getLsbD i = Bool.true;
      · simp +decide [ hi', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_add ];
      · have h_add_approx : ((kb₁.ones + kb₂.ones) + ((bv₁ &&& kb₁.unknowns) + (bv₂ &&& kb₂.unknowns))).getLsbD i = ((kb₁.ones + kb₂.ones).getLsbD i) := by
          apply KnownBits.add_sound_bit_lemma;
          exact hi;
          exact kb₁.wf;
          exact kb₂.wf;
          · simp +decide [ BitVec.and_assoc ];
          · simp +decide [ BitVec.and_assoc ];
          · grind;
          · grind;
          · simp +decide [ BitVec.getLsbD ] at hi' ⊢;
            exact hi'.2;
        grind;
    rw [ show kb₁.ones ||| bv₁ &&& kb₁.unknowns = kb₁.ones + ( bv₁ &&& kb₁.unknowns ) from ?_, show kb₂.ones ||| bv₂ &&& kb₂.unknowns = kb₂.ones + ( bv₂ &&& kb₂.unknowns ) from ?_ ];
    · grind;
    · have h_add_approx : ∀ (x y : BitVec n), x &&& y = 0 → x ||| y = x + y := by
        exact?;
      grind;
    · have h_add_approx : ∀ (x y : BitVec n), x &&& y = 0 → x ||| y = x + y := by
        exact?;
      grind;
  grind

theorem add_constfolds {n} (kb₁ kb₂ : KnownBits n) (h₁ : kb₁.IsConst) (h₂ : kb₂.IsConst) :
    (kb₁.add kb₂).IsConst := by
  simp [IsConst] at h₁ h₂;
  simp [add, IsConst];
  rw [h₁, h₂];
  simp;
