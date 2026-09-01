import Std

/- bv lemmas -/

theorem and_xor_distrib_left {x y z : BitVec w} : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_xor_distrib_left])

theorem and_xor_distrib_right {x y z : BitVec w} : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_xor_distrib_right])

theorem xor_both_sides (x y z : BitVec n) (h : x = y ^^^ z) : x ^^^ z = y := by
  grind

theorem and_minus_one (x : BitVec n) : x &&& (~~~0) = x := by
  simp


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


def force_membership {n} (kb : KnownBits n) (bv : BitVec n) : BitVec n :=
  kb.ones ||| (bv &&& kb.unknowns)


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





theorem invert_invert_is_identity (kb : KnownBits n) : kb.invert.invert = kb := by
  rw [ext kb.invert.invert kb];
  have h := kb.wf; simp [invert];
  have h₁ : ~~~kb.unknowns &&& ~~~(~~~kb.unknowns &&& ~~~kb.ones) = ~~~kb.unknowns &&& kb.ones := by grind;
  rw [h₁]; rw [← knowns]; exact knowns_and_ones_equal_ones kb;

theorem invert_implies_original_set_contains_invert {n} (kb : KnownBits n) (x : BitVec n) (h : kb.invert.Contains x)
  :  kb.Contains (~~~x) := by
  rw [← invert_invert_is_identity kb];
  grind

theorem invert_precise {kb inv : KnownBits n} (h : inv.IsInversionOf kb) :
  kb.invert.Subset inv := by
  intro bv hv;
  have h₁ : kb.Contains (~~~bv) := invert_implies_original_set_contains_invert kb bv hv;
  have h₂ : _ := h h₁; rw [BitVec.not_not] at h₂; exact h₂


/- and -/

@[grind, simp]
def and (kb₁ kb₂ : KnownBits n) : KnownBits n :=
  let ones   := kb₁.ones &&& kb₂.ones
  let knowns := kb₁.zeros ||| kb₂.zeros ||| ones
  { ones, unknowns := ~~~knowns }


@[grind, simp]
def IsAndOf (and a b : KnownBits n) :=
  ∀ {bv₁ bv₂}, a.Contains bv₁ ∧ b.Contains bv₂ → and.Contains (bv₁ &&& bv₂)

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
  -- By simplifying the expression using the properties bitwise operations, we can show that the result is indeed `bv`.
  have h_simp : (kb₁.ones ||| bv &&& kb₁.unknowns) &&& (kb₂.ones ||| bv &&& kb₂.unknowns) = (kb₁.ones &&& kb₂.ones) ||| (bv &&& (kb₁.unknowns ||| kb₂.unknowns)) := by
    grind;
  grind

theorem apply_is_and_of {n} (and a b : KnownBits n) (h : and.IsAndOf a b) {bv₁ bv₂} (h₁ : a.Contains bv₁) (h₂ : b.Contains bv₂) :
  and.Contains (bv₁ &&& bv₂) := by
  grind;

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

private theorem atLeastTwo_mono {a a' b b' c c' : Bool}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    Bool.atLeastTwo a b c ≤ Bool.atLeastTwo a' b' c' := by
  decide +revert

private theorem bool_le_antisymm (a b : Bool) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  decide +revert

private theorem carry_mono (a a' b b' : BitVec n)
    (ha : ∀ j, j < n → a.getLsbD j ≤ a'.getLsbD j)
    (hb : ∀ j, j < n → b.getLsbD j ≤ b'.getLsbD j) :
    ∀ i, BitVec.carry i a b false ≤ BitVec.carry i a' b' false := by
  intro i
  induction i with
  | zero => simp [BitVec.carry_zero]
  | succ i ih =>
    rw [BitVec.carry_succ, BitVec.carry_succ]
    have hai : a.getLsbD i ≤ a'.getLsbD i := by
      by_cases hi : i < n
      · exact ha i hi
      · rw [BitVec.getLsbD_of_ge a i (by omega), BitVec.getLsbD_of_ge a' i (by omega)]
        exact Bool.le_refl false
    have hbi : b.getLsbD i ≤ b'.getLsbD i := by
      by_cases hi : i < n
      · exact hb i hi
      · rw [BitVec.getLsbD_of_ge b i (by omega), BitVec.getLsbD_of_ge b' i (by omega)]
        exact Bool.le_refl false
    exact atLeastTwo_mono hai hbi ih

private theorem concrete_bit_ge_ones {bv : BitVec n} {kb : KnownBits n}
    (h : kb.Contains bv) (i : Nat) (hi : i < n) :
    kb.ones.getLsbD i ≤ bv.getLsbD i := by
  rw [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem hi]
  have hc := congrArg (fun x : BitVec n => x[i]) h
  simp [knowns] at hc
  cases hbv : bv[i] <;> cases hone : kb.ones[i] <;> simp_all [knowns]

private theorem concrete_bit_le_max {bv : BitVec n} {kb : KnownBits n}
    (h : kb.Contains bv) (i : Nat) (hi : i < n) :
    bv.getLsbD i ≤ (kb.ones + kb.unknowns).getLsbD i := by
  rw [BitVec.getLsbD_add hi, BitVec.carry_of_and_eq_zero kb.wf]
  simp only [BitVec.getLsbD_eq_getElem hi]
  have hc := congrArg (fun x : BitVec n => x[i]) h
  have hwf := congrArg (fun x : BitVec n => x[i]) kb.wf
  simp [knowns] at hc hwf
  cases hbv : bv[i] <;> cases hone : kb.ones[i] <;>
    cases hunk : kb.unknowns[i] <;> simp_all

private theorem extreme_carries_eq_at_known_bit {kb₁ kb₂ : KnownBits n}
    (i : Nat) (hi : i < n)
    (hu₁ : kb₁.unknowns.getLsbD i = false)
    (hu₂ : kb₂.unknowns.getLsbD i = false)
    (hχ : ((kb₁.ones + kb₂.ones + (kb₁.unknowns + kb₂.unknowns)) ^^^
      (kb₁.ones + kb₂.ones)).getLsbD i = false) :
    BitVec.carry i kb₁.ones kb₂.ones false =
      BitVec.carry i (kb₁.ones + kb₁.unknowns) (kb₂.ones + kb₂.unknowns) false := by
  have hsum :
      (kb₁.ones + kb₁.unknowns) + (kb₂.ones + kb₂.unknowns) =
        (kb₁.ones + kb₂.ones) + (kb₁.unknowns + kb₂.unknowns) := by
    ac_rfl
  have hresult :
      ((kb₁.ones + kb₂.ones) + (kb₁.unknowns + kb₂.unknowns)).getLsbD i =
        (kb₁.ones + kb₂.ones).getLsbD i := by
    simp only [BitVec.getLsbD_xor] at hχ
    generalize ha : ((kb₁.ones + kb₂.ones) +
      (kb₁.unknowns + kb₂.unknowns)).getLsbD i = a at hχ ⊢
    generalize hb : (kb₁.ones + kb₂.ones).getLsbD i = b at hχ ⊢
    cases a <;> cases b <;> simp_all
  have hmaxbit₁ : (kb₁.ones + kb₁.unknowns).getLsbD i = kb₁.ones.getLsbD i := by
    rw [BitVec.getLsbD_add hi, BitVec.carry_of_and_eq_zero kb₁.wf]
    simp [hu₁]
  have hmaxbit₂ : (kb₂.ones + kb₂.unknowns).getLsbD i = kb₂.ones.getLsbD i := by
    rw [BitVec.getLsbD_add hi, BitVec.carry_of_and_eq_zero kb₂.wf]
    simp [hu₂]
  rw [← hsum, BitVec.getLsbD_add hi, hmaxbit₁, hmaxbit₂,
    BitVec.getLsbD_add hi] at hresult
  have hcancel₁ := Bool.xor_right_inj.mp hresult
  exact (Bool.xor_right_inj.mp hcancel₁).symm

private theorem carry_eq_when_result_bit_known {bv₁ bv₂ : BitVec n}
    {kb₁ kb₂ : KnownBits n} (h₁ : kb₁.Contains bv₁) (h₂ : kb₂.Contains bv₂)
    (i : Nat) (hi : i < n)
    (hu₁ : kb₁.unknowns.getLsbD i = false)
    (hu₂ : kb₂.unknowns.getLsbD i = false)
    (hχ : ((kb₁.ones + kb₂.ones + (kb₁.unknowns + kb₂.unknowns)) ^^^
      (kb₁.ones + kb₂.ones)).getLsbD i = false) :
    BitVec.carry i bv₁ bv₂ false = BitVec.carry i kb₁.ones kb₂.ones false := by
  have hmin : BitVec.carry i kb₁.ones kb₂.ones false ≤ BitVec.carry i bv₁ bv₂ false :=
    carry_mono kb₁.ones bv₁ kb₂.ones bv₂
      (fun j hj => concrete_bit_ge_ones h₁ j hj)
      (fun j hj => concrete_bit_ge_ones h₂ j hj) i
  have hmax : BitVec.carry i bv₁ bv₂ false ≤
      BitVec.carry i (kb₁.ones + kb₁.unknowns) (kb₂.ones + kb₂.unknowns) false :=
    carry_mono bv₁ (kb₁.ones + kb₁.unknowns) bv₂ (kb₂.ones + kb₂.unknowns)
      (fun j hj => concrete_bit_le_max h₁ j hj)
      (fun j hj => concrete_bit_le_max h₂ j hj) i
  have hextreme := extreme_carries_eq_at_known_bit i hi hu₁ hu₂ hχ
  rw [← hextreme] at hmax
  exact bool_le_antisymm _ _ hmax hmin

theorem add_sound {bv₁ bv₂} {kb₁ kb₂ : KnownBits n} (h₁ : kb₁.Contains bv₁) (h₂ : kb₂.Contains bv₂) :
    (kb₁.add kb₂).Contains (bv₁ + bv₂) := by
  simp only [add, Contains, knowns] at *
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not]
  by_cases hη : (kb₁.unknowns ||| kb₂.unknowns |||
      ((kb₁.ones + kb₂.ones + (kb₁.unknowns + kb₂.unknowns)) ^^^
        (kb₁.ones + kb₂.ones)))[i]
  · simp [hη]
  · have hηfalse : (kb₁.unknowns ||| kb₂.unknowns |||
        ((kb₁.ones + kb₂.ones + (kb₁.unknowns + kb₂.unknowns)) ^^^
          (kb₁.ones + kb₂.ones)))[i] = false := by
      cases hm : (kb₁.unknowns ||| kb₂.unknowns |||
          ((kb₁.ones + kb₂.ones + (kb₁.unknowns + kb₂.unknowns)) ^^^
            (kb₁.ones + kb₂.ones)))[i] <;> simp_all
    simp only [BitVec.getElem_or, Bool.or_eq_false_iff] at hηfalse
    obtain ⟨⟨hu₁, hu₂⟩, hχ⟩ := hηfalse
    have hbv₁ : bv₁[i] = kb₁.ones[i] := by
      have hc := congrArg (fun x : BitVec n => x[i]) h₁
      simpa [hu₁] using hc
    have hbv₂ : bv₂[i] = kb₂.ones[i] := by
      have hc := congrArg (fun x : BitVec n => x[i]) h₂
      simpa [hu₂] using hc
    have hu₁D : kb₁.unknowns.getLsbD i = false := by
      simpa only [BitVec.getLsbD_eq_getElem hi] using hu₁
    have hu₂D : kb₂.unknowns.getLsbD i = false := by
      simpa only [BitVec.getLsbD_eq_getElem hi] using hu₂
    have hχD : ((kb₁.ones + kb₂.ones + (kb₁.unknowns + kb₂.unknowns)) ^^^
        (kb₁.ones + kb₂.ones)).getLsbD i = false := by
      simpa only [BitVec.getLsbD_eq_getElem hi] using hχ
    have hcarry := carry_eq_when_result_bit_known h₁ h₂ i hi hu₁D hu₂D hχD
    simp [hu₁, hu₂, hχ]
    rw [BitVec.getElem_add hi, BitVec.getElem_add hi, hbv₁, hbv₂, hcarry]


theorem add_constfolds {n} (kb₁ kb₂ : KnownBits n) (h₁ : kb₁.IsConst) (h₂ : kb₂.IsConst) :
    (kb₁.add kb₂).IsConst := by
  simp [IsConst] at h₁ h₂;
  simp [add, IsConst];
  rw [h₁, h₂];
  simp;

/-
theorem add_precise {sum a b : KnownBits n} (h : sum.IsAddOf a b) : (a.add b).Subset sum := by
  intro bv hv;
  simp only [Contains]; simp only [IsAddOf] at h;
  sorry /- *much* more difficult -/
-/



/- SMask -/

structure SMask (n : Nat) where
  smask    : BitVec n
  wf       : ∃ x : Nat, smask = (~~~(0 : BitVec n)) <<< x ∧ x < n := by first | bv_decide | grind

namespace SMask

theorem ext {n} (a b : SMask n) (h : a.smask = b.smask) : a = b := by
  cases a; cases b; simp at *; exact h

def top (n : Nat) (hn : n > 0) : SMask n where
  smask := (~~~(0 : BitVec n)) <<< (n - 1);
  wf := by
    apply Exists.intro (n - 1); grind

def isTop (kb : SMask n) : Prop :=
  ∃ hn : n > 0, kb = top n hn

def lower_bound {n} (kb : SMask n) : (BitVec n) :=
  kb.smask

def upper_bound {n} (kb : SMask n) : (BitVec n) :=
  ~~~(kb.smask)

theorem smask_is_negative {n} (kb : SMask n) (h : n > 0) : BitVec.slt kb.smask 0 := by
  obtain ⟨x, ⟨ h1a, h1b⟩ ⟩ := kb.wf; rw [h1a];
  apply BitVec.slt_zero_iff_msb_cond.mpr
  simp [BitVec.msb, BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_shiftLeft]
  omega

@[grind, simp]
def Contains (kb : SMask n) (val : BitVec n) : Prop :=
  val &&& kb.smask = 0 ∨ val &&& kb.smask = kb.smask


theorem lower_bound_is_lower_bound {n} (kb : SMask n) (bv : BitVec n) (h : kb.Contains bv) : BitVec.sle kb.lower_bound bv := by
  simp [Contains, lower_bound] at *;
  sorry;

theorem contains_zero {n} (kb : SMask n) : kb.Contains 0 := by
  simp [Contains]

theorem contains_mask {n} (kb : SMask n) : kb.Contains (kb.smask) := by
  simp [Contains]

theorem TopContainsEverything {n} (hn : n > 0) (val : BitVec n) : (top n hn).Contains val := by
  simp [top, Contains]; grind;

@[grind, simp]
def and (kb₁ kb₂ : SMask n) : SMask n where
  smask := kb₁.smask &&& kb₂.smask
  wf := by
    have h₁ := kb₁.wf; have h₂ := kb₂.wf; grind;

@[grind, simp]
def IsAndOf (and a b : SMask n) :=
  ∀ {bv₁ bv₂}, a.Contains bv₁ ∧ b.Contains bv₂ → and.Contains (bv₁ &&& bv₂)

theorem and_sound {n} (sm₁ sm₂ : SMask n) : (sm₁.and sm₂).IsAndOf sm₁ sm₂ := by
  grind

theorem allOnes_shl_inj {n} {x₁ x₂ : Nat} (hx₁ : x₁ < n) (hx₂ : x₂ < n)
    (h : (~~~(0 : BitVec n) <<< x₁) = (~~~(0 : BitVec n) <<< x₂)) : x₁ = x₂ := by
  have hne (h_ne : x₁ ≠ x₂) : False := by
    have hlt : x₁ < x₂ ∨ x₂ < x₁ := Nat.lt_or_gt_of_ne h_ne
    cases hlt with
    | inl hlt =>
      have h1 : (~~~(0 : BitVec n) <<< x₁).getLsbD x₁ = true := by
        simp [BitVec.getLsbD_shiftLeft]
        omega
      have h2 : (~~~(0 : BitVec n) <<< x₂).getLsbD x₁ = false := by
        simp [BitVec.getLsbD_shiftLeft]
        omega
      rw [h] at h1
      rw [h1] at h2
      contradiction
    | inr hlt =>
      have h1 : (~~~(0 : BitVec n) <<< x₂).getLsbD x₂ = true := by
        simp [BitVec.getLsbD_shiftLeft]
        omega
      have h2 : (~~~(0 : BitVec n) <<< x₁).getLsbD x₂ = false := by
        simp [BitVec.getLsbD_shiftLeft]
        omega
      rw [← h] at h1
      rw [h1] at h2
      contradiction
  apply Classical.byContradiction
  intro h_ne
  exact hne h_ne

theorem all_ones_shift_and_all_ones_shift_is_all_ones_shift {n} (x₁ x₂ : Nat) :
  (~~~(0 : BitVec n)) <<< x₁ &&& (~~~(0 : BitVec n)) <<< x₂ = (~~~(0 : BitVec n)) <<< max x₁ x₂ := by
  grind

@[grind, simp]
def add (kb₁ kb₂ : SMask n) (h1 : ¬ kb₁.isTop) (h2 : ¬ kb₂.isTop) : SMask n where
  smask := (kb₁.smask &&& kb₂.smask) <<< 1
  wf := by
    have ⟨x₁, h1a, h1b⟩ := kb₁.wf
    have ⟨x₂, h2a, h2b⟩ := kb₂.wf
    rw [h1a, h2a, all_ones_shift_and_all_ones_shift_is_all_ones_shift]
    apply Exists.intro (max x₁ x₂ + 1)
    apply And.intro
    . simp [BitVec.shiftLeft_add]
    . have hn : n > 0 := by
        apply Classical.byContradiction
        intro hn'
        simp at hn'
        subst hn'
        omega
      have hx₁_lt : x₁ < n - 1 := by
        apply Classical.byContradiction
        intro h_ge
        have : x₁ = n - 1 := by omega
        have : kb₁ = top n hn := by
          apply SMask.ext
          simp [top, h1a, this]
        exact h1 ⟨hn, this⟩
      have hx₂_lt : x₂ < n - 1 := by
        apply Classical.byContradiction
        intro h_ge
        have : x₂ = n - 1 := by omega
        have : kb₂ = top n hn := by
          apply SMask.ext
          simp [top, h2a, this]
        exact h2 ⟨hn, this⟩
      omega

theorem and_allOnes_shl_eq_zero_iff_toNat_lt {n x : Nat} (hx : x < n) (bv : BitVec n) :
    bv &&& ((~~~0 : BitVec n) <<< x) = 0 ↔ bv.toNat < 2^x := by
  sorry

theorem and_allOnes_shl_eq_self_iff_toNat_ge {n x : Nat} (hx : x < n) (bv : BitVec n) :
    bv &&& ((~~~0 : BitVec n) <<< x) = ((~~~0 : BitVec n) <<< x) ↔ bv.toNat ≥ 2^n - 2^x := by
  sorry

def IsAddOf (sum a b : SMask n) :=
  ∀ {bv₁ bv₂}, a.Contains bv₁ ∧ b.Contains bv₂ → sum.Contains (bv₁ + bv₂)

theorem add_top_sound {n} (sm₁ sm₂ : SMask n) (hn : n > 0) : (top n hn).IsAddOf sm₁ sm₂ := by
  simp only [top, IsAddOf, Contains] at *
  intro bv₁ bv₂ h; grind

theorem add_sound {n} (sm₁ sm₂ : SMask n) (h1 : ¬ sm₁.isTop) (h2 : ¬ sm₂.isTop) : (sm₁.add sm₂ h1 h2).IsAddOf sm₁ sm₂ := by
  sorry
