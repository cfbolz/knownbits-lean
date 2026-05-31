import Std

/- bitvector lemmas -/

theorem and_xor_distrib_left {x y z : BitVec w} : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_xor_distrib_left])

theorem and_xor_distrib_right {x y z : BitVec w} : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_xor_distrib_right])

theorem xor_both_sides (x y z : BitVec n) (h : x = y ^^^ z) : x ^^^ z = y := by
  grind

theorem and_minus_one (x : BitVec n) : x &&& (~~~0) = x := by
  simp


/- KnownBits -/

/- representation is like in the "tristate" paper https://arxiv.org/abs/2105.05398
 table of values:
| unknowns | ones | meaning   |
|----------|------|-----------|
| 0        | 0    |         0 |
| 0        | 1    |         1 |
| 1        | 0    |   unknown |
| 1        | 1    | forbidden |

in addition to the unknowns and ones bitvectors, we also have a well-formedness condition that the ones and unknowns bitvectors
cannot overlap, which means that the forbidden state is not allowed. when defining a function that creates a knownbits,
we need to prove that the well-formedness condition is satisfied.
-/

structure KnownBits (n : Nat) where
  ones     : BitVec n
  unknowns : BitVec n
  wf       : ones &&& unknowns = 0 := by first | bv_decide | grind

namespace KnownBits

/- extensionality: two knownbits are equal if their ones and unknowns are equal -/

theorem ext {n} (a b : KnownBits n) (h : a.ones = b.ones ∧ a.unknowns = b.unknowns) : a = b :=
by
  cases a; cases b; simp at *; exact h;


/- constructor from a constant value. the resulting knownbits has no unknowns and is a singleton set -/

@[grind, simp]
def fromConst (bv : BitVec n) : KnownBits n where
  ones     := bv
  unknowns := 0


/- access the known bits, just flip the unknowns -/

@[grind, simp]
def knowns (kb : KnownBits n) : BitVec n :=
  ~~~kb.unknowns

/- access the zero bits, which are the known bits that are zero -/

@[grind, simp]
def zeros (kb : KnownBits n) : BitVec n :=
  kb.knowns &&& ~~~kb.ones


/- membership of a concrete value in the knownbits set -/

@[grind, simp]
def Contains (kb : KnownBits n) (val : BitVec n) : Prop :=
  val &&& kb.knowns = kb.ones

/- subset relation, mathematically formulated -/

@[grind, simp]
def Subset (kb₁ kb₂ : KnownBits n) : Prop :=
  ∀ bv, kb₁.Contains bv → kb₂.Contains bv


/- a knownbits is a const set if it has no unknowns -/

def IsConst {n} (kb : KnownBits n) : Prop :=
  kb.unknowns = 0


/- a const set contains only one value -/

theorem const_implies_singleton_set {n} {kb : KnownBits n} (h : kb.IsConst) :
  ∀ {bv}, kb.Contains bv → bv = kb.ones := by
  intro bv hcontains;
  simp [Contains] at hcontains;
  simp [IsConst] at h;
  rw [h] at hcontains;
  simp at hcontains;
  exact hcontains


/- membership instance, allows using `∈` to check membership

(except that it doesn't work for lean reasons that I don't understand) -/

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

/- every knownbits contains its ones (which means that all unknown bits are set to zero) -/

theorem contains_ones {n} (kb : KnownBits n) : kb.Contains kb.ones := by
  grind [knowns_and_ones_equal_ones, Contains]


/- given any bitvector, we can force it to be a member of the knownbits set by setting the known bits to the desired value -/

def force_membership {n} (kb : KnownBits n) (bv : BitVec n) : BitVec n :=
  kb.ones ||| (bv &&& kb.unknowns)

theorem force_membership_is_member {n} (kb : KnownBits n) (bv : BitVec n) :
    kb.Contains (force_membership kb bv) := by
  have h := kb.wf;
  rw [force_membership];
  rw [Contains];
  have h₁ := knowns_and_ones_equal_ones kb;
  rw [← h₁];
  grind


/- invert (bitwise not) -/
/- let's start with the simplest transfer function, bitwise not. the definition is simple, all known bits are flipped-/

@[grind, simp]
def invert (kb : KnownBits n) : KnownBits n where
  ones     := kb.zeros
  unknowns := kb.unknowns


/- mathematical definition of inversion. inv is a sound inversion of orig, if for all values bv in orig, then ~~~bv is in inv -/

@[grind, simp]
def IsInversionOf (inv orig : KnownBits n) :=
  ∀ {bv}, orig.Contains bv → inv.Contains (~~~bv)

/- now we can prove that invert as defined above is indeed a sound inversion -/

theorem invert_sound (kb : KnownBits n) : kb.invert.IsInversionOf kb := by
  grind


/- two helper theorems -/


theorem invert_invert_is_identity (kb : KnownBits n) : kb.invert.invert = kb := by
  rw [ext kb.invert.invert kb];
  have h := kb.wf; simp [invert];
  have h₁ : ~~~kb.unknowns &&& ~~~(~~~kb.unknowns &&& ~~~kb.ones) = ~~~kb.unknowns &&& kb.ones := by grind;
  rw [h₁]; rw [← knowns]; exact knowns_and_ones_equal_ones kb;

theorem invert_implies_original_set_contains_invert {n} (kb : KnownBits n) (x : BitVec n) (h : kb.invert.Contains x)
  :  kb.Contains (~~~x) := by
  rw [← invert_invert_is_identity kb];
  grind

/- theorem that invert is the most precise inversion. if we have any other inversion of the original set kb, then invert is a subset of that inversion -/

theorem invert_precise {kb inv : KnownBits n} (h : inv.IsInversionOf kb) :
  kb.invert.Subset inv := by
  intro bv hv;
  have h₁ : kb.Contains (~~~bv) := invert_implies_original_set_contains_invert kb bv hv;
  have h₂ : _ := h h₁; rw [BitVec.not_not] at h₂; exact h₂


/- and -/
/- the next simplest transfer function, for bitwise and. it's more complicated because it's a binary function, but it's still a bitwise function.

the definition is simple, here's a table:

| kb₁ bit | kb₂ bit | result bit |
|---------|---------|------------|
|    0    |    0    |     0      |
|    0    |    1    |     0      |
|    0    |    ?    |     0      |
|    1    |    0    |     0      |
|    1    |    1    |     1      |
|    1    |    ?    |     ?      |
|    ?    |    0    |     0      |
|    ?    |    1    |     ?      |
|    ?    |    ?    |     ?      |
-/

@[grind, simp]
def and (kb₁ kb₂ : KnownBits n) : KnownBits n :=
  let ones   := kb₁.ones &&& kb₂.ones
  let knowns := kb₁.zeros ||| kb₂.zeros ||| ones
  { ones, unknowns := ~~~knowns }

/- mathematical criterion for when a knownbits is the sound bitwise and of two other knownbits -/

@[grind, simp]
def IsAndOf (and a b : KnownBits n) :=
  ∀ {bv₁ bv₂}, a.Contains bv₁ ∧ b.Contains bv₂ → and.Contains (bv₁ &&& bv₂)

/- proof that and is sound -/

theorem and_sound {n} (kb₁ kb₂ : KnownBits n) : (kb₁.and kb₂).IsAndOf kb₁ kb₂ := by
  simp only [IsAndOf, and, Contains];
  grind


/- proof that and constant-folds, ie if the two arguments are constants, the result is also a constant-/

theorem and_constfolds {n} (kb₁ kb₂ : KnownBits n) (h₁ : kb₁.IsConst) (h₂ : kb₂.IsConst) :
    (kb₁.and kb₂).IsConst := by
  simp [IsConst, and] at *;
  rw [h₁, h₂];
  grind;

/- helper lemmas for proving precision of and -/

theorem and_force_membership {n} (kb₁ kb₂ : KnownBits n) (bv : BitVec n) (h : (kb₁.and kb₂).Contains bv) :
    (force_membership kb₁ bv &&& force_membership kb₂ bv) = bv := by
  simp [force_membership];
  simp [and] at h;
  -- By simplifying the expression using the properties of bitwise operations, we can show that the result is indeed `bv`.
  have h_simp : (kb₁.ones ||| bv &&& kb₁.unknowns) &&& (kb₂.ones ||| bv &&& kb₂.unknowns) = (kb₁.ones &&& kb₂.ones) ||| (bv &&& (kb₁.unknowns ||| kb₂.unknowns)) := by
    grind;
  grind

theorem apply_is_and_of {n} (and a b : KnownBits n) (h : and.IsAndOf a b) {bv₁ bv₂} (h₁ : a.Contains bv₁) (h₂ : b.Contains bv₂) :
  and.Contains (bv₁ &&& bv₂) := by
  grind;

/- prove precision of and: if we have any other sound bitwise and of two knownbits, then the and function is a subset of that inversion -/

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

/- add is complicated, in the tristate paper there's a long and tricky proof of soundness of add. I didn't manage to port the proof to lean yet-/

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

theorem add_sound {bv₁ bv₂} {kb₁ kb₂ : KnownBits n} (h₁ : kb₁.Contains bv₁) (h₂ : kb₂.Contains bv₂) :
    (kb₁.add kb₂).Contains (bv₁ + bv₂) := by
  simp only [add, Contains, knowns] at *;
  sorry


theorem add_constfolds {n} (kb₁ kb₂ : KnownBits n) (h₁ : kb₁.IsConst) (h₂ : kb₂.IsConst) :
    (kb₁.add kb₂).IsConst := by
  simp [IsConst] at h₁ h₂;
  simp [add, IsConst];
  rw [h₁, h₂];
  simp;


theorem add_precise {sum a b : KnownBits n} (h : sum.IsAddOf a b) : (a.add b).Subset sum := by
  intro bv hv;
  simp only [Contains]; simp only [IsAddOf] at h;
  sorry


/- SMask -/

/- bonus abstract domain. this one comes from QEMU. it took me a while to wrap my heap around it, it's basically a course range
that uses only a single bitvector to represent a range [-2^n..2^n-1]. that range is encoded as a sequence of 1 bits
followed by a sequence of 0 bits. it's called "smask", "signed mask" because the one bits in the mask denote the bits in the
concrete values that all need to be equal to the sign bit (ie all 0 or all 1) -/

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

def isTop (mask : SMask n) : Prop :=
  ∃ hn : n > 0, mask = top n hn

def lower_bound {n} (mask : SMask n) : (BitVec n) :=
  mask.smask

def upper_bound {n} (mask : SMask n) : (BitVec n) :=
  ~~~(mask.smask)

theorem smask_is_negative {n} (mask : SMask n) (h : n > 0) : BitVec.slt mask.smask 0 := by
  obtain ⟨x, ⟨ h1a, h1b⟩ ⟩ := mask.wf; rw [h1a];
  apply BitVec.slt_zero_iff_msb_cond.mpr
  simp [BitVec.msb, BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_shiftLeft]
  omega


/- contains predicate

checks the definition, a value is contained in the smask if either all bits that are masked out are zero,
or all bits that are masked out are one. this means that the smask represents a range of values where all
values have the same bits in the masked out positions, and the masked out positions can be either all 0 or all 1.
-/

@[grind, simp]
def Contains (mask : SMask n) (val : BitVec n) : Prop :=
  val &&& mask.smask = 0 ∨ val &&& mask.smask = mask.smask


theorem lower_bound_is_lower_bound {n} (mask : SMask n) (bv : BitVec n) (h : mask.Contains bv) : BitVec.sle mask.lower_bound bv := by
  sorry;

theorem contains_zero {n} (mask : SMask n) : mask.Contains 0 := by
  simp [Contains]

theorem contains_mask {n} (mask : SMask n) : mask.Contains (mask.smask) := by
  simp [Contains]

theorem TopContainsEverything {n} (hn : n > 0) (val : BitVec n) : (top n hn).Contains val := by
  simp [top, Contains]; grind;

/- and transfer function.

and works by doing a bitwise and of the two masks, which is basically returning the smaller of the two implied ranges.
-/

@[grind, simp]
def and (mask₁ mask₂ : SMask n) : SMask n where
  smask := mask₁.smask &&& mask₂.smask
  wf := by
    have h₁ := mask₁.wf; have h₂ := mask₂.wf; grind;

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
def add (mask₁ mask₂ : SMask n) (h1 : ¬ mask₁.isTop) (h2 : ¬ mask₂.isTop) : SMask n where
  smask := (mask₁.smask &&& mask₂.smask) <<< 1
  wf := by
    have ⟨x₁, h1a, h1b⟩ := mask₁.wf
    have ⟨x₂, h2a, h2b⟩ := mask₂.wf
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
        have : mask₁ = top n hn := by
          apply SMask.ext
          simp [top, h1a, this]
        exact h1 ⟨hn, this⟩
      have hx₂_lt : x₂ < n - 1 := by
        apply Classical.byContradiction
        intro h_ge
        have : x₂ = n - 1 := by omega
        have : mask₂ = top n hn := by
          apply SMask.ext
          simp [top, h2a, this]
        exact h2 ⟨hn, this⟩
      omega

theorem and_allOnes_shl_eq_zero_iff_toNat_lt {n x : Nat} (hx : x < n) (bv : BitVec n) :
    bv &&& ((~~~0 : BitVec n) <<< x) = 0 ↔ bv.toNat < 2^x := by
  rw [BitVec.toNat_lt_iff_getLsbD_eq_false x hx]
  constructor
  · intro h k
    have h_idx : x + k < n ∨ x + k ≥ n := Nat.lt_or_ge (x + k) n
    by_cases h_lt : x + k < n
    · have h_bit : (bv &&& ((~~~0 : BitVec n) <<< x)).getLsbD (x + k) = (0 : BitVec n).getLsbD (x + k) := by
        rw [h]
      simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft] at h_bit
      simp [h_lt] at h_bit
      exact h_bit
    · apply BitVec.getLsbD_of_ge
      omega
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi_n : i < n
    · simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hi_n]
      by_cases h_le : x ≤ i
      · have := h (i - x)
        have : x + (i - x) = i := by omega
        rw [this] at this
        simp [this]
      · simp [h_le]
    · simp [BitVec.getLsbD_of_ge hi_n]

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
