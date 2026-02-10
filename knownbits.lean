import Std.Tactic.BVDecide

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

/-
instance : Membership (BitVec n) (KnownBits n) where
  mem := Contains
-/

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


theorem and_xor_distrib_left {x y z : BitVec w} : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_xor_distrib_left])

theorem and_xor_distrib_right {x y z : BitVec w} : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) :=
  BitVec.eq_of_getElem_eq (by simp [Bool.and_xor_distrib_right])


theorem knowns_and_ones_equal_ones (kb : KnownBits n) : kb.knowns &&& kb.ones = kb.ones := by
  simp [knowns]; have h := kb.wf;
  have h₂ : 0 = kb.ones ^^^ kb.ones := by simp;
  rw [h₂] at h; have h₃ : kb.ones &&& kb.unknowns ^^^ kb.ones = kb.ones := by grind;
  have h₄ : kb.ones &&& kb.unknowns ^^^ kb.ones &&& (~~~0) = kb.ones := by grind;
  rw [←and_xor_distrib_left] at h₄;
  have h₅ : kb.ones &&& (~~~kb.unknowns) = kb.ones := by grind;
  rw [BitVec.and_comm] at h₅;
  exact h₅

theorem invert_invert_is_identity (kb : KnownBits n) : kb.invert.invert = kb := by
  rw [ext kb.invert.invert kb];
  have h := kb.wf; simp [invert];
  /- here's the plan, where o is kb.ones an u is kb.unknowns:
  o & u == 0 => ~u & ~(~u & ~o) == o
xor with -1, ~x == x ^ -1
o & u == 0 => ~u & (~u & ~o ^ -1) == o
and distributes over xor, x & (y ^ z) == x & y ^ x & z
o & u == 0 => ~u & ~u & ~o ^ ~u & -1 == o
and with -1, x & -1 == x
o & u == 0 => ~u & ~u & ~o ^ ~u == o
associativity of and, x & (y & z) == (x & y) & z
o & u == 0 => ~u & ~u & ~o ^ ~u == o
and with self, x & x == x
o & u == 0 => ~u & ~o ^ ~u == o
De Morgan's law, ~x & ~y == ~(x | y)
o & u == 0 => ~(u | o) ^ ~u == o
double complement in xor, ~x ^ ~y == x ^ y
o & u == 0 => (u | o) ^ u == o
xor with y on both sides, (x ^ y == z) == (x == z ^ y)
o & u == 0 => u | o == o ^ u
xor with y on both sides, (x == y ^ z) == (x ^ y == z)
o & u == 0 => (u | o) ^ o == u
commutativity of or, x | y == y | x
o & u == 0 => (o | u) ^ o == u
commutativity of and, x & y == y & x
u & o == 0 => (o | u) ^ o == u
double complement in xor, x ^ y == ~x ^ ~y
u & o == 0 => ~(o | u) ^ ~o == u
De Morgan's law, ~(x | y) == ~x & ~y
u & o == 0 => ~o & ~u ^ ~o == u
and with self, x == x & x
u & o == 0 => ~o & ~o & ~u ^ ~o == u
associativity of and, (x & y) & z == x & (y & z)
u & o == 0 => ~o & ~o & ~u ^ ~o == u
and with -1, x == x & -1
u & o == 0 => ~o & ~o & ~u ^ ~o & -1 == u
and distributes over xor, x & y ^ x & z == x & (y ^ z)
u & o == 0 => ~o & (~o & ~u ^ -1) == u
xor with -1, x ^ -1 == ~x
u & o == 0 => ~o & ~(~o & ~u) == u
  -/
    sorry

theorem invert_implies_original_set_contains_invert {n} (kb : KnownBits n) (x : BitVec n) (h : kb.invert.Contains x)
  :  kb.Contains (~~~x) := by
  simp_all +decide [Contains, invert];
  rw [← knowns_and_ones_equal_ones _];
   sorry



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

@[grind, simp]
def and (kb₁ kb₂ : KnownBits n) : KnownBits n :=
  let ones   := kb₁.ones &&& kb₂.ones
  let knowns := kb₁.zeros ||| kb₂.zeros ||| ones
  { ones, unknowns := ~~~knowns }

theorem and_sound {bv₁ bv₂} {kb₁ kb₂ : KnownBits n} (h₁ : kb₁.Contains bv₁) (h₂ : kb₂.Contains bv₂) :
    (kb₁.and kb₂).Contains (bv₁ &&& bv₂) := by
  simp only [Contains, and]
  grind

@[grind, simp]
def add (kb₁ kb₂ : KnownBits n) : KnownBits n :=
  let sumOnes     := kb₁.ones + kb₂.ones
  let sumUnknowns := kb₁.unknowns + kb₂.unknowns
  let allCarriers := sumOnes + sumUnknowns
  let onesCarrier := allCarriers ^^^ sumOnes
  let unknowns    := kb₁.unknowns ||| kb₂.unknowns ||| onesCarrier
  let ones        := sumOnes &&& ~~~unknowns
  { ones, unknowns }

theorem add_sound {bv₁ bv₂} {kb₁ kb₂ : KnownBits n} (h₁ : kb₁.Contains bv₁) (h₂ : kb₂.Contains bv₂) :
    (kb₁.add kb₂).Contains (bv₁ + bv₂) := by
  simp only [add, Contains] at *
  sorry
