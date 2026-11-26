module

public import HostTerm
public import CountAxioms
public import NFInterpretations

@[expose] public section

set_option autoImplicit false

/-!
# The clauses for the Axiom of Counting, and the term model over the standard numbers

`HostTerm.lean` has the axioms N: a finite list of clause schemes about a truth assignment `τ`
to the atoms `t ∈ t'`, `t = t'` between closed terms of eighteen symbols (`NSat τ q`: every
instance whose atoms have codes below `q` holds). They are a Skolem form of the finite
axiomatisation of NF.

This file adds four symbols and nine clause schemes (`CSat τ q`):

* `usT x`: the set of the singletons of the members of `x`;
* `ddT`: a set that contains zero and is closed under successor;
* `scT k`: the successor of `k`, with a witness `w1T y k` for the members of `scT k`;
* the clause `k`: `x ∈ n` and `n ∈ ddT` imply `usT x ∈ n`.

Results, for truth assignments on the codes that are standard numbers:

* `TermN.model`: if `τ` satisfies every instance of N, the closed terms modulo the equality of
  `τ`, with the membership of `τ`, are a model of the finite axiomatisation of NF;
* `TermN.counting`: if `τ` also satisfies every instance of the nine clauses, the model
  satisfies the Axiom of Counting, in the form `JensenNFU.Counting` of `CountAxioms.lean`;
* `exists_limit`: compactness, with an ultrafilter on the bounds;
* **`consistent_nfc_of_clauses`**: if for every standard `q` some truth assignment satisfies
  the instances of N and of the nine clauses below `q`, then `𝗡𝗙𝗖` is consistent.

Nothing here refers to NFU or to a host. The hypothesis of `consistent_nfc_of_clauses` is what
the semantic part of the proof of `Con(𝗡𝗙𝗨𝗜𝗖) → Con(𝗡𝗙𝗖)` has to supply.
-/

section terms

variable {N : Type} [CommSemiring N]

/-- The set of the singletons of the members of `x`. -/
def usT (x : N) : N := tm 18 x 0
/-- The set of the natural numbers. -/
def ddT : N := tm 19 0 0
/-- The successor of `k`. -/
def scT (k : N) : N := tm 20 k 0
/-- A member `b` of `y` such that `y` without `b` is a member of `k`, if `y ∈ scT k`. -/
def w1T (y k : N) : N := tm 21 y k
/-- The empty set. -/
def emT : N := inT c1T (coT c1T)
/-- Zero: the set whose only member is the empty set. -/
def zrT : N := sgT emT
/-- The union. -/
def unT (x y : N) : N := coT (inT (coT x) (coT y))
/-- `x` with the further member `b`. -/
def adT (x b : N) : N := unT x (sgT b)
/-- `y` without the member `b`. -/
def rmT (y b : N) : N := inT y (coT (sgT b))

end terms

/-- The truth assignment `τ` satisfies every instance of the clauses for the Axiom of Counting
whose atoms have codes below `q`. -/
structure CSat {N : Type} [CommSemiring N] [PartialOrder N] (τ : N → Prop) (q : N) : Prop where
  u1a : ∀ s x : N, aIn s (usT x) + 1 ≤ q → aEq s (sgT (elT s)) + 1 ≤ q →
    τ (aIn s (usT x)) → τ (aEq s (sgT (elT s)))
  u1b : ∀ s x : N, aIn s (usT x) + 1 ≤ q → aIn (elT s) x + 1 ≤ q →
    τ (aIn s (usT x)) → τ (aIn (elT s) x)
  u2 : ∀ a x : N, aIn a x + 1 ≤ q → aIn (sgT a) (usT x) + 1 ≤ q →
    τ (aIn a x) → τ (aIn (sgT a) (usT x))
  s1a : ∀ y k : N, aIn y (scT k) + 1 ≤ q → aIn (rmT y (w1T y k)) k + 1 ≤ q →
    τ (aIn y (scT k)) → τ (aIn (rmT y (w1T y k)) k)
  s1b : ∀ y k : N, aIn y (scT k) + 1 ≤ q → aIn (w1T y k) y + 1 ≤ q →
    τ (aIn y (scT k)) → τ (aIn (w1T y k) y)
  s2 : ∀ x b k : N, aIn x k + 1 ≤ q → aIn b x + 1 ≤ q → aIn (adT x b) (scT k) + 1 ≤ q →
    τ (aIn x k) → ¬ τ (aIn b x) → τ (aIn (adT x b) (scT k))
  n1 : aIn (zrT : N) ddT + 1 ≤ q → τ (aIn zrT ddT)
  n2 : ∀ k : N, aIn k ddT + 1 ≤ q → aIn (scT k) ddT + 1 ≤ q →
    τ (aIn k ddT) → τ (aIn (scT k) ddT)
  k : ∀ x n : N, aIn x n + 1 ≤ q → aIn n ddT + 1 ≤ q → aIn (usT x) n + 1 ≤ q →
    τ (aIn x n) → τ (aIn n ddT) → τ (aIn (usT x) n)

namespace CSat

variable {N : Type} [CommSemiring N] [PartialOrder N] {τ τ' : N → Prop} {q q' : N}

/-- Two truth assignments that agree below `q` satisfy the same instances below `q`. -/
theorem congr (hag : ∀ i : N, i + 1 ≤ q → (τ i ↔ τ' i)) (h : CSat τ q) : CSat τ' q where
  u1a := fun s x h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.u1a s x h1 h2
  u1b := fun s x h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.u1b s x h1 h2
  u2 := fun a x h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.u2 a x h1 h2
  s1a := fun y k h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.s1a y k h1 h2
  s1b := fun y k h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.s1b y k h1 h2
  s2 := fun x b k h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.s2 x b k h1 h2 h3
  n1 := fun h1 => by
    rw [← hag _ h1]
    exact h.n1 h1
  n2 := fun k h1 h2 => by
    rw [← hag _ h1, ← hag _ h2]
    exact h.n2 k h1 h2
  k := fun x n h1 h2 h3 => by
    rw [← hag _ h1, ← hag _ h2, ← hag _ h3]
    exact h.k x n h1 h2 h3

/-- Satisfaction below `q` implies satisfaction below every smaller bound. -/
theorem mono (hqq : q' ≤ q) (h : CSat τ q) : CSat τ q' where
  u1a := fun s x h1 h2 => h.u1a s x (le_trans h1 hqq) (le_trans h2 hqq)
  u1b := fun s x h1 h2 => h.u1b s x (le_trans h1 hqq) (le_trans h2 hqq)
  u2 := fun a x h1 h2 => h.u2 a x (le_trans h1 hqq) (le_trans h2 hqq)
  s1a := fun y k h1 h2 => h.s1a y k (le_trans h1 hqq) (le_trans h2 hqq)
  s1b := fun y k h1 h2 => h.s1b y k (le_trans h1 hqq) (le_trans h2 hqq)
  s2 := fun x b k h1 h2 h3 => h.s2 x b k (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)
  n1 := fun h1 => h.n1 (le_trans h1 hqq)
  n2 := fun k h1 h2 => h.n2 k (le_trans h1 hqq) (le_trans h2 hqq)
  k := fun x n h1 h2 h3 => h.k x n (le_trans h1 hqq) (le_trans h2 hqq) (le_trans h3 hqq)

end CSat

/-! ## The term model over the standard numbers -/

namespace TermN

variable {τ : ℕ → Prop}

section nf

variable (hN : ∀ q : ℕ, NSat τ q)
include hN

/-! ### The instances of N, without bounds (generated by `gen/gen_clauses.py`) -/

theorem n_e1 (x : ℕ) :
    τ (aEq (x) (x)) :=
  (hN (aEq (x) (x) + 1)).e1 x (by omega)

theorem n_e2 (x y z : ℕ) :
    τ (aEq (x) (y)) → τ (aEq (x) (z)) → τ (aEq (y) (z)) :=
  (hN (aEq (x) (y) + aEq (x) (z) + aEq (y) (z) + 1)).e2 x y z (by omega) (by omega) (by omega)

theorem n_e3 (x x' y y' : ℕ) :
    τ (aEq (x) (x')) → τ (aEq (y) (y')) → τ (aIn (x) (y)) → τ (aIn (x') (y')) :=
  (hN (aEq (x) (x') + aEq (y) (y') + aIn (x) (y) + aIn (x') (y') + 1)).e3 x x' y y' (by omega) (by omega) (by omega) (by omega)

theorem n_e4a (x x' : ℕ) :
    τ (aEq (x) (x')) → τ (aEq (sgT x) (sgT x')) :=
  (hN (aEq (x) (x') + aEq (sgT x) (sgT x') + 1)).e4a x x' (by omega) (by omega)

theorem n_e4b (x x' y y' : ℕ) :
    τ (aEq (x) (x')) → τ (aEq (y) (y')) → τ (aEq (upT x y) (upT x' y')) :=
  (hN (aEq (x) (x') + aEq (y) (y') + aEq (upT x y) (upT x' y') + 1)).e4b x x' y y' (by omega) (by omega) (by omega)

theorem n_m1 (x y : ℕ) :
    (τ (aIn (dT x y) (x)) ↔ τ (aIn (dT x y) (y))) → τ (aEq (x) (y)) :=
  (hN (aIn (dT x y) (x) + aIn (dT x y) (y) + aEq (x) (y) + 1)).m1 x y (by omega) (by omega) (by omega)

theorem n_m2 (x y : ℕ) :
    (τ (aIn (y) (sgT x)) ↔ τ (aEq (y) (x))) :=
  (hN (aIn (y) (sgT x) + aEq (y) (x) + 1)).m2 x y (by omega) (by omega)

theorem n_m3 (x y z : ℕ) :
    (τ (aIn (z) (upT x y)) ↔ τ (aEq (z) (x)) ∨ τ (aEq (z) (y))) :=
  (hN (aIn (z) (upT x y) + aEq (z) (x) + aEq (z) (y) + 1)).m3 x y z (by omega) (by omega) (by omega)

theorem n_m4 (x y z : ℕ) :
    (τ (aIn (z) (inT x y)) ↔ τ (aIn (z) (x)) ∧ τ (aIn (z) (y))) :=
  (hN (aIn (z) (inT x y) + aIn (z) (x) + aIn (z) (y) + 1)).m4 x y z (by omega) (by omega) (by omega)

theorem n_m5 (x z : ℕ) :
    (τ (aIn (z) (coT x)) ↔ ¬ τ (aIn (z) (x))) :=
  (hN (aIn (z) (coT x) + aIn (z) (x) + 1)).m5 x z (by omega) (by omega)

theorem n_m6 (x z w : ℕ) :
    (τ (aIn (opT (sgT z) (sgT w)) (siT x)) ↔ τ (aIn (opT z w) (x))) :=
  (hN (aIn (opT (sgT z) (sgT w)) (siT x) + aIn (opT z w) (x) + 1)).m6 x z w (by omega) (by omega)

theorem n_m7 (x p s r : ℕ) :
    (τ (aIn (opT (sgT (sgT p)) (opT s r)) (i2T x)) ↔ τ (aIn (opT p r) (x))) :=
  (hN (aIn (opT (sgT (sgT p)) (opT s r)) (i2T x) + aIn (opT p r) (x) + 1)).m7 x p s r (by omega) (by omega)

theorem n_m8 (x p s r : ℕ) :
    (τ (aIn (opT (sgT (sgT p)) (opT s r)) (i3T x)) ↔ τ (aIn (opT p s) (x))) :=
  (hN (aIn (opT (sgT (sgT p)) (opT s r)) (i3T x) + aIn (opT p s) (x) + 1)).m8 x p s r (by omega) (by omega)

theorem n_m9a (x p : ℕ) :
    τ (aIn (p) (vcT x)) → τ (aEq (p) (opT (p1T p) (p2T p))) ∧ τ (aIn (p2T p) (x)) :=
  (hN (aIn (p) (vcT x) + aEq (p) (opT (p1T p) (p2T p)) + aIn (p2T p) (x) + 1)).m9a x p (by omega) (by omega) (by omega)

theorem n_m9b (x p s r : ℕ) :
    τ (aEq (p) (opT s r)) → τ (aIn (r) (x)) → τ (aIn (p) (vcT x)) :=
  (hN (aEq (p) (opT s r) + aIn (r) (x) + aIn (p) (vcT x) + 1)).m9b x p s r (by omega) (by omega) (by omega)

theorem n_m10a (x p s : ℕ) :
    τ (aIn (p) (tlT x)) → τ (aIn (opT s (sgT p)) (x)) :=
  (hN (aIn (p) (tlT x) + aIn (opT s (sgT p)) (x) + 1)).m10a x p s (by omega) (by omega)

theorem n_m10b (x p : ℕ) :
    τ (aIn (opT (wtT p x) (sgT p)) (x)) → τ (aIn (p) (tlT x)) :=
  (hN (aIn (opT (wtT p x) (sgT p)) (x) + aIn (p) (tlT x) + 1)).m10b x p (by omega) (by omega)

theorem n_m11 (x p s : ℕ) :
    (τ (aIn (opT p s) (cvT x)) ↔ τ (aIn (opT s p) (x))) :=
  (hN (aIn (opT p s) (cvT x) + aIn (opT s p) (x) + 1)).m11 x p s (by omega) (by omega)

theorem n_m12a (p : ℕ) :
    τ (aIn (p) (c1T)) → τ (aEq (p) (sgT (elT p))) :=
  (hN (aIn (p) (c1T) + aEq (p) (sgT (elT p)) + 1)).m12a p (by omega) (by omega)

theorem n_m12b (p s : ℕ) :
    τ (aEq (p) (sgT s)) → τ (aIn (p) (c1T)) :=
  (hN (aEq (p) (sgT s) + aIn (p) (c1T) + 1)).m12b p s (by omega) (by omega)

theorem n_m13a (p s r : ℕ) :
    τ (aIn (opT p s) (sbT)) → τ (aIn (r) (p)) → τ (aIn (r) (s)) :=
  (hN (aIn (opT p s) (sbT) + aIn (r) (p) + aIn (r) (s) + 1)).m13a p s r (by omega) (by omega) (by omega)

theorem n_m13b (p s : ℕ) :
    (τ (aIn (wsT p s) (p)) → τ (aIn (wsT p s) (s))) → τ (aIn (opT p s) (sbT)) :=
  (hN (aIn (wsT p s) (p) + aIn (wsT p s) (s) + aIn (opT p s) (sbT) + 1)).m13b p s (by omega) (by omega) (by omega)

/-! ### The model -/

theorem eta_symm {x y : ℕ} (h : τ (aEq x y)) : τ (aEq y x) := n_e2 hN x y x h (n_e1 hN x)

theorem eta_trans {x y z : ℕ} (h : τ (aEq x y)) (h' : τ (aEq y z)) : τ (aEq x z) :=
  n_e2 hN y x z (eta_symm hN h) h'

/-- The equality of `τ` on the codes. -/
def tmSetoid : Setoid ℕ where
  r a b := τ (aEq a b)
  iseqv := ⟨fun a => n_e1 hN a, fun h => eta_symm hN h, fun h h' => eta_trans hN h h'⟩

/-- The carrier of the model: the codes modulo the equality of `τ`. -/
def NV : Type := Quotient (tmSetoid hN)

/-- The class of a code. -/
def nmk (a : ℕ) : NV hN := Quotient.mk (tmSetoid hN) a

theorem nmk_eq {a b : ℕ} : nmk hN a = nmk hN b ↔ τ (aEq a b) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The membership of `τ`, on the classes. -/
def nmem : NV hN → NV hN → Prop :=
  Quotient.lift₂ (s₁ := tmSetoid hN) (s₂ := tmSetoid hN) (fun a b => τ (aIn a b))
    (fun a b a' b' ha hb => propext ⟨fun h => n_e3 hN a a' b b' ha hb h,
      fun h => n_e3 hN a' a b' b (eta_symm hN ha) (eta_symm hN hb) h⟩)

/-- The singleton, on the classes. -/
def nsing : NV hN → NV hN :=
  Quotient.map (sa := tmSetoid hN) (sb := tmSetoid hN) (fun a => sgT a)
    (fun a b h => n_e4a hN a b h)

/-- The unordered pair, on the classes. -/
def nup : NV hN → NV hN → NV hN :=
  Quotient.map₂ (sa := tmSetoid hN) (sb := tmSetoid hN) (sc := tmSetoid hN)
    (fun a b => upT a b) (fun a a' ha b b' hb => n_e4b hN a a' b b' ha hb)

theorem nmem_mk (a b : ℕ) : nmem hN (nmk hN a) (nmk hN b) ↔ τ (aIn a b) := Iff.rfl

theorem nsing_mk (a : ℕ) : nsing hN (nmk hN a) = nmk hN (sgT a) := rfl

theorem nup_mk (a b : ℕ) : nup hN (nmk hN a) (nmk hN b) = nmk hN (upT a b) := rfl

theorem nop_mk (a b : ℕ) :
    nup hN (nsing hN (nmk hN a)) (nup hN (nmk hN a) (nmk hN b)) = nmk hN (opT a b) := rfl

theorem nmk_surj (x : NV hN) : ∃ a : ℕ, x = nmk hN a :=
  Quotient.inductionOn x (fun a => ⟨a, rfl⟩)

set_option maxHeartbeats 400000 in
/-- **The term model of a truth assignment that satisfies N.** -/
def model : ConNF.NF.NFModel (NV hN) where
  mem := nmem hN
  sing := nsing hN
  up := nup hN
  ext := by
    intro x y
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    obtain ⟨b, rfl⟩ := nmk_surj hN y
    intro h
    exact (nmk_eq hN).mpr (n_m1 hN a b (h (nmk hN (dT a b))))
  mem_sing := by
    intro x y
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    obtain ⟨b, rfl⟩ := nmk_surj hN y
    exact (n_m2 hN a b).trans (nmk_eq hN).symm
  mem_up := by
    intro x y z
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    obtain ⟨b, rfl⟩ := nmk_surj hN y
    obtain ⟨c, rfl⟩ := nmk_surj hN z
    exact (n_m3 hN a b c).trans (or_congr (nmk_eq hN).symm (nmk_eq hN).symm)
  inter := by
    intro x y
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    obtain ⟨b, rfl⟩ := nmk_surj hN y
    refine ⟨nmk hN (inT a b), fun z => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN z
    exact n_m4 hN a b c
  compl := by
    intro x
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    refine ⟨nmk hN (coT a), fun z => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN z
    exact n_m5 hN a c
  singletonImage := by
    intro x
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    refine ⟨nmk hN (siT a), fun z w => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN z
    obtain ⟨e, rfl⟩ := nmk_surj hN w
    exact n_m6 hN a c e
  insertion2 := by
    intro x
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    refine ⟨nmk hN (i2T a), fun p q r => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN p
    obtain ⟨e, rfl⟩ := nmk_surj hN q
    obtain ⟨f, rfl⟩ := nmk_surj hN r
    exact n_m7 hN a c e f
  insertion3 := by
    intro x
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    refine ⟨nmk hN (i3T a), fun p q r => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN p
    obtain ⟨e, rfl⟩ := nmk_surj hN q
    obtain ⟨f, rfl⟩ := nmk_surj hN r
    exact n_m8 hN a c e f
  vCross := by
    intro x
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    refine ⟨nmk hN (vcT a), fun p => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN p
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := n_m9a hN a c h
      refine ⟨nmk hN (p1T c), nmk hN (p2T c), ?_, h2⟩
      show nmk hN c = nup hN (nsing hN (nmk hN (p1T c))) (nup hN (nmk hN (p1T c)) (nmk hN (p2T c)))
      rw [nop_mk]
      exact (nmk_eq hN).mpr h1
    · rintro ⟨q, r, e, hm⟩
      obtain ⟨e', rfl⟩ := nmk_surj hN q
      obtain ⟨f, rfl⟩ := nmk_surj hN r
      change nmk hN c = nup hN (nsing hN (nmk hN e')) (nup hN (nmk hN e') (nmk hN f)) at e
      rw [nop_mk] at e
      exact n_m9b hN a c e' f ((nmk_eq hN).mp e) hm
  typeLower := by
    intro x
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    refine ⟨nmk hN (tlT a), fun p => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN p
    constructor
    · intro h q
      obtain ⟨e, rfl⟩ := nmk_surj hN q
      exact n_m10a hN a c e h
    · intro h
      exact n_m10b hN a c (h (nmk hN (wtT c a)))
  converse := by
    intro x
    obtain ⟨a, rfl⟩ := nmk_surj hN x
    refine ⟨nmk hN (cvT a), fun p q => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN p
    obtain ⟨e, rfl⟩ := nmk_surj hN q
    exact n_m11 hN a c e
  cardinalOne := by
    refine ⟨nmk hN c1T, fun p => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN p
    constructor
    · intro h
      refine ⟨nmk hN (elT c), ?_⟩
      show nmk hN c = nsing hN (nmk hN (elT c))
      rw [nsing_mk]
      exact (nmk_eq hN).mpr (n_m12a hN c h)
    · rintro ⟨q, e⟩
      obtain ⟨e', rfl⟩ := nmk_surj hN q
      change nmk hN c = nsing hN (nmk hN e') at e
      rw [nsing_mk] at e
      exact n_m12b hN c e' ((nmk_eq hN).mp e)
  subset := by
    refine ⟨nmk hN sbT, fun p q => ?_⟩
    obtain ⟨c, rfl⟩ := nmk_surj hN p
    obtain ⟨e, rfl⟩ := nmk_surj hN q
    constructor
    · intro h r
      obtain ⟨f, rfl⟩ := nmk_surj hN r
      exact n_m13a hN c e f h
    · intro h
      exact n_m13b hN c e (h (nmk hN (wsT c e)))

/-- The term model satisfies extensionality and every instance of stratified comprehension. -/
theorem isNF : ConNF.NF.IsNF (NV hN) (nmem hN) := (model hN).isNF

/-! ### Membership in the terms of this file -/

theorem ext' {a b : ℕ} (h : ∀ c : ℕ, τ (aIn c a) ↔ τ (aIn c b)) : τ (aEq a b) :=
  n_m1 hN a b (h (dT a b))

theorem mem_em (z : ℕ) : ¬ τ (aIn z emT) := fun h =>
  (n_m5 hN c1T z).mp ((n_m4 hN c1T (coT c1T) z).mp h).2 ((n_m4 hN c1T (coT c1T) z).mp h).1

theorem mem_un (x y z : ℕ) : τ (aIn z (unT x y)) ↔ τ (aIn z x) ∨ τ (aIn z y) := by
  unfold unT
  rw [n_m5 hN, n_m4 hN, n_m5 hN, n_m5 hN]
  tauto

theorem mem_ad (x b z : ℕ) : τ (aIn z (adT x b)) ↔ τ (aIn z x) ∨ τ (aEq z b) := by
  unfold adT
  rw [mem_un hN, n_m2 hN]

theorem mem_rm (y b z : ℕ) : τ (aIn z (rmT y b)) ↔ τ (aIn z y) ∧ ¬ τ (aEq z b) := by
  unfold rmT
  rw [n_m4 hN, n_m5 hN, n_m2 hN]

end nf

/-! ### The Axiom of Counting in the term model -/

section counting

variable (hN : ∀ q : ℕ, NSat τ q) (hC : ∀ q : ℕ, CSat τ q)
include hC

theorem c_u1a (s x : ℕ) : τ (aIn s (usT x)) → τ (aEq s (sgT (elT s))) :=
  (hC (aIn s (usT x) + aEq s (sgT (elT s)) + 1)).u1a s x (by omega) (by omega)

theorem c_u1b (s x : ℕ) : τ (aIn s (usT x)) → τ (aIn (elT s) x) :=
  (hC (aIn s (usT x) + aIn (elT s) x + 1)).u1b s x (by omega) (by omega)

theorem c_u2 (a x : ℕ) : τ (aIn a x) → τ (aIn (sgT a) (usT x)) :=
  (hC (aIn a x + aIn (sgT a) (usT x) + 1)).u2 a x (by omega) (by omega)

theorem c_s1a (y k : ℕ) : τ (aIn y (scT k)) → τ (aIn (rmT y (w1T y k)) k) :=
  (hC (aIn y (scT k) + aIn (rmT y (w1T y k)) k + 1)).s1a y k (by omega) (by omega)

theorem c_s1b (y k : ℕ) : τ (aIn y (scT k)) → τ (aIn (w1T y k) y) :=
  (hC (aIn y (scT k) + aIn (w1T y k) y + 1)).s1b y k (by omega) (by omega)

theorem c_s2 (x b k : ℕ) : τ (aIn x k) → ¬ τ (aIn b x) → τ (aIn (adT x b) (scT k)) :=
  (hC (aIn x k + aIn b x + aIn (adT x b) (scT k) + 1)).s2 x b k (by omega) (by omega) (by omega)

theorem c_n1 : τ (aIn zrT ddT) := (hC (aIn zrT ddT + 1)).n1 (by omega)

theorem c_n2 (k : ℕ) : τ (aIn k ddT) → τ (aIn (scT k) ddT) :=
  (hC (aIn k ddT + aIn (scT k) ddT + 1)).n2 k (by omega) (by omega)

theorem c_k (x n : ℕ) : τ (aIn x n) → τ (aIn n ddT) → τ (aIn (usT x) n) :=
  (hC (aIn x n + aIn n ddT + aIn (usT x) n + 1)).k x n (by omega) (by omega) (by omega)

include hN

/-- Every zero of the term model is the class of `zrT`. -/
theorem zero_eq {z : NV hN} (hz : JensenNFU.IsZeroN (nmem hN) z) : z = nmk hN zrT := by
  obtain ⟨a, rfl⟩ := nmk_surj hN z
  refine (nmk_eq hN).mpr (ext' hN fun c => ?_)
  have h1 := hz (nmk hN c)
  rw [nmem_mk] at h1
  rw [h1]
  unfold zrT
  rw [n_m2 hN]
  constructor
  · intro h
    exact ext' hN fun w => ⟨fun hw => absurd ((nmem_mk hN w c).mpr hw) (h (nmk hN w)),
      fun hw => absurd hw (mem_em hN w)⟩
  · intro h w hw
    obtain ⟨b, rfl⟩ := nmk_surj hN w
    exact mem_em hN b (n_e3 hN b b c emT (n_e1 hN b) h ((nmem_mk hN b c).mp hw))

/-- Every successor of the class of `a` is the class of `scT a`. -/
theorem succ_eq {a : ℕ} {k' : NV hN} (hk : JensenNFU.IsSuccN (nmem hN) (nmk hN a) k') :
    k' = nmk hN (scT a) := by
  obtain ⟨a', rfl⟩ := nmk_surj hN k'
  refine (nmk_eq hN).mpr (ext' hN fun c => ?_)
  have h1 := hk (nmk hN c)
  rw [nmem_mk] at h1
  rw [h1]
  constructor
  · rintro ⟨x, hx, b, hb, hall⟩
    obtain ⟨x0, rfl⟩ := nmk_surj hN x
    obtain ⟨b0, rfl⟩ := nmk_surj hN b
    have h2 := c_s2 hC x0 b0 a ((nmem_mk hN x0 a).mp hx) (fun h => hb ((nmem_mk hN b0 x0).mpr h))
    have h3 : τ (aEq (adT x0 b0) c) := ext' hN fun z => by
      rw [mem_ad hN]
      have h4 := hall (nmk hN z)
      rw [nmem_mk, nmem_mk, nmk_eq] at h4
      exact h4.symm
    exact n_e3 hN (adT x0 b0) c (scT a) (scT a) h3 (n_e1 hN _) h2
  · intro h
    have h2 := c_s1a hC c a h
    have h3 := c_s1b hC c a h
    refine ⟨nmk hN (rmT c (w1T c a)), (nmem_mk hN _ _).mpr h2, nmk hN (w1T c a), ?_, fun z => ?_⟩
    · rw [nmem_mk, mem_rm hN]
      exact fun h4 => h4.2 (n_e1 hN _)
    · obtain ⟨z0, rfl⟩ := nmk_surj hN z
      rw [nmem_mk, nmem_mk, nmk_eq, mem_rm hN]
      constructor
      · intro hz
        by_cases he : τ (aEq z0 (w1T c a))
        · exact Or.inr he
        · exact Or.inl ⟨hz, he⟩
      · rintro (hz | hz)
        · exact hz.1
        · exact n_e3 hN (w1T c a) z0 c c (eta_symm hN hz) (n_e1 hN c) h3

/-- **The term model of a truth assignment that satisfies N and the nine clauses satisfies the
Axiom of Counting.** -/
theorem counting : JensenNFU.Counting (nmem hN) := by
  intro n hn x hx
  have hD : nmem hN n (nmk hN ddT) := by
    refine hn (nmk hN ddT) ⟨fun z hz => ?_, fun k hk k' hk' => ?_⟩
    · rw [zero_eq hN hC hz, nmem_mk]
      exact c_n1 hC
    · obtain ⟨a, rfl⟩ := nmk_surj hN k
      rw [succ_eq hN hC hk', nmem_mk]
      exact c_n2 hC a ((nmem_mk hN a ddT).mp hk)
  obtain ⟨a, rfl⟩ := nmk_surj hN n
  obtain ⟨c, rfl⟩ := nmk_surj hN x
  have hca : τ (aIn c a) := (nmem_mk hN c a).mp hx
  refine ⟨nmk hN (usT c), (nmem_mk hN _ _).mpr (c_k hC c a hca ((nmem_mk hN a ddT).mp hD)),
    fun s => ?_⟩
  obtain ⟨e, rfl⟩ := nmk_surj hN s
  rw [nmem_mk]
  constructor
  · intro h
    have h1 := c_u1a hC e c h
    have h2 := c_u1b hC e c h
    refine ⟨nmk hN (elT e), (nmem_mk hN _ _).mpr h2, fun z => ?_⟩
    obtain ⟨z0, rfl⟩ := nmk_surj hN z
    rw [nmem_mk, nmk_eq, ← n_m2 hN]
    exact ⟨fun hz => n_e3 hN z0 z0 e (sgT (elT e)) (n_e1 hN z0) h1 hz,
      fun hz => n_e3 hN z0 z0 (sgT (elT e)) e (n_e1 hN z0) (eta_symm hN h1) hz⟩
  · rintro ⟨a', ha', hall⟩
    obtain ⟨f, rfl⟩ := nmk_surj hN a'
    have h1 := c_u2 hC f c ((nmem_mk hN f c).mp ha')
    have h2 : τ (aEq (sgT f) e) := ext' hN fun z => by
      rw [n_m2 hN]
      have h3 := hall (nmk hN z)
      rw [nmem_mk, nmk_eq] at h3
      exact h3.symm
    exact n_e3 hN (sgT f) e (usT c) (usT c) h2 (n_e1 hN _) h1

end counting

end TermN

/-! ## Compactness -/

/-- **Compactness for truth assignments.** For a sequence `σ` of truth assignments there is a
truth assignment that agrees, below any given bound, with `σ q` for some `q` above the bound. -/
theorem exists_limit (σ : ℕ → ℕ → Prop) :
    ∃ τ : ℕ → Prop, ∀ q₀ : ℕ, ∃ q, q₀ ≤ q ∧ ∀ i, i + 1 ≤ q₀ → (σ q i ↔ τ i) := by
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  refine ⟨fun i => ∀ᶠ q in (U : Filter ℕ), σ q i, fun q₀ => ?_⟩
  have h1 : ∀ᶠ q in (U : Filter ℕ), q₀ ≤ q := hU (Filter.eventually_ge_atTop q₀)
  have h2 : ∀ i, i ∈ Finset.range q₀ →
      ∀ᶠ q in (U : Filter ℕ), (σ q i ↔ ∀ᶠ q' in (U : Filter ℕ), σ q' i) := by
    intro i _
    by_cases h : ∀ᶠ q' in (U : Filter ℕ), σ q' i
    · exact h.mono fun q hq => ⟨fun _ => h, fun _ => hq⟩
    · exact (Ultrafilter.eventually_not.mpr h).mono fun q hq => ⟨fun h' => absurd h' hq,
        fun h' => absurd h' h⟩
  have h3 := (Filter.eventually_all_finset (Finset.range q₀)).mpr h2
  obtain ⟨q, hq1, hq2⟩ := (h1.and h3).exists
  exact ⟨q, hq1, fun i hi => hq2 i (Finset.mem_range.mpr (by omega))⟩

/-- If for every standard `q` some truth assignment satisfies the instances of N and of the
nine clauses below `q`, then some truth assignment satisfies all of them. -/
theorem exists_assignment (h : ∀ q : ℕ, ∃ τ : ℕ → Prop, NSat τ q ∧ CSat τ q) :
    ∃ τ : ℕ → Prop, (∀ q : ℕ, NSat τ q) ∧ ∀ q : ℕ, CSat τ q := by
  choose σ hσ using h
  obtain ⟨τ, hτ⟩ := exists_limit σ
  refine ⟨τ, fun q₀ => ?_, fun q₀ => ?_⟩
  · obtain ⟨q, hq, hag⟩ := hτ q₀
    exact NSat.congr hag ((hσ q).1.mono hq)
  · obtain ⟨q, hq, hag⟩ := hτ q₀
    exact CSat.congr hag ((hσ q).2.mono hq)

/-- **A model of NF with the Axiom of Counting from the clauses.** -/
theorem exists_nfc_structure (h : ∀ q : ℕ, ∃ τ : ℕ → Prop, NSat τ q ∧ CSat τ q) :
    ∃ (W : Type) (mem : W → W → Prop), Nonempty W ∧ ConNF.NF.IsNF W mem ∧
      JensenNFU.Counting mem := by
  obtain ⟨τ, hN, hC⟩ := exists_assignment h
  exact ⟨TermN.NV hN, TermN.nmem hN, ⟨TermN.nmk hN 0⟩, TermN.isNF hN, TermN.counting hN hC⟩

namespace FFL.FirstOrder.SetTheory

/-- **`𝗡𝗙𝗖` is consistent if the clauses are finitely satisfiable**: if for every standard `q`
some truth assignment satisfies the instances of N and of the nine clauses for the Axiom of
Counting whose atoms have codes below `q`. -/
theorem consistent_nfc_of_clauses (h : ∀ q : ℕ, ∃ τ : ℕ → Prop, NSat τ q ∧ CSat τ q) :
    Entailment.Consistent 𝗡𝗙𝗖 := by
  obtain ⟨W, mem, hne, hnf, hcount⟩ := exists_nfc_structure h
  let _ : SetStructure W := ⟨fun y x ↦ mem x y⟩
  have hM : W↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗖 := by
    refine models_theory_iff.mpr fun φ hφ => ?_
    rcases hφ with hφ | hφ
    · exact models_theory_iff.mp (models_nf_of_isNF hnf) φ hφ
    · rw [show φ = Axiom.counting from hφ]
      exact models_counting_iff.mpr hcount
  exact consistent_of_model 𝗡𝗙𝗖 W

end FFL.FirstOrder.SetTheory
