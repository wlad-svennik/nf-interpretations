module

public import NFTheories

@[expose] public section

set_option autoImplicit false

/-!
# Rosser's Axiom of Counting as a first-order sentence

The sentence `Axiom.counting` of the language `ℒₛₑₜ` of membership and equality:

  every natural number `n` contains, with each of its members `x`, a set whose members are
  the singletons of the members of `x`.

In the usual notation this is `T n = n` for every natural number `n`.

The natural numbers are Frege's. Only membership is used, so the sentence can be read both in
NF and in Jensen's NFU, where no object without members is singled out as the empty set:

* zero is the set of the objects without members (in NF this is `{∅}`);
* the successor of `k` is the set of the `y` whose members are those of some `x ∈ k` and one
  further object;
* `n` is a natural number when it belongs to every family that contains zero and is closed
  under successor.

`JensenNFU.Counting mem` is the same statement about a structure, and
`models_counting_iff` says that the sentence means it.

The theories: `𝗖𝗢𝗨𝗡𝗧 = {Axiom.counting}`, `𝗡𝗙𝗖 = 𝗡𝗙 ∪ 𝗖𝗢𝗨𝗡𝗧` and `𝗡𝗙𝗨𝗜𝗖 = 𝗡𝗙𝗨𝗜 ∪ 𝗖𝗢𝗨𝗡𝗧`.
-/

/-! ### The statement about a structure -/

namespace JensenNFU

variable {V : Type*}

/-- `z` is zero: its members are the objects without members. -/
def IsZeroN (mem : V → V → Prop) (z : V) : Prop := ∀ e, mem e z ↔ ∀ w, ¬mem w e

/-- `k'` is the successor of `k`: its members are the `y` whose members are those of some
`x ∈ k` and one further object. -/
def IsSuccN (mem : V → V → Prop) (k k' : V) : Prop :=
  ∀ y, mem y k' ↔ ∃ x, mem x k ∧ ∃ b, ¬mem b x ∧ ∀ z, mem z y ↔ mem z x ∨ z = b

/-- `n` is a natural number: it belongs to every family that contains zero and is closed under
successor. -/
def IsNatN (mem : V → V → Prop) (n : V) : Prop :=
  ∀ F, ((∀ z, IsZeroN mem z → mem z F) ∧ ∀ k, mem k F → ∀ k', IsSuccN mem k k' → mem k' F) →
    mem n F

/-- **The Axiom of Counting**, as a property of a structure: every natural number `n`
contains, with each of its members `x`, a set whose members are the singletons of the members
of `x`. -/
def Counting (mem : V → V → Prop) : Prop :=
  ∀ n, IsNatN mem n → ∀ x, mem x n →
    ∃ y, mem y n ∧ ∀ s, mem s y ↔ ∃ a, mem a x ∧ ∀ z, mem z s ↔ z = a

end JensenNFU

namespace FFL.FirstOrder

namespace SetTheory

namespace Axiom

/-- **Rosser's Axiom of Counting.** -/
def counting : SetTheorySentence :=
  “∀ n, (∀ F, ((∀ z, (∀ e, e ∈ z ↔ (∀ w, w ∉ e)) → z ∈ F) ∧
        (∀ k, k ∈ F → ∀ l, (∀ y, y ∈ l ↔ (∃ x, x ∈ k ∧ ∃ b, b ∉ x ∧ ∀ z, z ∈ y ↔ z ∈ x ∨ z = b)) →
          l ∈ F)) → n ∈ F) →
      ∀ x, x ∈ n → ∃ y, y ∈ n ∧ ∀ s, s ∈ y ↔ (∃ a, a ∈ x ∧ ∀ z, z ∈ s ↔ z = a)”

end Axiom

/-- The theory containing only the Axiom of Counting. -/
def CountingAxiom : SetTheory := {Axiom.counting}

notation "𝗖𝗢𝗨𝗡𝗧" => CountingAxiom

/-- NF with the Axiom of Counting. -/
abbrev NFCounting : SetTheory := 𝗡𝗙 ∪ 𝗖𝗢𝗨𝗡𝗧

notation "𝗡𝗙𝗖" => NFCounting

/-- NFU with the axiom of infinity and the Axiom of Counting. -/
abbrev NFUInfinityCounting : SetTheory := 𝗡𝗙𝗨𝗜 ∪ 𝗖𝗢𝗨𝗡𝗧

notation "𝗡𝗙𝗨𝗜𝗖" => NFUInfinityCounting

instance : 𝗡𝗙 ⪯ 𝗡𝗙𝗖 := inferInstance

instance : 𝗡𝗙𝗨𝗜 ⪯ 𝗡𝗙𝗨𝗜𝗖 := inferInstance

instance : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗖 :=
  let : 𝗘𝗤 _ ⪯ 𝗡𝗙 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗨𝗜𝗖 :=
  let : 𝗘𝗤 _ ⪯ 𝗡𝗙𝗨𝗜 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

/-- **The sentence means the property.** -/
lemma models_counting_iff {N : Type} [Nonempty N] [SetStructure N] :
    N↓[ℒₛₑₜ] ⊧ Axiom.counting ↔ JensenNFU.Counting (fun a b : N ↦ a ∈ b) := by
  simp [models_iff, Axiom.counting, JensenNFU.Counting, JensenNFU.IsNatN, JensenNFU.IsSuccN,
    JensenNFU.IsZeroN]

end SetTheory

end FFL.FirstOrder
