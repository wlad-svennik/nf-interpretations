module

public import NFInterpretsMac

@[expose] public section

set_option autoImplicit false

/-!
# "`ℵₙ` exists" as a sentence of set theory

For each natural number `n` of the metatheory, the sentence `Axiom.aleph n` of the language of
membership and equality says that there is a list `λ₀, …, λₙ` of von Neumann ordinals with
`λ₀ = ω` and each `λᵢ₊₁` the least ordinal that does not map one-to-one into `λᵢ`.

* `OrdS x`: `x` is transitive and any two of its members are equal or one is a member of the
  other.
* `InjS f a b`: `f`, as a set of Kuratowski pairs, maps the members of `a` one-to-one into
  the members of `b`.
* `NextS x y`: `y` is an ordinal that does not map one-to-one into `x`, and every member of `y`
  does. `OmegaS x`: `x` is an ordinal with an empty member, closed under successor, all of
  whose members are empty or successors of members.
* `IsAleph n y`: `y = ℵₙ`. `models_aleph_iff`: the sentence means `∃ y, IsAleph n y`.
* `𝗭𝗔 n` is `𝗭` with `Axiom.aleph n`, and `𝗭𝗔ω` is `𝗭` with all of them.

These notions are not stratified, so the formulas are built as `UDef`s; this file adds the
missing connectives of `UDef`. It does not mention NF.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace UDef

variable {k : ℕ} {R S : URel k}

def eq (i j : Fin k) : UDef (k := k) (fun _ _ v ↦ v i = v j) :=
  ⟨Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![#i, #j], fun _ _ _ => Iff.rfl⟩

def or (d : UDef R) (e : UDef S) : UDef (fun V _ v ↦ R V v ∨ S V v) :=
  ⟨d.φ ⋎ e.φ, fun V _ v => by simp [d.eval, e.eval]⟩

def not (d : UDef R) : UDef (fun V _ v ↦ ¬ R V v) :=
  ⟨∼d.φ, fun V _ v => by simp [d.eval]⟩

def imp (d : UDef R) (e : UDef S) : UDef (fun V _ v ↦ R V v → S V v) :=
  ⟨d.φ 🡒 e.φ, fun V _ v => by simp [d.eval, e.eval]⟩

def iff (d : UDef R) (e : UDef S) : UDef (fun V _ v ↦ (R V v ↔ S V v)) :=
  ((d.imp e).and (e.imp d)).congr fun _ _ _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

def all {R : URel (k + 1)} (d : UDef R) : UDef (fun V _ v ↦ ∀ a : V, R V (a :> v)) :=
  ⟨∀¹ d.φ, fun V _ v => by simp [d.eval]⟩

end UDef

/-! ### The notions -/

section defs

variable {V : Type} [SetStructure V]

/-- `x` is a von Neumann ordinal. -/
def OrdS (x : V) : Prop :=
  (∀ u v : V, u ∈ x → v ∈ u → v ∈ x) ∧ ∀ u v : V, u ∈ x → v ∈ x → (u = v ∨ u ∈ v ∨ v ∈ u)

/-- `f` maps the members of `a` one-to-one into the members of `b`. -/
def InjS (f a b : V) : Prop :=
  (∀ u : V, u ∈ a → ∃ v : V, v ∈ b ∧ Hin.Rl f u v) ∧
  (∀ u u' v : V, u ∈ a → u' ∈ a → Hin.Rl f u v → Hin.Rl f u' v → u = u')

/-- `y` is the least ordinal that does not map one-to-one into `x`. -/
def NextS (x y : V) : Prop :=
  OrdS y ∧ (¬ ∃ f : V, InjS f y x) ∧ ∀ z : V, z ∈ y → ∃ f : V, InjS f z x

/-- `x` is the least infinite ordinal. -/
def OmegaS (x : V) : Prop :=
  OrdS x ∧ (∃ e : V, e ∈ x ∧ ∀ z : V, z ∉ e) ∧
  (∀ u : V, u ∈ x → ∃ s : V, s ∈ x ∧ ∀ z : V, z ∈ s ↔ z ∈ u ∨ z = u) ∧
  (∀ u : V, u ∈ x → (∀ z : V, z ∉ u) ∨ ∃ p : V, p ∈ x ∧ ∀ z : V, z ∈ u ↔ z ∈ p ∨ z = p)

/-- `y = ℵₙ`. -/
def IsAleph : ℕ → V → Prop
  | 0, x => OmegaS x
  | n + 1, y => ∃ x : V, IsAleph n x ∧ NextS x y

end defs

/-! ### The formulas -/

def ordSU : UDef (k := 1) (fun _ _ v ↦ OrdS (v 0)) :=
  ((UDef.all (UDef.all ((UDef.mem 1 2).imp ((UDef.mem 0 1).imp (UDef.mem 0 2))))).and
    (UDef.all (UDef.all ((UDef.mem 1 2).imp ((UDef.mem 0 2).imp ((UDef.eq 1 0).or
      ((UDef.mem 1 0).or (UDef.mem 0 1)))))))).congr fun _ _ _ => Iff.rfl

def injSU : UDef (k := 3) (fun _ _ v ↦ InjS (v 0) (v 1) (v 2)) :=
  ((UDef.all ((UDef.mem 0 2).imp (UDef.ex ((UDef.mem 0 4).and
      ((UDef.ofS Hin.rlD).comp ![2, 1, 0]))))).and
    (UDef.all (UDef.all (UDef.all ((UDef.mem 2 4).imp ((UDef.mem 1 4).imp
      (((UDef.ofS Hin.rlD).comp ![3, 2, 0]).imp (((UDef.ofS Hin.rlD).comp ![3, 1, 0]).imp
        (UDef.eq 2 1))))))))).congr fun _ _ _ => Iff.rfl

def nextSU : UDef (k := 2) (fun _ _ v ↦ NextS (v 0) (v 1)) :=
  ((ordSU.comp ![1]).and (((UDef.ex (injSU.comp ![0, 2, 1])).not).and
    (UDef.all ((UDef.mem 0 2).imp (UDef.ex (injSU.comp ![0, 1, 2])))))).congr
    fun _ _ _ => Iff.rfl

def omegaSU : UDef (k := 1) (fun _ _ v ↦ OmegaS (v 0)) :=
  ((ordSU.comp ![0]).and ((UDef.ex ((UDef.mem 0 1).and (UDef.all (UDef.mem 0 1).not))).and
    ((UDef.all ((UDef.mem 0 1).imp (UDef.ex ((UDef.mem 0 2).and
        (UDef.all ((UDef.mem 0 1).iff ((UDef.mem 0 2).or (UDef.eq 0 2)))))))).and
      (UDef.all ((UDef.mem 0 1).imp ((UDef.all (UDef.mem 0 1).not).or
        (UDef.ex ((UDef.mem 0 2).and
          (UDef.all ((UDef.mem 0 2).iff ((UDef.mem 0 1).or (UDef.eq 0 1)))))))))))).congr
    fun _ _ _ => Iff.rfl

def alephU : (n : ℕ) → UDef (k := 1) (fun _ _ v ↦ IsAleph n (v 0))
  | 0 => omegaSU.congr fun _ _ _ => Iff.rfl
  | n + 1 => (UDef.ex (((alephU n).comp ![0]).and (nextSU.comp ![0, 1]))).congr
      fun _ _ _ => Iff.rfl

namespace Axiom

/-- **"`ℵₙ` exists."** -/
def aleph (n : ℕ) : SetTheorySentence := (UDef.ex (alephU n)).φ

end Axiom

/-- **The sentence means the property.** -/
lemma models_aleph_iff {n : ℕ} {N : Type} [Nonempty N] [SetStructure N] :
    N↓[ℒₛₑₜ] ⊧ Axiom.aleph n ↔ ∃ y : N, IsAleph n y :=
  (UDef.ex (alephU n)).eval N ![]

/-- `𝗭` with "`ℵₙ` exists". -/
abbrev ZermeloAleph (n : ℕ) : SetTheory := 𝗭 ∪ {Axiom.aleph n}

@[inherit_doc] notation "𝗭𝗔" => ZermeloAleph

/-- `𝗭` with "`ℵₙ` exists" for every `n`. -/
abbrev ZermeloAlephs : SetTheory := 𝗭 ∪ Set.range Axiom.aleph

@[inherit_doc] notation "𝗭𝗔ω" => ZermeloAlephs

instance (n : ℕ) : 𝗘𝗤 _ ⪯ 𝗭𝗔 n :=
  let : 𝗘𝗤 _ ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

instance : 𝗘𝗤 _ ⪯ 𝗭𝗔ω :=
  let : 𝗘𝗤 _ ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

end FFL.FirstOrder.SetTheory
