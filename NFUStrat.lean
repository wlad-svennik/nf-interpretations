module

public import NFStrat

@[expose] public section

set_option autoImplicit false

/-!
# Stratified comprehension in models of `𝗡𝗙𝗨𝗜`

`NFStrat.lean` packages a formula, a stratification of it and its meaning as an `SDef`, and
proves comprehension for every `SDef` in a model of `𝗡𝗙`. The `SDef`s do not depend on the
theory. This file proves the same comprehension theorem in a model of Jensen's `𝗡𝗙𝗨` (in the
language of membership and equality, with no predicate for sets), and states extensionality in
the form that `𝗡𝗙𝗨` has: for objects with a member.

* `nfu_ext`: two objects with the same members, one of which has a member, are equal.
* `SDef.comprehensionU`: `{x | R (x, p)}` is the extension of some object, for every relation
  with an `SDef` and all parameters `p`.
* `nfui_infinite`: the axiom of Infinity of `𝗡𝗙𝗨𝗜`, in a model.
-/

namespace FFL.FirstOrder

open Semiformula

namespace SetTheory

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

lemma models_nfu_of_nfui : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨 :=
  models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hT φ (Or.inl hφ)

/-- Extensionality in a model of `𝗡𝗙𝗨`, for objects with a member. -/
theorem nfu_ext {x y : V} (hx : ∃ z, z ∈ x) (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  have h0 : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨 := models_nfu_of_nfui
  have := by
    simpa [models_iff] using
      Theory.models V 𝗡𝗙𝗨 NewFoundationsWithUrelements.extensionality
  obtain ⟨z, hz⟩ := hx
  exact this x y z hz h

/-- **Stratified comprehension in a model of `𝗡𝗙𝗨`**: if `R` has a stratified definition, then
`{x | R (x, p)}` is the extension of some object, for all parameters `p`. -/
theorem SDef.comprehensionU {k : ℕ} {τ : Fin (k + 1) → ℕ} {R : URel (k + 1)} (d : SDef τ R)
    (p : Fin k → V) : ∃ y : V, ∀ x, x ∈ y ↔ R V (x :> p) := by
  classical
  have h0 : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨 := models_nfu_of_nfui
  let ω : Rew ℒₛₑₜ Empty (k + 1) ℕ 1 :=
    Rew.bind ((#0 : Semiterm ℒₛₑₜ ℕ 1) :> fun i : Fin k ↦ &(i : ℕ)) Empty.elim
  let ψ : SetTheorySemiproposition 1 := ω ▹ d.φ
  let σ : ℕ → ℕ := fun n ↦ if h : n < k then τ (Fin.succ ⟨n, h⟩) else 0
  have hψ : ψ.IsStratified :=
    ⟨σ, ![τ 0], Semiformula.stratified_rew 0 d.φ ω τ ![τ 0]
      (by
        intro x
        cases x using Fin.cases with
        | zero => simp [ω]
        | succ x => simp [ω, σ]; rfl)
      (fun x => x.elim) d.strat⟩
  have := by
    simpa [models_iff, Axiom.comprehensionSchema] using
      Theory.models V 𝗡𝗙𝗨 (NewFoundationsWithUrelements.comprehension ψ hψ)
  let x₀ : V := Classical.arbitrary V
  obtain ⟨y, hy⟩ := this (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀)
  refine ⟨y, fun x => (hy x).trans ?_⟩
  have e : (Semiterm.val ![x] (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) ∘ ω ∘ Semiterm.bvar) =
      (x :> p) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [ω]
    | succ i => simp [ω]
  have e2 : (Semiterm.val ![x] (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) ∘ ω ∘
      Semiterm.fvar) = (Empty.elim : Empty → V) := funext fun z => z.elim
  rw [eval_rew, e, e2]
  exact d.eval V _

/-- The axiom of Infinity of `𝗡𝗙𝗨𝗜`, in a model. -/
theorem nfui_infinite : ∃ F : V, (∀ e : V, (∀ z, z ∉ e) → e ∈ F) ∧
    (∀ s ∈ F, ∀ b s' : V, (∀ z, z ∈ s' ↔ z ∈ s ∨ z = b) → s' ∈ F) ∧
    ∀ u : V, (∀ z, z ∈ u) → u ∉ F := by
  have h1 : V↓[ℒₛₑₜ] ⊧ Axiom.universeInfinite := models_theory_iff.mp hT _ (Or.inr rfl)
  simpa [models_iff, Axiom.universeInfinite] using h1

end model

end SetTheory

end FFL.FirstOrder
