module

public import Foundation.FirstOrder.LK.Interpretation

@[expose] public section

set_option autoImplicit false

/-!
# A translation depends only on its formulas

Two translations of a language `L₂` into theories `T` and `T'` of the same language, with the
same domain and the same formulas for the relation and function symbols, translate every
formula of `L₂` in the same way (`DirectTranslation.translate_congr`). So an interpretation in
`T` can be reused in an extension of `T`.
-/

namespace FFL.FirstOrder.DirectTranslation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T T' : Theory L₁} [𝗘𝗤 _ ⪯ T] [𝗘𝗤 _ ⪯ T']
  (π : DirectTranslation T L₂) (π' : DirectTranslation T' L₂)

theorem varEqual_congr (hd : π.domain = π'.domain)
    (hf : ∀ {k} (f : L₂.Func k), π.func f = π'.func f) {ξ : Type*} {n : ℕ} :
    ∀ t : Semiterm L₂ ξ n, π.varEqual t = π'.varEqual t
  | #x => rfl
  | &x => rfl
  | .func f v => by
    have ih : ∀ i, π.varEqual (v i) = π'.varEqual (v i) := fun i => varEqual_congr hd hf (v i)
    simp only [varEqual, hd, hf, ih]

theorem translateRel_congr (hd : π.domain = π'.domain)
    (hr : ∀ {k} (r : L₂.Rel k), π.rel r = π'.rel r)
    (hf : ∀ {k} (f : L₂.Func k), π.func f = π'.func f) {ξ : Type*} {n k : ℕ} (r : L₂.Rel k)
    (v : Fin k → Semiterm L₂ ξ n) : π.translateRel r v = π'.translateRel r v := by
  have ih : ∀ i, π.varEqual (v i) = π'.varEqual (v i) := fun i => varEqual_congr π π' hd hf (v i)
  simp only [translateRel, hd, hr, ih]

/-- **Two translations with the same formulas translate every formula in the same way.** -/
theorem translate_congr (hd : π.domain = π'.domain)
    (hr : ∀ {k} (r : L₂.Rel k), π.rel r = π'.rel r)
    (hf : ∀ {k} (f : L₂.Func k), π.func f = π'.func f) {ξ : Type*} {n : ℕ}
    (φ : Semiformula L₂ ξ n) : π.translate φ = π'.translate φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [translate_rel, translate_rel, translateRel_congr π π' hd hr hf]
  | hnrel r v => rw [translate_nrel, translate_nrel, translateRel_congr π π' hd hr hf]
  | hand φ ψ ih1 ih2 => simp [ih1, ih2]
  | hor φ ψ ih1 ih2 => simp [ih1, ih2]
  | hall φ ih => rw [translate_all, translate_all, ih]; simp only [fal, hd]
  | hexs φ ih => rw [translate_ex, translate_ex, ih]; simp only [exs, hd]

end FFL.FirstOrder.DirectTranslation
