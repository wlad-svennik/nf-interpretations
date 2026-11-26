module

public import MGraphOps

@[expose] public section

set_option autoImplicit false

/-!
# The pointed graphs of a model of `𝗠` form a model of `𝗠`

Continues `MGraphOps.lean`.

* `trq`: a formula read in a structure that is the quotient of a set `&0` of a model, with
  membership given by a set `&1` of pairs and equality by a set `&2` of pairs. The result is
  bounded (`trq_bdd`), and it means the formula in the quotient structure (`trq_eval`).
* `qg_sep`: the last condition of `IsMacBase` for `QG V`. The structure of the members of a
  class is the quotient of the set of the children of the point.
* **`isMacBase_qg`**, **`qgModelsM : (QG V) ⊧ 𝗠`**.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-! ### A formula read in a quotient of a set -/

section quotient

/-- A term with its parameters moved up by three. -/
def sh3 {n : ℕ} : Semiterm ℒₛₑₜ ℕ n → Semiterm ℒₛₑₜ ℕ n
  | #x => #x
  | &x => &(x + 3)
  | .func f _ => Empty.elim f

/-- An atomic formula read in the quotient: membership is `&1`, equality is `&2`. -/
def trqRel {n : ℕ} :
    {k : ℕ} → (ℒₛₑₜ).Rel k → (Fin k → Semiterm ℒₛₑₜ ℕ n) → Semiformula ℒₛₑₜ ℕ n
  | _, Language.Set.Rel.eq, v => Rew.embSubsts ![&2, v 0, v 1] ▹ MH.prB.φ
  | _, Language.Set.Rel.mem, v => Rew.embSubsts ![&1, v 0, v 1] ▹ MH.prB.φ

/-- A formula read in the quotient of the set `&0`. -/
def trq {n : ℕ} : Semiformula ℒₛₑₜ ℕ n → Semiformula ℒₛₑₜ ℕ n
  | .rel r v => trqRel r (fun i ↦ sh3 (v i))
  | .nrel r v => ∼trqRel r (fun i ↦ sh3 (v i))
  | ⊤ => ⊤
  | ⊥ => ⊥
  | φ ⋏ ψ => trq φ ⋏ trq ψ
  | φ ⋎ ψ => trq φ ⋎ trq ψ
  | ∀¹ φ => ∀¹[memOp.operator ![#0, &0]] trq φ
  | ∃¹ φ => ∃¹[memOp.operator ![#0, &0]] trq φ

theorem trqRel_bdd {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ℕ n) :
    (Bounding.mem ℒₛₑₜ).Closure (trqRel r v) := by
  cases r with
  | eq => exact MH.prB.bdd.rew _
  | mem => exact MH.prB.bdd.rew _

theorem trq_bdd : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n), (Bounding.mem ℒₛₑₜ).Closure (trq φ) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => exact Bounding.Closure.verum _
  | hfalsum => exact Bounding.Closure.falsum _
  | hrel r v => exact trqRel_bdd r _
  | hnrel r v =>
    have h := trqRel_bdd r (fun i ↦ sh3 (v i))
    show (Bounding.mem ℒₛₑₜ).Closure (∼trqRel r (fun i ↦ sh3 (v i)))
    simpa using h
  | hand φ ψ ih1 ih2 => exact Bounding.Closure.and ih1 ih2
  | hor φ ψ ih1 ih2 => exact Bounding.Closure.or ih1 ih2
  | hall φ ih =>
    exact Bounding.Closure.ball (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive]) ih
  | hexs φ ih =>
    exact Bounding.Closure.bexs (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive]) ih

variable {M : Type} [SetStructure M] {U : Type} [SetStructure U]

/-- The parameters: the set, the two sets of pairs, and the parameters of the formula. -/
def rho3 (C Mm Eqq : M) (ε : ℕ → M) : ℕ → M
  | 0 => C
  | 1 => Mm
  | 2 => Eqq
  | k + 3 => ε k

/-- The member of the set that a term denotes. -/
def tvq {C : M} {n : ℕ} (u : Semiterm ℒₛₑₜ ℕ n) (e : Fin n → {c : M // c ∈ C})
    (ε : ℕ → {c : M // c ∈ C}) : {c : M // c ∈ C} :=
  match u with
  | #x => e x
  | &x => ε x
  | .func f _ => Empty.elim f

lemma sh3_val (C Mm Eqq : M) {n : ℕ} (u : Semiterm ℒₛₑₜ ℕ n) (e : Fin n → {c : M // c ∈ C})
    (ε : ℕ → {c : M // c ∈ C}) :
    (sh3 u).val (M := M) (fun i ↦ (e i : M)) (rho3 C Mm Eqq fun k ↦ (ε k : M)) =
      (tvq u e ε : M) := by
  match u with
  | #x => rfl
  | &x => rfl
  | .func f _ => exact Empty.elim f

lemma tvq_val {C : M} (π : {c : M // c ∈ C} → U) {n : ℕ} (u : Semiterm ℒₛₑₜ ℕ n)
    (e : Fin n → {c : M // c ∈ C}) (ε : ℕ → {c : M // c ∈ C}) :
    u.val (M := U) (fun i ↦ π (e i)) (fun k ↦ π (ε k)) = π (tvq u e ε) := by
  match u with
  | #x => rfl
  | &x => rfl
  | .func f _ => exact Empty.elim f

lemma trqRel_eval_eq {n : ℕ} (b : Fin n → M) (f : ℕ → M) (t u : Semiterm ℒₛₑₜ ℕ n) :
    Eval (M := M) b f (trqRel Language.Set.Rel.eq ![t, u]) ↔
      MH.Pr (f 2) (t.val b f) (u.val b f) := by
  show Eval (M := M) b f (Rew.embSubsts ![&2, t, u] ▹ MH.prB.φ) ↔ _
  rw [eval_embSubsts]
  exact MH.prB.eval M _

lemma trqRel_eval_mem {n : ℕ} (b : Fin n → M) (f : ℕ → M) (t u : Semiterm ℒₛₑₜ ℕ n) :
    Eval (M := M) b f (trqRel Language.Set.Rel.mem ![t, u]) ↔
      MH.Pr (f 1) (t.val b f) (u.val b f) := by
  show Eval (M := M) b f (Rew.embSubsts ![&1, t, u] ▹ MH.prB.φ) ↔ _
  rw [eval_embSubsts]
  exact MH.prB.eval M _

/-- **The meaning of the rewritten formula** is that of the formula in the quotient. -/
theorem trq_eval (C Mm Eqq : M) (π : {c : M // c ∈ C} → U) (hsur : Function.Surjective π)
    (hmem : ∀ c c' : {c : M // c ∈ C}, π c ∈ π c' ↔ MH.Pr Mm (c : M) (c' : M))
    (heq : ∀ c c' : {c : M // c ∈ C}, π c = π c' ↔ MH.Pr Eqq (c : M) (c' : M))
    (ε : ℕ → {c : M // c ∈ C}) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (e : Fin n → {c : M // c ∈ C}),
      Eval (M := M) (fun i ↦ (e i : M)) (rho3 C Mm Eqq fun k ↦ (ε k : M)) (trq φ) ↔
        Eval (M := U) (fun i ↦ π (e i)) (fun k ↦ π (ε k)) φ := by
  have hcons : ∀ {n : ℕ} (c : {c : M // c ∈ C}) (e : Fin n → {c : M // c ∈ C}),
      ((c : M) :> fun i ↦ (e i : M)) = fun i ↦ (((c :> e) i : {c : M // c ∈ C}) : M) := by
    intro n c e; funext i; cases i using Fin.cases <;> rfl
  have hconsU : ∀ {n : ℕ} (c : {c : M // c ∈ C}) (e : Fin n → {c : M // c ∈ C}),
      (π c :> fun i ↦ π (e i)) = fun i ↦ π ((c :> e) i) := by
    intro n c e; funext i; cases i using Fin.cases <;> rfl
  have hrel : ∀ {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ℕ n)
      (e : Fin n → {c : M // c ∈ C}),
      Eval (M := M) (fun i ↦ (e i : M)) (rho3 C Mm Eqq fun k ↦ (ε k : M))
          (trqRel r (fun i ↦ sh3 (v i))) ↔
        Eval (M := U) (fun i ↦ π (e i)) (fun k ↦ π (ε k)) (Semiformula.rel r v) := by
    intro n k r v e
    cases r with
    | eq =>
      have h1 : (fun i ↦ sh3 (v i)) = ![sh3 (v 0), sh3 (v 1)] := Matrix.fun_eq_vec_two _
      rw [h1, trqRel_eval_eq, sh3_val, sh3_val]
      show MH.Pr Eqq _ _ ↔ ((v 0).val (M := U) _ _ = (v 1).val (M := U) _ _)
      rw [tvq_val, tvq_val]
      exact (heq _ _).symm
    | mem =>
      have h1 : (fun i ↦ sh3 (v i)) = ![sh3 (v 0), sh3 (v 1)] := Matrix.fun_eq_vec_two _
      rw [h1, trqRel_eval_mem, sh3_val, sh3_val]
      show MH.Pr Mm _ _ ↔ ((v 0).val (M := U) _ _ ∈ (v 1).val (M := U) _ _)
      rw [tvq_val, tvq_val]
      exact (hmem _ _).symm
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e; exact Iff.rfl
  | hfalsum => intro e; exact Iff.rfl
  | hrel r v => intro e; exact hrel r v e
  | hnrel r v =>
    intro e
    show Eval (M := M) _ _ (∼trqRel r (fun i ↦ sh3 (v i))) ↔
      Eval (M := U) _ _ (∼Semiformula.rel r v)
    simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
    exact not_congr (hrel r v e)
  | hand φ ψ ih1 ih2 =>
    intro e
    show Eval (M := M) _ _ (trq φ ⋏ trq ψ) ↔ Eval (M := U) _ _ (φ ⋏ ψ)
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
    rw [ih1 e, ih2 e]
  | hor φ ψ ih1 ih2 =>
    intro e
    show Eval (M := M) _ _ (trq φ ⋎ trq ψ) ↔ Eval (M := U) _ _ (φ ⋎ ψ)
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    rw [ih1 e, ih2 e]
  | hall φ ih =>
    intro e
    show Eval (M := M) _ _ (∀¹[memOp.operator ![#0, &0]] trq φ) ↔ Eval (M := U) _ _ (∀¹ φ)
    simp only [eval_ball, eval_memOp, Matrix.cons_val_zero]
    rw [eval_all]
    constructor
    · intro H u
      obtain ⟨c, rfl⟩ := hsur u
      have h1 := H (c : M) c.2
      rw [hcons] at h1
      have h2 := (ih _).mp h1
      rw [← hconsU] at h2
      exact h2
    · intro H x hx
      have h2 := H (π ⟨x, hx⟩)
      rw [hconsU] at h2
      have h1 := (ih _).mpr h2
      rw [← hcons] at h1
      exact h1
  | hexs φ ih =>
    intro e
    show Eval (M := M) _ _ (∃¹[memOp.operator ![#0, &0]] trq φ) ↔ Eval (M := U) _ _ (∃¹ φ)
    simp only [eval_bexs, eval_memOp, Matrix.cons_val_zero]
    rw [eval_ex]
    constructor
    · rintro ⟨x, hx, h1⟩
      have h1' : Eval (M := M) (((⟨x, hx⟩ : {c : M // c ∈ C}) : M) :> fun i ↦ (e i : M))
          (rho3 C Mm Eqq fun k ↦ (ε k : M)) (trq φ) := h1
      rw [hcons] at h1'
      have h2 := (ih _).mp h1'
      rw [← hconsU] at h2
      exact ⟨π ⟨x, hx⟩, h2⟩
    · rintro ⟨u, hu⟩
      obtain ⟨c, rfl⟩ := hsur u
      rw [hconsU] at hu
      have h1 := (ih _).mpr hu
      rw [← hcons] at h1
      exact ⟨(c : M), c.2, h1⟩

end quotient

namespace MG

open MH

section defs

variable {V : Type} [SetStructure V]

/-- The class of `(E, c)` is a member of the class of `(E, c')`, by a bisimulation in `P`. -/
def MemQ (c c' P E : V) : Prop := MemCh c P E E c'

/-- The classes of `(E, c)` and `(E, c')` are equal, by a bisimulation in `P`. -/
def EqQ (c c' P E : V) : Prop := BisIn P E c E c'

end defs

def memQB : BDef (k := 4) (fun V _ v ↦ MemQ (v 0) (v 1) (v 2) (v 3)) :=
  (memChB.comp ![0, 2, 3, 3, 1]).congr fun _ _ _ => Iff.rfl

def eqQB : BDef (k := 4) (fun V _ v ↦ EqQ (v 0) (v 1) (v 2) (v 3)) :=
  (bisInB.comp ![2, 3, 0, 3, 1]).congr fun _ _ _ => Iff.rfl

section sep

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-- Membership of classes, bounded, for any sets of nodes. -/
theorem memCh_iff' {E Ez pz c N Nz : V} (hN : ∀ z, z ∈ fld E → z ∈ N) (hc : c ∈ N)
    (hNz : ∀ z, z ∈ fld Ez → z ∈ Nz) :
    MemCh c (℘ (prodS N Nz)) E Ez pz ↔ ∃ d, Pr Ez d pz ∧ Bis E c Ez d := by
  constructor
  · rintro ⟨e, he, w, -, d, -, hop, k⟩
    exact ⟨d, ⟨e, he, hop⟩, bisIn_bis k⟩
  · rintro ⟨d, ⟨e, he, hop⟩, k⟩
    obtain ⟨w, hw, hdw⟩ := pr_fst_mem hop
    exact ⟨e, he, w, hw, d, hdw, hop, bis_trim hN hc hNz (hNz _ (pr_fld ⟨e, he, hop⟩).1) k⟩

/-- **Every subset of the members of a class that is definable in the structure of those
members is the extension of a class.** -/
theorem qg_sep (t : QG V) (ψ : SetTheorySemiproposition 1) (ε : ℕ → extSet t) :
    ∃ y : QG V, ∀ z, z ∈ y ↔ ∃ hz : z ∈ extSet t, Eval (M := extSet t) ![⟨z, hz⟩] ε ψ := by
  obtain ⟨g, rfl⟩ := exists_rep t
  let N : V := nodes g
  have hN := nodes_ok g
  let C : V := sepB (k := 2) (prB.comp ![1, 0, 2]) N ![g.E, g.p]
  have hC : ∀ c, c ∈ C ↔ Pr g.E c g.p := fun c =>
    (mem_sepB _ _ _ c).trans ⟨fun k => k.2, fun k => ⟨(hN c _ k).1, k⟩⟩
  have hCN : ∀ c, c ∈ C → c ∈ N := fun c hc => (hN c _ ((hC c).mp hc)).1
  let P : V := ℘ (prodS N N)
  let Mm : V := relB (k := 2) memQB C C ![P, g.E]
  have hMm : ∀ c c', Pr Mm c c' ↔ c ∈ C ∧ c' ∈ C ∧ MemQ c c' P g.E :=
    fun c c' => pr_relB memQB C C ![P, g.E] c c'
  let Eqq : V := relB (k := 2) eqQB C C ![P, g.E]
  have hEqq : ∀ c c', Pr Eqq c c' ↔ c ∈ C ∧ c' ∈ C ∧ EqQ c c' P g.E :=
    fun c c' => pr_relB eqQB C C ![P, g.E] c c'
  let π : {c : V // c ∈ C} → extSet (mkQ g) := fun c =>
    ⟨mkQ (g.at (c : V)),
      show mkQ (g.at (c : V)) ∈ mkQ g from mem_mkQ.mpr ⟨(c : V), (hC c).mp c.2, rfl⟩⟩
  have hsur : Function.Surjective π := by
    intro u
    obtain ⟨c, hc, e⟩ := mem_mkQ.mp u.2
    exact ⟨⟨c, (hC c).mpr hc⟩, Subtype.ext e.symm⟩
  have hmem : ∀ c c' : {c : V // c ∈ C}, π c ∈ π c' ↔ Pr Mm (c : V) (c' : V) := by
    intro c c'
    have h1 : π c ∈ π c' ↔ mkQ (g.at c) ∈ mkQ (g.at c') := Iff.rfl
    rw [h1, mkQ_mem, hMm]
    have h2 : MemQ (c : V) (c' : V) P g.E ↔ ∃ d, Pr g.E d c' ∧ Bis g.E c g.E d :=
      memCh_iff' (fld_sub_nodes g) (hCN c c.2) (fld_sub_nodes g)
    exact ⟨fun k => ⟨c.2, c'.2, h2.mpr k⟩, fun k => h2.mp k.2.2⟩
  have heq : ∀ c c' : {c : V // c ∈ C}, π c = π c' ↔ Pr Eqq (c : V) (c' : V) := by
    intro c c'
    have h1 : π c = π c' ↔ mkQ (g.at c) = mkQ (g.at c') := Subtype.ext_iff
    rw [h1, mkQ_eq, hEqq]
    exact ⟨fun k => ⟨c.2, c'.2, bis_trim (fld_sub_nodes g) (hCN c c.2) (fld_sub_nodes g)
      (hCN c' c'.2) k⟩, fun k => bisIn_bis k.2.2⟩
  let ε' : ℕ → {c : V // c ∈ C} := fun k => Classical.choose (hsur (ε k))
  have hε' : (fun k ↦ π (ε' k)) = ε := funext fun k => Classical.choose_spec (hsur (ε k))
  obtain ⟨S, hS⟩ := sep_raw (trq ψ) (trq_bdd ψ) (rho3 C Mm Eqq fun k ↦ (ε' k : V)) C
  have key : ∀ a : {c : V // c ∈ C}, (a : V) ∈ S ↔ Eval (M := extSet (mkQ g)) ![π a] ε ψ := by
    intro a
    have h1 := trq_eval C Mm Eqq π hsur hmem heq ε' ψ ![a]
    have e1 : (fun i ↦ ((![a] i : {c : V // c ∈ C}) : V)) = ![(a : V)] := by
      funext i; fin_cases i; rfl
    have e2 : (fun i ↦ π (![a] i)) = ![π a] := by
      funext i; fin_cases i; rfl
    rw [e1, e2, hε'] at h1
    exact (hS a).trans ⟨fun k => h1.mp k.2, fun k => ⟨a.2, h1.mpr k⟩⟩
  refine ⟨mkS g N hN S, fun z => ?_⟩
  rw [mem_mkS g N hN fun a ha => hCN a ((hS a).mp ha).1]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haC : a ∈ C := ((hS a).mp ha).1
    exact ⟨(π ⟨a, haC⟩).2, (key ⟨a, haC⟩).mp ha⟩
  · rintro ⟨hz, h⟩
    obtain ⟨a, ha⟩ := hsur ⟨z, hz⟩
    rw [← ha] at h
    exact ⟨a, (key a).mpr h, (congrArg Subtype.val ha).symm⟩

/-- **The pointed graphs modulo bisimulation satisfy the conditions of `IsMacBase`.** -/
theorem isMacBase_qg : IsMacBase (QG V) :=
  ⟨qg_ext, qg_found, qg_pair, qg_power, qg_tco, qg_inf, qg_sep⟩

instance qgNonempty : Nonempty (QG V) := isMacBase_qg.nonempty

/-- **The pointed graphs of a model of `𝗠`, modulo bisimulation, are a model of `𝗠`.** -/
instance qgModelsM : (QG V)↓[ℒₛₑₜ] ⊧* 𝗠 := isMacBase_qg.models

end sep

end MG

end FFL.FirstOrder.SetTheory
