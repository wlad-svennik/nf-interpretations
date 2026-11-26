module

public import NFUCountInterp
public import NFUConsistent

/-!
# Adapter for the independently stated NF+AxCount challenge

The substantive proofs are the uploaded development's `nfc_sem` and Specker's theorem.
This adapter only converts between two explicit first-order formula representations,
passes between the development's semantic and syntactic model predicates, and exposes
the unchanged mathematical conclusions in a compact, independently readable statement.
-/

set_option autoImplicit false

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

namespace Palomar

namespace Adapter

open JensenNFU

/-- A variable in a formula with no free variables is a de Bruijn index. -/
def termIndex {n : ℕ} : Semiterm ℒₛₑₜ Empty n → ℕ
  | #x => x
  | &x => isEmptyElim x
  | .func f _ => isEmptyElim f

theorem termIndex_val {N : Type} [Tarski.Structure ℒₛₑₜ N] {n : ℕ}
    (t : Semiterm ℒₛₑₜ Empty n) (e : Fin n → N) :
    (List.ofFn e)[termIndex t]? = some (t.val e Empty.elim) := by
  match t with
  | #x => simp [termIndex]
  | &x => exact isEmptyElim x
  | .func f _ => exact isEmptyElim f

def atomTFm {n k : ℕ} (r : (ℒₛₑₜ).Rel k)
    (v : Fin k → Semiterm ℒₛₑₜ Empty n) : TFm :=
  match r with
  | .eq => .eq (termIndex (v 0)) (termIndex (v 1))
  | .mem => .mem (termIndex (v 0)) (termIndex (v 1))

/-- Quantifier annotations do not affect untyped satisfaction, so zero suffices here. -/
def toTFm : {n : ℕ} → Semisentence ℒₛₑₜ n → TFm
  | _, .verum => .all 0 (.eq 0 0)
  | _, .falsum => .neg (.all 0 (.eq 0 0))
  | _, .rel r v => atomTFm r v
  | _, .nrel r v => .neg (atomTFm r v)
  | _, .and φ ψ => .and (toTFm φ) (toTFm ψ)
  | _, .or φ ψ => .neg (.and (.neg (toTFm φ)) (.neg (toTFm ψ)))
  | _, .all φ => .all 0 (toTFm φ)
  | _, .exs φ => .neg (.all 0 (.neg (toTFm φ)))

section evaluation

variable {N : Type} [s : Tarski.Structure ℒₛₑₜ N] [Tarski.Structure.Eq ℒₛₑₜ N]

theorem sat_atomTFm {n k : ℕ} (r : (ℒₛₑₜ).Rel k)
    (v : Fin k → Semiterm ℒₛₑₜ Empty n) (e : Fin n → N) :
    TFm.Sat (fun a b ↦ s.rel Language.Mem.mem ![a, b]) (atomTFm r v) (List.ofFn e) ↔
      s.rel r (fun i ↦ (v i).val e Empty.elim) := by
  cases r with
  | eq =>
    simp only [atomTFm, TFm.Sat, termIndex_val]
    have h : s.rel Language.Set.Rel.eq (fun i ↦ (v i).val e Empty.elim) ↔
        (v 0).val e Empty.elim = (v 1).val e Empty.elim :=
      Tarski.Structure.eq_lang (L := ℒₛₑₜ) (v := fun i ↦ (v i).val e Empty.elim)
    rw [h]
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      rw [Option.some.inj ha, Option.some.inj hb]
      exact hab
    · intro h
      exact ⟨_, _, rfl, rfl, h⟩
  | mem =>
    simp only [atomTFm, TFm.Sat, termIndex_val]
    have h : (fun i ↦ (v i).val e Empty.elim) =
        ![(v 0).val e Empty.elim, (v 1).val e Empty.elim] := Matrix.fun_eq_vec_two _
    rw [h]
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      rw [Option.some.inj ha, Option.some.inj hb]
      exact hab
    · intro h
      exact ⟨_, _, rfl, rfl, h⟩

/-- The conversion preserves every formula's meaning in every structure. -/
theorem eval_toTFm {n : ℕ} (φ : Semisentence ℒₛₑₜ n) :
    ∀ e : Fin n → N,
    TFm.Sat (fun a b ↦ s.rel Language.Mem.mem ![a, b]) (toTFm φ) (List.ofFn e) ↔
      N ⊧/e φ := by
  classical
  induction φ using Semiformula.rec' with
  | hverum => intro e; simp [toTFm, TFm.Sat]
  | hfalsum => intro e; simp [toTFm, TFm.Sat]
  | hrel r v =>
    intro e
    exact (sat_atomTFm r v e).trans Semiformula.eval_rel'.symm
  | hnrel r v =>
    intro e
    simp only [toTFm, TFm.Sat, sat_atomTFm]
    exact Semiformula.eval_nrel'.symm
  | hand φ ψ ihφ ihψ =>
    intro e
    simp [toTFm, TFm.Sat, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    intro e
    simp only [toTFm, TFm.Sat, ihφ, ihψ]
    simp <;> tauto
  | hall φ ih =>
    intro e
    simp only [toTFm, TFm.Sat, Semiformula.eval_all]
    refine forall_congr' fun a => ?_
    simpa only [List.ofFn_vecCons_j] using ih (a :> e)
  | hexs φ ih =>
    intro e
    simp only [toTFm, TFm.Sat, Semiformula.eval_ex, not_forall, not_not]
    refine exists_congr fun a => ?_
    simpa only [List.ofFn_vecCons_j] using ih (a :> e)

end evaluation

/-- The NF and NFU formula grammars differ only by their namespace. -/
def toNFFormula : TFm → ConNF.NF.Fm
  | .mem i j => .mem i j
  | .eq i j => .eq i j
  | .neg φ => .neg (toNFFormula φ)
  | .and φ ψ => .and (toNFFormula φ) (toNFFormula ψ)
  | .all t φ => .all t (toNFFormula φ)

theorem strat_toNFFormula (φ : TFm) (Γ : List ℕ) :
    TFm.Strat Γ φ ↔ ConNF.NF.Strat Γ (toNFFormula φ) := by
  induction φ generalizing Γ <;> simp_all [toNFFormula, TFm.Strat, ConNF.NF.Strat]

theorem sat_toNFFormula {V : Type} (mem : V → V → Prop) (φ : TFm) (env : List V) :
    TFm.Sat mem φ env ↔ ConNF.NF.Sat mem (toNFFormula φ) env := by
  induction φ generalizing env with
  | mem i j => rfl
  | eq i j => rfl
  | neg φ ih => exact not_congr (ih env)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ env) (ihψ env)
  | all t φ ih => exact forall_congr' fun a => ih (a :: env)

theorem isNFU_of_isNF {V : Type} {mem : V → V → Prop} (h : ConNF.NF.IsNF V mem) :
    JensenNFU.IsNFU V mem where
  ext := fun x y _ hxy => h.ext x y hxy
  comprehension := by
    intro t Γ φ hφ params hp
    obtain ⟨y, hy⟩ := h.comprehension t Γ (toNFFormula φ)
      ((strat_toNFFormula φ _).mp hφ) params hp
    exact ⟨y, fun x => (hy x).trans (sat_toNFFormula mem φ (x :: params)).symm⟩

end Adapter

/-- Uniform parameter-free interpretation, obtained from the uploaded `nfc_sem`. -/
theorem nfuic_interprets_nfc :
    ∃ δ ε : JensenNFU.TFm,
      ∀ (V : Type) (memV : V → V → Prop), Nonempty V →
        JensenNFU.IsNFU V memV → JensenNFU.UnivInfinite memV → JensenNFU.Counting memV →
        ∃ (A : Type) (memA : A → A → Prop) (f : A → V),
          Nonempty A ∧ ConNF.NF.IsNF A memA ∧ JensenNFU.Counting memA ∧
          Function.Injective f ∧
          (∀ x : V, JensenNFU.TFm.Sat memV δ [x] ↔ ∃ a, f a = x) ∧
          ∀ a b : A, JensenNFU.TFm.Sat memV ε [f a, f b] ↔ memA a b := by
  refine ⟨Adapter.toTFm HinU.nfcDomF, Adapter.toTFm HinU.nfcMemF, ?_⟩
  intro V memV hne hU hI hC
  letI : Nonempty V := hne
  letI : SetStructure V := ⟨fun y x => memV x y⟩
  have hUI : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := Jensen.models_nfui_of_isNFU hU hI
  have hUIC : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖 := models_theory_iff.mpr fun φ hφ => by
    rcases hφ with hφ | hφ
    · exact models_theory_iff.mp hUI φ hφ
    · rw [show φ = Axiom.counting from hφ]
      exact models_counting_iff.mpr hC
  have := hUIC
  obtain ⟨A, memA, f, hneA, hNF, hCA, hf, hd, hm⟩ := nfc_sem (M := V)
  refine ⟨A, memA, f, hneA, hNF, hCA, hf, ?_, ?_⟩
  · intro x
    have he : JensenNFU.TFm.Sat memV (Adapter.toTFm HinU.nfcDomF) [x] ↔
        V ⊧/![x] HinU.nfcDomF := by
      simpa only [List.ofFn_succ, List.ofFn_zero] using
        (Adapter.eval_toTFm (N := V) HinU.nfcDomF ![x])
    exact he.trans (hd x)
  · intro a b
    have he : JensenNFU.TFm.Sat memV (Adapter.toTFm HinU.nfcMemF) [f a, f b] ↔
        V ⊧/![f a, f b] HinU.nfcMemF := by
      simpa only [List.ofFn_succ, List.ofFn_zero] using
        (Adapter.eval_toTFm (N := V) HinU.nfcMemF ![f a, f b])
    exact he.trans (hm a b)

/-- The reverse direction retains the universe and membership unchanged. -/
theorem nfc_interprets_nfuic (V : Type) (memV : V → V → Prop)
    (hNF : ConNF.NF.IsNF V memV) (hC : JensenNFU.Counting memV) :
    JensenNFU.IsNFU V memV ∧ JensenNFU.UnivInfinite memV ∧ JensenNFU.Counting memV := by
  obtain ⟨u, hu⟩ := hNF.exists_univ
  letI : Nonempty V := ⟨u⟩
  letI : SetStructure V := ⟨fun y x => memV x y⟩
  have hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙 := models_nf_of_isNF hNF
  have hi : V↓[ℒₛₑₜ] ⊧ Axiom.universeInfinite :=
    models_of_provable hT nf_provable_universeInfinite
  refine ⟨Adapter.isNFU_of_isNF hNF, ?_, hC⟩
  simpa [models_iff, Axiom.universeInfinite, JensenNFU.UnivInfinite] using hi

end Palomar
