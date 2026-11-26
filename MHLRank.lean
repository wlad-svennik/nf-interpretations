module

public import MHRankSupply
public import MHER
public import MHInterpretsMAC
public import MGraphRank

@[expose] public section

set_option autoImplicit false

/-!
# A level of the constructible sets that is a model of `𝗭𝗖` with rank axioms

In a model `V` of `𝗠𝗛`.

* `LimFull X`: `X` is a constructible transitive set with `ω` as a member, and every member of
  `X` is a member of a level at a full height that is itself a member of `X`. (The union of the
  levels at an increasing sequence of full heights, of limit length, is such a set.)
* `isMacBase_limFull`, `fullsep_limFull`, `ac_limFull`, **`limFull_models_zc`**: the structure
  of the members of such a set is a model of `𝗭𝗖`. Separation for all formulas: a definable
  subset is constructible (`sep_good`), and a constructible subset of a member of a level at a
  full height is a member of that level. Choice: from the order of the constructible sets.
* **`hasRank_limFull`**: the rank axioms up to `N` hold in it, if `X` has as a member a sequence
  of levels at full heights on the ordinals up to the `(N + 2)`-nd of a chain of next heights.
  The hierarchy is made inside the structure (`exists_powH`, for a model of `𝗠`); its value at
  the numeral `j` is a member of the level at the `j`-th height of the chain; and the next
  height does not map one-to-one into the level at a height by a constructible relation
  (`not_linj_nextH`).
* **`exists_zc_ranks`**: such a set exists when the rank axiom for `4 (N + 3) + 15` holds in
  `V`: the supply of `MHRankSupply.lean` gives a ladder of full heights (`exists_ladder'`).
* **`consistent_zcr_of_consistent_mhr : Con(𝗠𝗛𝗥) → Con(𝗭𝗖𝗥)`**, by compactness.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-! ### Compactness for the rank axioms over any theory -/

/-- **Compactness.** If `T` with the rank axioms up to `N` is consistent for every `N`, then
`T` with all the rank axioms is consistent. -/
theorem consistent_ranks_of_forall (T : SetTheory)
    (h : ∀ N : ℕ, Entailment.Consistent (T ∪ {φ | ∃ j, j ≤ N ∧ φ = Axiom.rank j})) :
    Entailment.Consistent (T ∪ Set.range Axiom.rank) := by
  by_contra hZ
  have hbot : (T ∪ Set.range Axiom.rank) ⊢ (⊥ : Sentence ℒₛₑₜ) :=
    Entailment.not_consistent_iff_inconsistent.mp hZ ⊥
  obtain ⟨𝓕, h𝓕, hfin, hF⟩ := Entailment.Compact.finite_provable hbot
  have key : ∀ S : Set (Sentence ℒₛₑₜ), S.Finite → S ⊆ T ∪ Set.range Axiom.rank →
      ∃ N : ℕ, ∀ φ ∈ S, φ ∈ T ∨ ∃ k, k ≤ N ∧ φ = Axiom.rank k := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨0, fun φ hφ => absurd hφ (Set.notMem_empty φ)⟩
    | @insert ψ S _ _ ih =>
      intro hsub
      obtain ⟨N, hN⟩ := ih fun φ hφ => hsub (Set.mem_insert_of_mem _ hφ)
      rcases hsub (Set.mem_insert ψ S) with hψ | ⟨k, rfl⟩
      · refine ⟨N, fun φ hφ => ?_⟩
        rcases hφ with rfl | hφ
        · exact Or.inl hψ
        · exact hN φ hφ
      · refine ⟨max N k, fun φ hφ => ?_⟩
        rcases hφ with rfl | hφ
        · exact Or.inr ⟨k, le_max_right _ _, rfl⟩
        · rcases hN φ hφ with h' | ⟨j, hj, rfl⟩
          · exact Or.inl h'
          · exact Or.inr ⟨j, le_trans hj (le_max_left _ _), rfl⟩
  obtain ⟨N, hN⟩ := key 𝓕 ((Set.adjunctiveSet_finite_iff 𝓕).mp hfin) h𝓕
  have hle : 𝓕 ⪯ (T ∪ {φ | ∃ j, j ≤ N ∧ φ = Axiom.rank j}) :=
    Entailment.WeakerThan.ofAxm! fun {φ} hφ => by
      rcases hN φ hφ with h' | ⟨k, hk, rfl⟩
      · exact Entailment.by_axm (Or.inl h')
      · exact Entailment.by_axm (Or.inr ⟨k, hk, rfl⟩)
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (hle.pbl hF)) (h N)

/-- Zermelo set theory with Choice and the rank axioms for every `n`. -/
abbrev ZermeloChoiceRanks : SetTheory := 𝗭𝗖 ∪ Set.range Axiom.rank

@[inherit_doc] notation "𝗭𝗖𝗥" => ZermeloChoiceRanks

instance : 𝗘𝗤 _ ⪯ 𝗭𝗖𝗥 :=
  let : 𝗘𝗤 _ ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this
    (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl (Or.inl h))

namespace MH

section defs

variable {V : Type} [SetStructure V]

/-- `x` is a member of a set that `Lam` gives for a member of `lam`. -/
def InLad (x lam Lam : V) : Prop :=
  ∃ q, q ∈ Lam ∧ ∃ u, u ∈ q ∧ ∃ A, A ∈ u ∧ (x ∈ A ∧ ∃ α, α ∈ lam ∧ IsOp q α A)

/-- `q` is a pair whose first component is a member of `s`. -/
def FstIn (q s : V) : Prop := ∃ α, α ∈ s ∧ ∃ u, u ∈ q ∧ ∃ A, A ∈ u ∧ IsOp q α A

/-- `c` is a member of `C` and of a member of `F`. -/
def ChoR (c C F : V) : Prop := c ∈ C ∧ ∃ Y, Y ∈ F ∧ c ∈ Y

end defs

def inLadB : BDef (k := 3) (fun V _ v ↦ InLad (v 0) (v 1) (v 2)) :=
  (BDef.bex 2 (BDef.bex 0 (BDef.bex 0 ((BDef.mem 3 0).and
    (BDef.bex 4 (isOpB.comp ![3, 0, 1])))))).congr fun _ _ _ => Iff.rfl

def fstInB : BDef (k := 2) (fun V _ v ↦ FstIn (v 0) (v 1)) :=
  (BDef.bex 1 (BDef.bex 1 (BDef.bex 0 (isOpB.comp ![3, 2, 0])))).congr fun _ _ _ => Iff.rfl

def choRB : BDef (k := 3) (fun V _ v ↦ ChoR (v 0) (v 1) (v 2)) :=
  ((BDef.mem 0 1).and (BDef.bex 2 (BDef.mem 1 0))).congr fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem inLad_iff {x lam Lam : V} :
    InLad x lam Lam ↔ ∃ α A, α ∈ lam ∧ (Pr Lam α A ∧ x ∈ A) := by
  constructor
  · rintro ⟨q, hq, u, -, A, -, hx, α, hα, hop⟩
    exact ⟨α, A, hα, ⟨q, hq, hop⟩, hx⟩
  · rintro ⟨α, A, hα, ⟨q, hq, hop⟩, hx⟩
    obtain ⟨u, hu, hAu⟩ := pr_snd_mem hop
    exact ⟨q, hq, u, hu, A, hAu, hx, α, hα, hop⟩

theorem fstIn_iff {q s : V} : FstIn q s ↔ ∃ α A, α ∈ s ∧ IsOp q α A := by
  constructor
  · rintro ⟨α, hα, u, -, A, -, hop⟩
    exact ⟨α, A, hα, hop⟩
  · rintro ⟨α, A, hα, hop⟩
    obtain ⟨u, hu, hAu⟩ := pr_snd_mem hop
    exact ⟨α, hα, u, hu, A, hAu, hop⟩

/-! ### Heights -/

/-- The heights of a supply, as a sequence: each is full and the next height after the one
before, and the level at the last maps one-to-one into the last base set. -/
theorem supply_chain {r : ℕ} {T : ℕ → V} {ρ Sq : V} (sup : Supply r T ρ Sq) :
    ∃ e : ℕ → V, (∀ j, j ≤ r → Full (e j)) ∧ (∀ j, j < r → NextH (e j) (e (j + 1))) ∧
      VInj (Lev (e r)) (T (r + 2)) := by
  obtain ⟨ν₀, μ, hν, hit, hv⟩ := supply_heights sup r le_rfl
  obtain ⟨hl, hom⟩ := hgtV_lim (sup.base 0 (by omega)) hν
  obtain ⟨μs, h0, hs, hlast⟩ := iterH_seq r μ hit
  have hF : ∀ j, j ≤ r → Full (μs j) := by
    intro j
    induction j with
    | zero => exact fun _ => nextH_full hl hom h0
    | succ j ih =>
      intro hj
      have hj' := ih (by omega)
      exact nextH_full hj'.lim hj'.omega (hs j (by omega))
  refine ⟨μs, hF, fun j hj => hs j hj, ?_⟩
  rw [hlast]
  exact hv

/-- **The next height after `κ` does not map one-to-one into the level at `κ` by a
constructible relation.** -/
theorem not_linj_nextH {κ μ : V} (hκ : Lim κ) (hom : (om : V) ∈ κ) (h : NextH κ μ) :
    ¬LInj μ (Lev κ) := by
  intro hinj
  obtain ⟨δ, hδ, hall⟩ := lnext_reg hκ hom h.1 h.2.1 h.2.2.1 h.2.2.2 (con_ord h.1.1)
    (fun v hv => ord_mem_lev_lim h.1 v hv) hinj
  exact ord_not_mem_lev (ord_mem h.1.1 hδ) (hall δ hδ)

/-! ### Unions of levels at full heights -/

/-- `X` is a constructible transitive set with `ω` as a member in which every member is a
member of a level at a full height that is a member of `X`. -/
structure LimFull (X : V) : Prop where
  con : Con X
  tr : Tr X
  om : (om : V) ∈ X
  full : ∀ x, x ∈ X → ∃ μ, Full μ ∧ (x ∈ Lev μ ∧ Lev μ ∈ X)

theorem LimFull.con_mem {X x : V} (hX : LimFull X) (hx : x ∈ X) : Con x :=
  let ⟨μ, hμ, h, _⟩ := hX.full x hx
  ⟨μ, hμ.lim.1, h⟩

/-- A constructible subset of a member of `X` is a member of `X`. -/
theorem LimFull.sub {X x w : V} (hX : LimFull X) (hx : x ∈ X) (hw : Con w)
    (hsub : ∀ z, z ∈ w → z ∈ x) : w ∈ X :=
  let ⟨μ, hμ, h, l⟩ := hX.full x hx
  hX.tr (Lev μ) l w (hμ.sub x w h hw hsub)

theorem limFull_nonempty {X : V} (hX : LimFull X) : Nonempty (extSet X) := ⟨⟨om, hX.om⟩⟩

/-- **Separation for all formulas** in the structure of the members of `X`. -/
theorem fullsep_limFull {X : V} (hX : LimFull X) (ψ : SetTheorySemiproposition 1)
    (ε : ℕ → extSet X) (t : extSet X) :
    ∃ y : extSet X, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := extSet X) ![z] ε ψ := by
  obtain ⟨Y, hY, hYm⟩ := sep_good closed_true (good_of_con hX.con) ψ ε
    (fun k => good_of_con (hX.con_mem (ε k).2))
  have hYc : Con Y := con_of_good hY
  let y₀ : V := sepB (k := 1) (BDef.mem 0 1) t.1 ![Y]
  have hy₀ : ∀ z, z ∈ y₀ ↔ z ∈ t.1 ∧ z ∈ Y := fun z => mem_sepB (BDef.mem 0 1) t.1 ![Y] z
  have hy₀c : Con y₀ := con_sepB (BDef.mem 0 1) (hX.con_mem t.2) ![Y] (fun i => by
    have e := Fin.eq_zero i
    subst e
    exact hYc)
  have hy₀X : y₀ ∈ X := hX.sub t.2 hy₀c fun z hz => ((hy₀ z).mp hz).1
  refine ⟨⟨y₀, hy₀X⟩, fun z => ?_⟩
  have h1 : z ∈ (⟨y₀, hy₀X⟩ : extSet X) ↔ z.1 ∈ t.1 ∧ z.1 ∈ Y := hy₀ z.1
  rw [h1, hYm]
  exact and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨z.2, h⟩⟩

/-- The structure of the members of `X` satisfies the conditions `IsMacBase`. -/
theorem isMacBase_limFull {X : V} (hX : LimFull X) : IsMacBase (extSet X) := by
  refine ⟨fun x y h => ?_, fun x hx => ?_, fun x y => ?_, fun x => ?_, fun x => ?_, ?_, ?_⟩
  · refine Subtype.ext (mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · exact (h ⟨z, hX.tr x.1 x.2 z hz⟩).mp hz
    · exact (h ⟨z, hX.tr y.1 y.2 z hz⟩).mpr hz
  · obtain ⟨y, hy⟩ := hx
    obtain ⟨m, hm, hmin⟩ := m_found x.1 ⟨y.1, hy⟩
    exact ⟨⟨m, hX.tr x.1 x.2 m hm⟩, hm, fun z hz => hmin z.1 hz⟩
  · obtain ⟨μ₁, f₁, h₁, l₁⟩ := hX.full x.1 x.2
    obtain ⟨μ₂, f₂, h₂, l₂⟩ := hX.full y.1 y.2
    rcases ord_tri f₁.lim.1 f₂.lim.1 with e | e | e
    · exact ⟨⟨Lev μ₂, l₂⟩, lev_mono f₂.lim.1 e _ h₁, h₂⟩
    · rw [e] at h₁
      exact ⟨⟨Lev μ₂, l₂⟩, h₁, h₂⟩
    · exact ⟨⟨Lev μ₁, l₁⟩, h₁, lev_mono f₁.lim.1 e _ h₂⟩
  · obtain ⟨μ, f, h, l⟩ := hX.full x.1 x.2
    exact ⟨⟨Lev μ, l⟩, fun z hz => f.sub x.1 z.1 h (hX.con_mem z.2)
      fun w hw => hz ⟨w, hX.tr z.1 z.2 w hw⟩ hw⟩
  · obtain ⟨μ, f, h, l⟩ := hX.full x.1 x.2
    exact ⟨⟨Lev μ, l⟩, fun z hz => lev_tr f.lim.1 x.1 h z.1 hz,
      fun y hy z hz => lev_tr f.lim.1 y.1 hy z.1 hz⟩
  · have h0 : (∅ : V) ∈ X := hX.tr om hX.om ∅ empty_mem_om
    refine ⟨⟨om, hX.om⟩, ⟨⟨∅, h0⟩, empty_mem_om,
      fun z hz => absurd (show z.1 ∈ (∅ : V) from hz) (by simp)⟩, fun x hx => ?_⟩
    have hs : sc x.1 ∈ (om : V) := sc_mem_om hx
    refine ⟨⟨sc x.1, hX.tr om hX.om _ hs⟩, hs, fun z => ?_⟩
    have h1 : z.1 ∈ sc x.1 ↔ z.1 = x.1 ∨ z.1 ∈ x.1 := mem_sc
    exact h1.trans (or_congr_left Subtype.ext_iff.symm)
  · exact sep_of_fullsep (fullsep_limFull hX)

/-- **Choice** in the structure of the members of `X`. -/
theorem ac_limFull {X : V} (hX : LimFull X) : ∀ F : extSet X, (∀ Y ∈ F, ∃ y, y ∈ Y) →
    (∀ Y ∈ F, ∀ Z ∈ F, (∃ x ∈ Y, x ∈ Z) → Y = Z) →
    ∃ C : extSet X, ∀ Y ∈ F, ∃! x, x ∈ C ∧ x ∈ Y := by
  intro F hne hdis
  let W₀ : Set V := {x | Con x}
  have hi : Function.Injective (fun w : W₀ => (w : V)) := Subtype.val_injective
  have hran : ∀ x : V, Con x ↔ ∃ w : W₀, (w : V) = x :=
    fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.2⟩
  have hmem : ∀ a b : W₀, a ∈ b ↔ (a : V) ∈ (b : V) := fun _ _ => Iff.rfl
  have hcF : Con F.1 := hX.con_mem F.2
  have hinF : ∀ Y, Y ∈ F.1 → Y ∈ X := fun Y hY => hX.tr F.1 F.2 Y hY
  obtain ⟨C₀, hC₀⟩ := ac_of_con (fun w : W₀ => (w : V)) hi hran hmem (⟨F.1, hcF⟩ : W₀)
    (fun Y hY => by
      obtain ⟨y, hy⟩ := hne ⟨Y.1, hinF Y.1 hY⟩ hY
      exact ⟨⟨y.1, hX.con_mem y.2⟩, hy⟩)
    (fun Y hY Z hZ ⟨x, hxY, hxZ⟩ => by
      have hxX : x.1 ∈ X := hX.tr Y.1 (hinF Y.1 hY) x.1 hxY
      have e := hdis ⟨Y.1, hinF Y.1 hY⟩ hY ⟨Z.1, hinF Z.1 hZ⟩ hZ ⟨⟨x.1, hxX⟩, hxY, hxZ⟩
      have e' : (Y : V) = (Z : V) := congrArg (fun w : extSet X => (w : V)) e
      exact Subtype.ext e')
  obtain ⟨μ, f, hFμ, lμ⟩ := hX.full F.1 F.2
  let C : V := sepB (k := 2) choRB (Lev μ) ![C₀.1, F.1]
  have hC : ∀ c, c ∈ C ↔ c ∈ Lev μ ∧ ChoR c C₀.1 F.1 :=
    fun c => mem_sepB choRB (Lev μ) ![C₀.1, F.1] c
  have hCc : Con C := con_sepB choRB (con_lev f.lim.1) ![C₀.1, F.1] (fun i => by
    fin_cases i
    · exact C₀.2
    · exact hcF)
  have hCX : C ∈ X := hX.sub lμ hCc fun z hz => ((hC z).mp hz).1
  refine ⟨⟨C, hCX⟩, fun Y hY => ?_⟩
  obtain ⟨x₀, ⟨hx₀C, hx₀Y⟩, huniq⟩ := hC₀ ⟨Y.1, hX.con_mem Y.2⟩ hY
  have hx₀X : x₀.1 ∈ X := hX.tr Y.1 Y.2 x₀.1 hx₀Y
  have hx₀μ : x₀.1 ∈ Lev μ :=
    lev_tr f.lim.1 Y.1 (lev_tr f.lim.1 F.1 hFμ Y.1 hY) x₀.1 hx₀Y
  refine ⟨⟨x₀.1, hx₀X⟩, ⟨(hC x₀.1).mpr ⟨hx₀μ, hx₀C, Y.1, hY, hx₀Y⟩, hx₀Y⟩, ?_⟩
  rintro x' ⟨hx'C, hx'Y⟩
  obtain ⟨-, hx'C₀, -⟩ := (hC x'.1).mp hx'C
  have e := huniq ⟨x'.1, hX.con_mem x'.2⟩ ⟨hx'C₀, hx'Y⟩
  have e' : (x' : V) = (x₀ : V) := congrArg (fun w : W₀ => (w : V)) e
  exact Subtype.ext e'

/-- **The structure of the members of `X` is a model of `𝗭𝗖`.** -/
theorem limFull_models_zc {X : V} (hX : LimFull X) [Nonempty (extSet X)] :
    (extSet X)↓[ℒₛₑₜ] ⊧* 𝗭𝗖 := by
  have hB := isMacBase_limFull hX
  have hZ : (extSet X)↓[ℒₛₑₜ] ⊧* 𝗭 := models_zermelo_of_base hB (fullsep_limFull hX)
  have hA : (extSet X)↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := ac_models' (ac_limFull hX)
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · exact models_theory_iff.mp hZ φ hφ
  · exact models_theory_iff.mp hA φ hφ

/-! ### The rank axioms -/

/-- **The rank axioms up to `N` hold in the structure of the members of `X`**, given a chain
of heights `e 0, …, e (N + 1)` and, as a member of `X`, a sequence of levels at full heights
on the ordinals up to `e (N + 1)`. -/
theorem hasRank_limFull {X : V} (hX : LimFull X) {N : ℕ} {e : ℕ → V} {Sq' : V}
    (hfull : ∀ j, j ≤ N + 1 → Full (e j)) (hnext : NextH (e N) (e (N + 1)))
    (hstep : ∀ j, j ≤ N → e j ∈ e (j + 1))
    (hθX : e (N + 1) ∈ X) (hSqX : Sq' ∈ X)
    (hSqtot : ∀ α, α ∈ sc (e (N + 1)) → ∃ μ, Full μ ∧ Pr Sq' α (Lev μ))
    (hSqfn : ∀ α S S', Pr Sq' α S → Pr Sq' α S' → S = S')
    (hSqmono : ∀ α β A B, α ∈ β → β ∈ sc (e (N + 1)) → Pr Sq' α A → Pr Sq' β B → A ∈ B)
    (hSqlev : ∀ α S, Pr Sq' α S → ∃ μ, Full μ ∧ S = Lev μ) :
    ∀ j, j ≤ N → HasRank j (extSet X) := by
  intro j hj
  have : Nonempty (extSet X) := limFull_nonempty hX
  have hM : (extSet X)↓[ℒₛₑₜ] ⊧* 𝗠 := (isMacBase_limFull hX).models
  have hθF : Full (e (N + 1)) := hfull (N + 1) le_rfl
  have hθO : Ord (e (N + 1)) := hθF.lim.1
  let ρ' : extSet X := ⟨e (N + 1), hθX⟩
  let S'' : extSet X := ⟨Sq', hSqX⟩
  have hOρ : Ord ρ' := (bdef_tr ordB hX.tr ![ρ']).mpr hθO
  have hprX : ∀ {f a b : V}, f ∈ X → Pr f a b → a ∈ X ∧ b ∈ X := by
    rintro f a b hf ⟨p, hp, hop⟩
    obtain ⟨d, hd, hdab⟩ := hop.2.1
    have hdX : d ∈ X := hX.tr p (hX.tr f hf p hp) d hd
    exact ⟨hX.tr d hdX a hdab.1, hX.tr d hdX b hdab.2.1⟩
  have hPS : ∀ a b : extSet X, Pr S'' a b ↔ Pr Sq' a.1 b.1 :=
    fun a b => bdef_tr prB hX.tr ![S'', a, b]
  have hsc : ∀ α : extSet X, α ∈ sc ρ' → α.1 ∈ sc (e (N + 1)) := by
    intro α hα
    rcases mem_sc.mp hα with h | h
    · exact mem_sc.mpr (Or.inl (congrArg Subtype.val h))
    · exact mem_sc.mpr (Or.inr h)
  have hom_ext : ∀ z : extSet X, z ∈ (om : extSet X) ↔ z.1 ∈ (om : V) := fun z =>
    numR_iff_m.symm.trans ((bdef_tr numB hX.tr ![z]).trans numR_iff_m)
  -- the hierarchy, made in the structure
  obtain ⟨h, H⟩ := exists_powH (V := extSet X) (ρ := ρ') (Sq := S'') hOρ
    (fun α hα => by
      obtain ⟨μ, -, hp⟩ := hSqtot α.1 (hsc α hα)
      exact ⟨⟨Lev μ, (hprX hSqX hp).2⟩, (hPS _ _).mpr hp⟩)
    (fun α S S' h1 h2 =>
      Subtype.ext (hSqfn α.1 S.1 S'.1 ((hPS _ _).mp h1) ((hPS _ _).mp h2)))
    (fun α S _ hp n hn => by
      obtain ⟨μ, hμ, e'⟩ := hSqlev α.1 S.1 ((hPS _ _).mp hp)
      have hn' : n.1 ∈ (om : V) := (hom_ext n).mp hn
      have h2 : n.1 ∈ Lev μ := ord_mem_lev_lim hμ.lim n.1 (hμ.lim.1.1 om hμ.omega n.1 hn')
      rw [← e'] at h2
      exact h2)
    (fun α β S S' hαβ hβ h1 h2 => by
      have hAB : S.1 ∈ S'.1 :=
        hSqmono α.1 β.1 S.1 S'.1 hαβ (hsc β hβ) ((hPS _ _).mp h1) ((hPS _ _).mp h2)
      obtain ⟨μ', hμ', e'⟩ := hSqlev β.1 S'.1 ((hPS _ _).mp h2)
      refine ⟨fun z hz => ?_, fun x hx => ?_⟩
      · have h3 : z.1 ∈ Lev μ' := lev_tr hμ'.lim.1 S.1 (e' ▸ hAB) z.1 hz
        rw [← e'] at h3
        exact h3
      · have h3 : x.1 ∈ Lev μ' := hμ'.sub S.1 x.1 (e' ▸ hAB) (hX.con_mem x.2)
          fun z hz => hx ⟨z, hX.tr x.1 x.2 z hz⟩ hz
        rw [← e'] at h3
        exact h3)
  -- the levels of the chain increase
  have hmonoe : ∀ k, k ≤ N + 1 → ∀ i, i ≤ k → ∀ x, x ∈ Lev (e i) → x ∈ Lev (e k) := by
    intro k
    induction k with
    | zero =>
      intro _ i hi x hx
      have e0 : i = 0 := by omega
      rw [e0] at hx
      exact hx
    | succ k ih =>
      intro hk i hi x hx
      rcases Nat.lt_or_ge i (k + 1) with h1 | h1
      · exact lev_mono (hfull (k + 1) hk).lim.1 (hstep k (by omega)) x
          (ih (by omega) i (by omega) x hx)
      · have e0 : i = k + 1 := by omega
        rw [e0] at hx
        exact hx
  -- the value at the numeral `i` is a member of the level at `e i`
  have hpw : ∀ i, i ≤ N → ((pw i : extSet X) : V) ∈ Lev (e i) := by
    intro i
    induction i with
    | zero =>
      intro _
      have e0 : ((om : extSet X) : V) = (om : V) := mem_ext fun z =>
        ⟨fun hz => (hom_ext ⟨z, hX.tr _ (om : extSet X).2 z hz⟩).mp hz,
          fun hz => (hom_ext ⟨z, hX.tr _ hX.om z hz⟩).mpr hz⟩
      have h1 : (om : V) ∈ Lev (e 0) :=
        ord_mem_lev_lim (hfull 0 (by omega)).lim om (hfull 0 (by omega)).omega
      rw [← e0] at h1
      exact h1
    | succ i ih =>
      intro hi
      have h1 : ((pw i : extSet X) : V) ∈ Lev (e i) := ih (by omega)
      have hFi : Full (e i) := hfull i (by omega)
      have hFi' : Full (e (i + 1)) := hfull (i + 1) (by omega)
      have hsub : ∀ z, z ∈ ((pw (i + 1) : extSet X) : V) → z ∈ Lev (e i) := by
        intro z hz
        have hzX : z ∈ X := hX.tr _ (pw (i + 1) : extSet X).2 z hz
        have hz' : (⟨z, hzX⟩ : extSet X) ∈ ℘ (pw i : extSet X) := hz
        have hz'' := mem_power_iff.mp hz'
        exact hFi.sub _ z h1 (hX.con_mem hzX) fun w hw => hz'' ⟨w, hX.tr z hzX w hw⟩ hw
      exact hFi'.sub (Lev (e i)) _ (lev_mem hFi'.lim.1 (hstep i (by omega)))
        (hX.con_mem (pw (i + 1) : extSet X).2) hsub
  have hnm : (nm j : extSet X) ∈ ρ' := by
    have h1 : ((nm j : extSet X) : V) ∈ (om : V) := (hom_ext _).mp (nm_mem_om j)
    exact hθO.1 om hθF.omega _ h1
  refine ⟨h, ρ', hOρ, (powH_iff hOρ).mpr H, nm j, isNum_nm j, hnm, pw j,
    powH_num H j (mem_sc.mpr (Or.inr hnm)), ?_⟩
  rintro ⟨f, hf1, hf2⟩
  have hFN : Full (e N) := hfull N (by omega)
  have hpwN : ∀ z, z ∈ ((pw j : extSet X) : V) → z ∈ Lev (e N) := fun z hz =>
    lev_tr hFN.lim.1 _ (hmonoe N (by omega) j hj _ (hpw j hj)) z hz
  apply not_linj_nextH hFN.lim hFN.omega hnext
  refine ⟨f.1, hX.con_mem f.2, fun u hu => ?_, fun u u' v hu hu' h1 h2 => ?_⟩
  · let u₁ : extSet X := ⟨u, hX.tr _ hθX u hu⟩
    obtain ⟨v, hv, hrl⟩ := hf1 u₁ hu
    have q1 : Pr f u₁ v := pr_iff.mpr (hin_rl_iff'.mp hrl)
    have p1 : Pr f.1 u v.1 := (bdef_tr prB hX.tr ![f, u₁, v]).mp q1
    exact ⟨v.1, hpwN v.1 hv, hin_rl_iff.mpr (pr_iff.mp p1)⟩
  · have p1 : Pr f.1 u v := pr_iff.mpr (hin_rl_iff.mp h1)
    have p2 : Pr f.1 u' v := pr_iff.mpr (hin_rl_iff.mp h2)
    let u₁ : extSet X := ⟨u, hX.tr _ hθX u hu⟩
    let u₂ : extSet X := ⟨u', hX.tr _ hθX u' hu'⟩
    let v₁ : extSet X := ⟨v, (hprX f.2 p1).2⟩
    have q1 : Pr f u₁ v₁ := (bdef_tr prB hX.tr ![f, u₁, v₁]).mpr p1
    have q2 : Pr f u₂ v₁ := (bdef_tr prB hX.tr ![f, u₂, v₁]).mpr p2
    have e' : u₁ = u₂ := hf2 u₁ u₂ v₁ hu hu' (hin_rl_iff'.mpr (pr_iff.mp q1))
      (hin_rl_iff'.mpr (pr_iff.mp q2))
    exact congrArg Subtype.val e'

/-! ### Such a set exists -/

/-- **From the rank axiom for `4 (N + 3) + 15`: a set whose members form a model of `𝗭𝗖` with
the rank axioms up to `N`.** -/
theorem exists_zc_ranks (N : ℕ) (hR : HasRank (4 * (N + 3) + 15) V) :
    ∃ X : V, LimFull X ∧ ∀ j, j ≤ N → HasRank j (extSet X) := by
  obtain ⟨ρ, Sq, sup⟩ := supply_of_rank (N + 3) hR
  obtain ⟨e, hfull, hnext, hv⟩ := supply_chain sup
  let lam : V := e (N + 2)
  have hlam : Lim lam := (hfull (N + 2) (by omega)).lim
  have htopl : Lim (e (N + 3)) := (hfull (N + 3) le_rfl).lim
  have hlamtop : lam ∈ e (N + 3) := (hnext (N + 2) (by omega)).2.1
  have hρ : ∀ ξ, ξ ∈ e (N + 3) → ξ ∈ ρ := fun ξ hξ => sup.hart ξ (ord_mem htopl.1 hξ)
    (vinj_dom_mono hv fun z hz => ord_mem_lev_lim htopl z (htopl.1.1 ξ hξ z hz))
  have hlamρ : lam ∈ ρ := hρ lam hlamtop
  have hin : ∀ γ, γ ∈ lam → γ ∈ ρ := fun γ hγ => hρ γ (htopl.1.1 lam hlamtop γ hγ)
  obtain ⟨U, hU⟩ := sup.tot lam hlamρ
  have lad : Ladder lam Sq U lam :=
    { tot := fun γ hγ => sup.tot γ (hin γ hγ)
      base := fun γ S hγ hS => sup.sbase γ S (hin γ hγ) hS
      sub := fun γ S hγ hS => (sup.mono γ lam S U hγ hlamρ hS hU).1
      top := fun γ S hγ hS => (sup.mono γ lam S U hγ hlamρ hS hU).2
      far := fun γ γ' S S' hγγ' hγ' hS hS' => (sup.mono γ γ' S S' hγγ' (hin γ' hγ') hS hS').2
      low := fun γ S hγ hS => vinj_mono (vinj_dom_mono hv (lev_mono htopl.1 hlamtop))
        (sup.low γ S (hin γ hγ) hS)
      baseU := sup.sbase lam U hlamρ hU }
  obtain ⟨K, Lam, hK, hLamc, -, hLamf, hLammono, -, -⟩ := exists_ladder' hlam.1 hlam.1 lad
  -- the union of the levels of the ladder
  let X : V := sepB (k := 2) inLadB (Lev K) ![lam, Lam]
  have hXm : ∀ x, x ∈ X ↔ ∃ α A, α ∈ lam ∧ (Pr Lam α A ∧ x ∈ A) := by
    intro x
    have h0 : x ∈ X ↔ x ∈ Lev K ∧ InLad x lam Lam := mem_sepB inLadB (Lev K) ![lam, Lam] x
    rw [h0, inLad_iff]
    refine ⟨fun k => k.2, fun k => ⟨?_, k⟩⟩
    obtain ⟨α, A, hα, hp, hxA⟩ := k
    obtain ⟨μ, hμK, -, -, hA⟩ := hLamf α hα
    rw [(hA A).mp hp] at hxA
    exact lev_mono hK.lim.1 hμK x hxA
  have hlevX : ∀ α μ, α ∈ lam → Pr Lam α (Lev μ) → Lev μ ∈ X := by
    intro α μ hα hp
    have hs : sc α ∈ lam := hlam.2.2 α hα
    obtain ⟨μ', -, -, -, hA'⟩ := hLamf (sc α) hs
    have hp' : Pr Lam (sc α) (Lev μ') := (hA' _).mpr rfl
    exact (hXm _).mpr ⟨sc α, Lev μ', hs, hp', hLammono α (sc α) _ _ (self_mem_sc α) hs hp hp'⟩
  have h0lam : (∅ : V) ∈ lam := (lim_big hlam).2 ∅ empty_mem_om
  have hXL : LimFull X :=
    { con := con_sepB inLadB (con_lev hK.lim.1) ![lam, Lam] (fun i => by
        fin_cases i
        · exact con_ord hlam.1
        · exact hLamc)
      tr := fun x hx z hz => by
        obtain ⟨α, A, hα, hp, hxA⟩ := (hXm x).mp hx
        obtain ⟨μ, -, hμF, -, hA⟩ := hLamf α hα
        have e' := (hA A).mp hp
        have hzA : z ∈ A := by
          rw [e'] at hxA ⊢
          exact lev_tr hμF.lim.1 x hxA z hz
        exact (hXm z).mpr ⟨α, A, hα, hp, hzA⟩
      om := by
        obtain ⟨μ, -, hμF, -, hA⟩ := hLamf ∅ h0lam
        exact (hXm _).mpr ⟨∅, Lev μ, h0lam, (hA _).mpr rfl,
          ord_mem_lev_lim hμF.lim om hμF.omega⟩
      full := fun x hx => by
        obtain ⟨α, A, hα, hp, hxA⟩ := (hXm x).mp hx
        obtain ⟨μ, -, hμF, -, hA⟩ := hLamf α hα
        have e' := (hA A).mp hp
        rw [e'] at hxA hp
        exact ⟨μ, hμF, hxA, hlevX α μ hα hp⟩ }
  -- the sequence of the levels on the ordinals up to `e (N + 1)`
  have hθF : Full (e (N + 1)) := hfull (N + 1) (by omega)
  have hθO : Ord (e (N + 1)) := hθF.lim.1
  have hθlam : e (N + 1) ∈ lam := (hnext (N + 1) (by omega)).2.1
  have hs1 : sc (e (N + 1)) ∈ lam := hlam.2.2 _ hθlam
  have hs2 : sc (sc (e (N + 1))) ∈ lam := hlam.2.2 _ hs1
  have hsclam : ∀ α, α ∈ sc (e (N + 1)) → α ∈ lam := fun α hα => hlam.1.1 _ hs1 α hα
  let Sq' : V := sepB (k := 1) fstInB Lam ![sc (e (N + 1))]
  have hSq' : ∀ q, q ∈ Sq' ↔ q ∈ Lam ∧ FstIn q (sc (e (N + 1))) :=
    fun q => mem_sepB fstInB Lam ![sc (e (N + 1))] q
  have hPSq : ∀ α A, Pr Sq' α A ↔ α ∈ sc (e (N + 1)) ∧ Pr Lam α A := by
    intro α A
    constructor
    · rintro ⟨q, hq, hop⟩
      obtain ⟨hqL, hf⟩ := (hSq' q).mp hq
      obtain ⟨α', A', hα', hop'⟩ := fstIn_iff.mp hf
      obtain ⟨e1, -⟩ := op_inj hop hop'
      rw [← e1] at hα'
      exact ⟨hα', q, hqL, hop⟩
    · rintro ⟨hα, q, hq, hop⟩
      exact ⟨q, (hSq' q).mpr ⟨hq, fstIn_iff.mpr ⟨α, A, hα, hop⟩⟩, hop⟩
  obtain ⟨μ₁, -, hμ₁F, hlamμ₁, hA₁⟩ := hLamf (sc (e (N + 1))) hs1
  obtain ⟨μ₂, -, hμ₂F, -, hA₂⟩ := hLamf (sc (sc (e (N + 1)))) hs2
  have hp₁ : Pr Lam (sc (e (N + 1))) (Lev μ₁) := (hA₁ _).mpr rfl
  have hp₂ : Pr Lam (sc (sc (e (N + 1)))) (Lev μ₂) := (hA₂ _).mpr rfl
  have h12 : Lev μ₁ ∈ Lev μ₂ := hLammono _ _ _ _ (self_mem_sc _) hs2 hp₁ hp₂
  have hSqc : Con Sq' := con_sepB fstInB hLamc ![sc (e (N + 1))] (fun i => by
    have e' := Fin.eq_zero i
    subst e'
    exact con_ord (ord_sc hθO))
  have hordμ₁ : ∀ α, α ∈ lam → α ∈ Lev μ₁ := fun α hα =>
    ord_mem_lev_lim hμ₁F.lim α (hμ₁F.lim.1.1 lam hlamμ₁ α hα)
  have hSqsub : ∀ q, q ∈ Sq' → q ∈ Lev μ₁ := by
    intro q hq
    obtain ⟨hqL, hf⟩ := (hSq' q).mp hq
    obtain ⟨α, A, hα, hop⟩ := fstIn_iff.mp hf
    have hAμ : A ∈ Lev μ₁ := hLammono α _ A (Lev μ₁) hα hs1 ⟨q, hqL, hop⟩ hp₁
    rw [isOp_iff.mp hop]
    exact kp_mem_lev_lim hμ₁F.lim hμ₁F.omega (hordμ₁ α (hsclam α hα)) hAμ
  have hl₂X : Lev μ₂ ∈ X := hlevX _ μ₂ hs2 hp₂
  have hl₁X : Lev μ₁ ∈ X := hlevX _ μ₁ hs1 hp₁
  have hSqX : Sq' ∈ X := hXL.tr _ hl₂X Sq' (hμ₂F.sub _ Sq' h12 hSqc hSqsub)
  have hθX : e (N + 1) ∈ X := hXL.tr _ hl₁X _ (hordμ₁ _ hθlam)
  refine ⟨X, hXL, hasRank_limFull hXL (e := e) (Sq' := Sq')
    (fun j hj => hfull j (by omega)) (hnext N (by omega))
    (fun j hj => (hnext j (by omega)).2.1) hθX hSqX ?_ ?_ ?_ ?_⟩
  · intro α hα
    obtain ⟨μ, -, hμF, -, hA⟩ := hLamf α (hsclam α hα)
    exact ⟨μ, hμF, (hPSq _ _).mpr ⟨hα, (hA _).mpr rfl⟩⟩
  · intro α S S' h1 h2
    obtain ⟨hα, k1⟩ := (hPSq _ _).mp h1
    obtain ⟨-, k2⟩ := (hPSq _ _).mp h2
    obtain ⟨μ, -, -, -, hA⟩ := hLamf α (hsclam α hα)
    rw [(hA S).mp k1, (hA S').mp k2]
  · intro α β A B hαβ hβ h1 h2
    exact hLammono α β A B hαβ (hsclam β hβ) ((hPSq _ _).mp h1).2 ((hPSq _ _).mp h2).2
  · intro α S h1
    obtain ⟨hα, k1⟩ := (hPSq _ _).mp h1
    obtain ⟨μ, -, hμF, -, hA⟩ := hLamf α (hsclam α hα)
    exact ⟨μ, hμF, (hA S).mp k1⟩

end model

end MH

/-! ### The consistency statement -/

/-- If `𝗠𝗛` with the rank axioms is consistent, so is `𝗭𝗖` with the rank axioms up to `N`. -/
theorem consistent_zc_upto_of_consistent_mhr (h : Entailment.Consistent 𝗠𝗛𝗥) (N : ℕ) :
    Entailment.Consistent (𝗭𝗖 ∪ {φ | ∃ j, j ≤ N ∧ φ = Axiom.rank j}) := by
  by_contra hU
  refine Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable ?_) h
  apply SetTheory.complete.{0}
  intro M _ _ hTR
  exfalso
  apply hU
  have hMH : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := mhr_models_mh
  obtain ⟨X, hX, hr⟩ := MH.exists_zc_ranks (V := M) N (mhr_rank _)
  have : Nonempty (extSet X) := MH.limFull_nonempty hX
  have hZC : (extSet X)↓[ℒₛₑₜ] ⊧* 𝗭𝗖 := MH.limFull_models_zc hX
  have : (extSet X)↓[ℒₛₑₜ] ⊧* (𝗭𝗖 ∪ {φ | ∃ j, j ≤ N ∧ φ = Axiom.rank j}) :=
    models_theory_iff.mpr fun φ hφ => by
      rcases hφ with hφ | ⟨j, hj, rfl⟩
      · exact models_theory_iff.mp hZC φ hφ
      · exact models_rank_iff.mpr (hr j hj)
  exact consistent_of_model _ (extSet X)

/-- **If `𝗠𝗛` with the rank axioms is consistent, so is Zermelo set theory with Choice and
the rank axioms.** -/
theorem consistent_zcr_of_consistent_mhr (h : Entailment.Consistent 𝗠𝗛𝗥) :
    Entailment.Consistent 𝗭𝗖𝗥 :=
  consistent_ranks_of_forall 𝗭𝗖 fun N => consistent_zc_upto_of_consistent_mhr h N

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.limFull_models_zc
#print axioms FFL.FirstOrder.SetTheory.MH.hasRank_limFull
#print axioms FFL.FirstOrder.SetTheory.MH.exists_zc_ranks
#print axioms FFL.FirstOrder.SetTheory.consistent_zcr_of_consistent_mhr
