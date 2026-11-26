module

public import MHArith
public import MHCountSound

@[expose] public section

set_option autoImplicit false

/-!
# The rank axioms over `𝗠𝗛`

For each natural number `n` of the metatheory, the sentence `Axiom.rank n` says:

> there are an ordinal `θ` and a set `h` such that `h` is the hierarchy of the iterated power
> sets of `ω` on the ordinals up to `θ`, and `θ` does not map one-to-one into the `n`-th
> iterated power set of `ω`.

Here `h` is a set of pairs with `h(0) = ω`, `h(α + 1) = ℘(h(α))` for `α < θ`, and
`h(λ) = ⋃_{α < λ} h(α)` for limit `λ ≤ θ` (`PowH`). With Choice, `ω ∪ ⋃_{α ≤ θ} h(α)` is the
rank `V_{ω + θ}`, and the size condition says `θ ≥ ℶₙ⁺`.

`𝗠𝗛𝗥` is `𝗠𝗛` with these sentences for all `n`.

This file has the definitions, and what follows from the hierarchy inside a model of `𝗠𝗛`:

* `pw k`: the `k`-th iterated power set of `ω`. `pw_supRel`, `pw_base`.
* `IsPowH`: the hierarchy, stated with the operations of the model; `powH_iff`.
* `ord_ind`: induction on the members of an ordinal for a property with a bounded definition.
* `powH_tmon`: the values are transitive and increasing. `powH_num`: the value at the numeral
  `k` is `pw k`.
* `exists_powH`: the hierarchy exists on the ordinals up to `ρ` when there is a sequence of
  sets on those ordinals, each including `ω`, with every subset of an earlier one a member of
  each later one. The recursion is `ord_rec`, with the values cut down to the given sets.
* `hasRank_of_levels`: so the rank axiom for `n` holds if such a sequence exists on the least
  ordinal that does not map one-to-one into `pw n`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace UDef

variable {k : ℕ} {R : URel k}

/-- A bounded definition, as a definition. -/
def ofB (d : BDef R) : UDef R := ⟨d.φ, d.eval⟩

end UDef

namespace MH

/-! ### The notions -/

section defs

variable {V : Type} [SetStructure V]

/-- `β` has a member, and the successor of every member of `β` is a member of `β`. -/
def LimR (β : V) : Prop := (∃ z, z ∈ β) ∧ ∀ α, α ∈ β → ∃ α', α' ∈ β ∧ SuccR α' α

/-- **`h` is the hierarchy of the iterated power sets of `ω` on the ordinals up to `θ`.** -/
def PowH (h θ : V) : Prop :=
  (∀ α x x' : V, Pr h α x → Pr h α x' → x = x') ∧
  ((∀ α : V, (α ∈ θ ∨ α = θ) → ∃ x, Pr h α x) ∧
  ((∀ α x : V, Pr h α x → (∀ z, ¬ z ∈ α) → ∀ z, (z ∈ x ↔ NumR z)) ∧
  ((∀ α β x y : V, α ∈ θ → SuccR β α → Pr h α x → Pr h β y →
      ∀ z, (z ∈ y ↔ ∀ w, w ∈ z → w ∈ x)) ∧
  (∀ β y : V, (β ∈ θ ∨ β = θ) → LimR β → Pr h β y →
      ∀ z, (z ∈ y ↔ ∃ α, α ∈ β ∧ ∃ x, Pr h α x ∧ z ∈ x)))))

/-- `θ` is an ordinal, `h` is the hierarchy on the ordinals up to `θ`, and `θ` does not map
one-to-one into the value of `h` at the numeral `n`. -/
def RankAt (n : ℕ) (θ h : V) : Prop :=
  Ord θ ∧ (PowH h θ ∧ ∃ k, IsNum n k ∧ (k ∈ θ ∧ ∃ w, Pr h k w ∧ ¬∃ f, InjS f θ w))

end defs

/-- **The rank axiom for `n`** in a structure. -/
def HasRank (n : ℕ) (V : Type) [SetStructure V] : Prop := ∃ h θ : V, RankAt n θ h

/-! ### The formulas -/

def limRU : UDef (k := 1) (fun V _ v ↦ LimR (v 0)) :=
  ((UDef.ex (UDef.mem 0 1)).and (UDef.all ((UDef.mem 0 1).imp
    (UDef.ex ((UDef.mem 0 2).and ((UDef.ofB succB).comp ![0, 1])))))).congr
    fun _ _ _ => Iff.rfl

def powH1U : UDef (k := 2)
    (fun V _ v ↦ ∀ α x x' : V, Pr (v 0) α x → Pr (v 0) α x' → x = x') :=
  (UDef.all (UDef.all (UDef.all (((UDef.ofB prB).comp ![3, 2, 1]).imp
    (((UDef.ofB prB).comp ![3, 2, 0]).imp (UDef.eq 1 0)))))).congr fun _ _ _ => Iff.rfl

def powH2U : UDef (k := 2)
    (fun V _ v ↦ ∀ α : V, (α ∈ v 1 ∨ α = v 1) → ∃ x, Pr (v 0) α x) :=
  (UDef.all (((UDef.mem 0 2).or (UDef.eq 0 2)).imp
    (UDef.ex ((UDef.ofB prB).comp ![2, 1, 0])))).congr fun _ _ _ => Iff.rfl

def powH3U : UDef (k := 2)
    (fun V _ v ↦ ∀ α x : V, Pr (v 0) α x → (∀ z, ¬ z ∈ α) → ∀ z, (z ∈ x ↔ NumR z)) :=
  (UDef.all (UDef.all (((UDef.ofB prB).comp ![2, 1, 0]).imp
    ((UDef.all (UDef.mem 0 2).not).imp
      (UDef.all ((UDef.mem 0 1).iff ((UDef.ofB numB).comp ![0]))))))).congr
    fun _ _ _ => Iff.rfl

def powH4U : UDef (k := 2)
    (fun V _ v ↦ ∀ α β x y : V, α ∈ v 1 → SuccR β α → Pr (v 0) α x → Pr (v 0) β y →
      ∀ z, (z ∈ y ↔ ∀ w, w ∈ z → w ∈ x)) :=
  (UDef.all (UDef.all (UDef.all (UDef.all ((UDef.mem 3 5).imp
    (((UDef.ofB succB).comp ![2, 3]).imp (((UDef.ofB prB).comp ![4, 3, 1]).imp
      (((UDef.ofB prB).comp ![4, 2, 0]).imp
        (UDef.all ((UDef.mem 0 1).iff
          (UDef.all ((UDef.mem 0 1).imp (UDef.mem 0 3))))))))))))).congr
    fun _ _ _ => Iff.rfl

def powH5U : UDef (k := 2)
    (fun V _ v ↦ ∀ β y : V, (β ∈ v 1 ∨ β = v 1) → LimR β → Pr (v 0) β y →
      ∀ z, (z ∈ y ↔ ∃ α, α ∈ β ∧ ∃ x, Pr (v 0) α x ∧ z ∈ x)) :=
  (UDef.all (UDef.all (((UDef.mem 1 3).or (UDef.eq 1 3)).imp
    ((limRU.comp ![1]).imp (((UDef.ofB prB).comp ![2, 1, 0]).imp
      (UDef.all ((UDef.mem 0 1).iff (UDef.ex ((UDef.mem 0 3).and
        (UDef.ex (((UDef.ofB prB).comp ![5, 1, 0]).and (UDef.mem 2 0)))))))))))).congr
    fun _ _ _ => Iff.rfl

def powHU : UDef (k := 2) (fun V _ v ↦ PowH (v 0) (v 1)) :=
  (powH1U.and (powH2U.and (powH3U.and (powH4U.and powH5U)))).congr fun _ _ _ => Iff.rfl

def rankAtU (n : ℕ) : UDef (k := 2) (fun V _ v ↦ RankAt n (v 0) (v 1)) :=
  (((UDef.ofB ordB).comp ![0]).and ((powHU.comp ![1, 0]).and
    (UDef.ex (((UDef.ofB (isNumB n)).comp ![0]).and ((UDef.mem 0 1).and
      (UDef.ex (((UDef.ofB prB).comp ![3, 1, 0]).and
        (UDef.ex (injSU.comp ![0, 3, 1])).not))))))).congr fun _ _ _ => Iff.rfl

end MH

namespace Axiom

/-- **The rank axiom for `n`**: the iterated power sets of `ω` exist along an ordinal that does
not map one-to-one into the `n`-th of them. -/
def rank (n : ℕ) : SetTheorySentence := (UDef.ex (UDef.ex (MH.rankAtU n))).φ

end Axiom

/-- **The sentence means the property.** -/
lemma models_rank_iff {n : ℕ} {N : Type} [Nonempty N] [SetStructure N] :
    N↓[ℒₛₑₜ] ⊧ Axiom.rank n ↔ MH.HasRank n N :=
  (UDef.ex (UDef.ex (MH.rankAtU n))).eval N ![]

/-- `𝗠𝗛` with the rank axioms for every `n`. -/
abbrev MathiasMHRanks : SetTheory := 𝗠𝗛 ∪ Set.range Axiom.rank

@[inherit_doc] notation "𝗠𝗛𝗥" => MathiasMHRanks

instance : 𝗘𝗤 _ ⪯ 𝗠𝗛𝗥 :=
  let : 𝗘𝗤 _ ⪯ 𝗠𝗛 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

section

variable {M : Type} [SetStructure M] [Nonempty M] [hTR : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗥]

theorem mhr_models_mh : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 :=
  models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hTR φ (Or.inl hφ)

theorem mhr_rank (n : ℕ) : MH.HasRank n M :=
  models_rank_iff.mp (models_theory_iff.mp hTR _ (Or.inr ⟨n, rfl⟩))

end

/-- A model of `𝗠𝗛` in which the rank axioms hold is a model of `𝗠𝗛𝗥`. -/
theorem models_mhr_of {W : Type} [SetStructure W] [Nonempty W] (hMH : W↓[ℒₛₑₜ] ⊧* 𝗠𝗛)
    (hr : ∀ n : ℕ, MH.HasRank n W) : W↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗥 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | ⟨n, rfl⟩
  · exact models_theory_iff.mp hMH φ hφ
  · exact models_rank_iff.mpr (hr n)

namespace MH

/-! ### In a model of `𝗠𝗛` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-! The three sections of this file that follow use only `𝗠`; the collapse axiom is used in the
sections marked `𝗠𝗛` (`pw_base` and `hasRank_of_levels`). -/

theorem zs_om_m {x : V} (hx : x ∈ (om : V)) : ZS x := by
  rcases om_cases hx with h | ⟨m, -, h⟩
  · exact Or.inl fun z hz => by
      rw [h] at hz
      exact absurd hz (by simp)
  · exact Or.inr ⟨m, by rw [h]; exact self_mem_sc m, succR_iff_sc.mpr h⟩

/-- The finite ordinals are the members of `ω`, in a model of `𝗠` (`numR_iff` of
`MHArith.lean` is stated for `𝗠𝗛`). -/
theorem numR_iff_m {x : V} : NumR x ↔ x ∈ (om : V) := by
  constructor
  · rintro ⟨hO, hz, hall⟩
    by_contra hx
    let Z : V := sepB (k := 1) (BDef.mem 0 1).not (sc x) ![(om : V)]
    have hZ : ∀ y, y ∈ Z ↔ y ∈ sc x ∧ ¬ y ∈ (om : V) := fun y => mem_sepB _ _ _ y
    obtain ⟨z, hzZ, hmin⟩ := ord_least Z (fun y hy => ord_mem (ord_sc hO) ((hZ y).mp hy).1)
      ⟨x, (hZ x).mpr ⟨self_mem_sc x, hx⟩⟩
    obtain ⟨hzs, hzo⟩ := (hZ z).mp hzZ
    have hzZS : ZS z := by
      rcases mem_sc.mp hzs with e | e
      · rw [e]
        exact hz
      · exact hall z e
    rcases hzZS with h | ⟨w, hw, hs⟩
    · apply hzo
      have : z = ∅ := mem_ext fun u => ⟨fun hu => (h u hu).elim, fun hu => absurd hu (by simp)⟩
      rw [this]
      exact empty_mem_om
    · have e : z = sc w := succR_iff_sc.mp hs
      have hws : w ∈ sc x := (ord_sc hO).1 z hzs w hw
      have hwo : w ∈ (om : V) := by
        by_contra hwn
        rcases hmin w ((hZ w).mpr ⟨hws, hwn⟩) with k | k
        · rw [k] at hw
          exact mem_irrefl _ hw
        · exact mem_asymm hw k
      apply hzo
      rw [e]
      exact sc_mem_om hwo
  · intro hx
    exact ⟨ord_mem ord_om hx, zs_om_m hx, fun y hy => zs_om_m (om_tr x hx y hy)⟩

/-- An ordinal is empty, a successor or a limit, in a model of `𝗠`. -/
theorem ord_cases_m {ξ : V} (h : Ord ξ) : ξ = ∅ ∨ (∃ η, η ∈ ξ ∧ ξ = sc η) ∨ Lim ξ := by
  by_cases h0 : ∃ z, z ∈ ξ
  · by_cases hs : ∃ η, η ∈ ξ ∧ ξ = sc η
    · exact Or.inr (Or.inl hs)
    · refine Or.inr (Or.inr ⟨h, h0, fun β hβ => ?_⟩)
      rcases ord_sc_le (ord_mem h hβ) h hβ with e | e
      · exact absurd ⟨β, hβ, e.symm⟩ hs
      · exact e
  · exact Or.inl (mem_ext fun z => ⟨fun hz => absurd ⟨z, hz⟩ h0, fun hz => absurd hz (by simp)⟩)


theorem limR_iff {β : V} (hβ : Ord β) : LimR β ↔ Lim β := by
  constructor
  · rintro ⟨hne, hs⟩
    refine ⟨hβ, hne, fun α hα => ?_⟩
    obtain ⟨α', hα', hsc⟩ := hs α hα
    rw [← succR_iff_sc.mp hsc]
    exact hα'
  · rintro ⟨-, hne, hs⟩
    exact ⟨hne, fun α hα => ⟨sc α, hs α hα, succR_iff_sc.mpr rfl⟩⟩

/-- **Induction on the members of an ordinal**, for a property with a bounded definition. -/
theorem ord_ind {k : ℕ} {R : MRel (k + 1)} (d : BDef R) (p : Fin k → V) {δ : V} (hδ : Ord δ)
    (step : ∀ β, β ∈ δ → (∀ α, α ∈ β → R V (α :> p)) → R V (β :> p)) :
    ∀ β, β ∈ δ → R V (β :> p) := by
  by_contra hcon
  let Z : V := sepB d.not δ p
  have hZ : ∀ z, z ∈ Z ↔ z ∈ δ ∧ ¬R V (z :> p) := fun z => mem_sepB _ _ _ z
  have hne : ∃ z, z ∈ Z := by
    by_contra h
    exact hcon fun β hβ => by
      by_contra hn
      exact h ⟨β, (hZ β).mpr ⟨hβ, hn⟩⟩
  obtain ⟨β, hβZ, hmin⟩ := ord_least Z (fun z hz => ord_mem hδ ((hZ z).mp hz).1) hne
  obtain ⟨hβ, hn⟩ := (hZ β).mp hβZ
  refine hn (step β hβ fun α hα => ?_)
  by_contra hna
  rcases hmin α ((hZ α).mpr ⟨hδ.1 β hβ α hα, hna⟩) with e | e
  · rw [e] at hα
    exact mem_irrefl α hα
  · exact mem_asymm e hα

/-! ### The iterated power sets of `ω` -/

/-- The `k`-th iterated power set of `ω`. -/
noncomputable def pw : ℕ → V
  | 0 => om
  | k + 1 => ℘ (pw k)

theorem pw_tr : ∀ k : ℕ, Tr (pw k : V)
  | 0 => om_tr
  | k + 1 => fun y hy z hz =>
    mem_power_iff.mpr fun w hw => pw_tr k z (mem_power_iff.mp hy z hz) w hw

theorem pw_succ_sub (k : ℕ) : ∀ z : V, z ∈ (pw k : V) → z ∈ (pw (k + 1) : V) :=
  fun z hz => mem_power_iff.mpr fun w hw => pw_tr k z hz w hw

theorem pw_mono {a b : ℕ} (h : a ≤ b) : ∀ z : V, z ∈ (pw a : V) → z ∈ (pw b : V) := by
  induction h with
  | refl => exact fun z hz => hz
  | step _ ih => exact fun z hz => pw_succ_sub _ z (ih z hz)

theorem om_sub_pw (k : ℕ) : ∀ z : V, z ∈ (om : V) → z ∈ (pw k : V) :=
  pw_mono (Nat.zero_le k)

/-! ### The hierarchy, with the operations of the model -/

/-- `h` is the hierarchy of the iterated power sets of `ω` on the ordinals up to `θ`. -/
structure IsPowH (h θ : V) : Prop where
  ord : Ord θ
  fn : ∀ α x x' : V, Pr h α x → Pr h α x' → x = x'
  tot : ∀ α : V, α ∈ sc θ → ∃ x, Pr h α x
  zero : Pr h ∅ (om : V)
  succ : ∀ α x : V, α ∈ θ → Pr h α x → Pr h (sc α) (℘ x)
  lim : ∀ β y : V, β ∈ sc θ → Lim β → Pr h β y →
    ∀ z, z ∈ y ↔ ∃ α, α ∈ β ∧ ∃ x, Pr h α x ∧ z ∈ x

theorem powH_iff {h θ : V} (hθ : Ord θ) : PowH h θ ↔ IsPowH h θ := by
  constructor
  · rintro ⟨fn, tot, zero, succ, lim⟩
    have tot' : ∀ α : V, α ∈ sc θ → ∃ x, Pr h α x := fun α hα => by
      rcases mem_sc.mp hα with e | e
      · exact tot α (Or.inr e)
      · exact tot α (Or.inl e)
    refine ⟨hθ, fn, tot', ?_, fun α x hα hx => ?_, fun β y hβ hl hy => ?_⟩
    · have h0 : (∅ : V) ∈ sc θ := by
        rcases ord_tri ord_empty hθ with e | e | e
        · exact mem_sc.mpr (Or.inr e)
        · exact mem_sc.mpr (Or.inl e)
        · exact absurd e (by simp)
      obtain ⟨x, hx⟩ := tot' ∅ h0
      have e : x = (om : V) := mem_ext fun z =>
        (zero ∅ x hx (fun z hz => absurd hz (by simp)) z).trans numR_iff_m
      rw [← e]
      exact hx
    · have hs : sc α ∈ sc θ := by
        rcases ord_sc_le (ord_mem hθ hα) hθ hα with e | e
        · exact mem_sc.mpr (Or.inl e)
        · exact mem_sc.mpr (Or.inr e)
      obtain ⟨y, hy⟩ := tot' (sc α) hs
      have e : y = ℘ x := mem_ext fun z =>
        ⟨fun hz => mem_power_iff.mpr ((succ α (sc α) x y hα (succR_iff_sc.mpr rfl) hx hy z).mp hz),
          fun hz => (succ α (sc α) x y hα (succR_iff_sc.mpr rfl) hx hy z).mpr
            (mem_power_iff.mp hz)⟩
      rw [← e]
      exact hy
    · have hβ' : β ∈ θ ∨ β = θ := (mem_sc.mp hβ).symm
      exact lim β y hβ' ((limR_iff hl.1).mpr hl) hy
  · intro H
    refine ⟨H.fn, fun α hα => H.tot α (mem_sc.mpr hα.symm), fun α x hx hα z => ?_,
      fun α β x y hα hs hx hy z => ?_, fun β y hβ hl hy => ?_⟩
    · have e : α = ∅ := mem_ext fun w => ⟨fun hw => absurd hw (hα w), fun hw => absurd hw (by simp)⟩
      rw [e] at hx
      rw [H.fn _ _ _ hx H.zero]
      exact numR_iff_m.symm
    · rw [succR_iff_sc.mp hs] at hy
      rw [H.fn _ _ _ hy (H.succ α x hα hx)]
      exact ⟨fun hz => mem_power_iff.mp hz, fun hz => mem_power_iff.mpr hz⟩
    · have hβs : β ∈ sc θ := mem_sc.mpr hβ.symm
      exact H.lim β y hβs ((limR_iff (ord_mem (ord_sc hθ) hβs)).mp hl) hy

/-- The value at `β` is transitive and includes the values at the members of `β`: bounded
form. -/
def TMon {V : Type} [SetStructure V] (β h : V) : Prop :=
  ∀ q, q ∈ h → ∀ u, u ∈ q → ∀ y, y ∈ u → (IsOp q β y → (Tr y ∧
    ∀ α, α ∈ β → ∀ q', q' ∈ h → ∀ u', u' ∈ q' → ∀ x, x ∈ u' → (IsOp q' α x →
      ∀ z, z ∈ x → z ∈ y)))

end model

/-! ### In a model of `𝗠𝗛` -/

section modelH

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem supRel_mono {S S' T T' : V} (h : SupRel S T) (hS : ∀ z, z ∈ S' → z ∈ S)
    (hT : ∀ z, z ∈ T → z ∈ T') : SupRel S' T' := fun C hC =>
  hT C (h C fun w hw p hp => by
    obtain ⟨a, ha, b, hb, e⟩ := mem_prodS.mp (hC w hw p hp)
    exact mem_prodS.mpr ⟨a, hS a ha, b, hS b hb, e⟩)

/-- Every set of relations on a set is a member of its fourth power set. -/
theorem supRel_pow4 (x : V) : SupRel x (℘ (℘ (℘ (℘ x)))) :=
  supRel_of_pow4 (L₁ := ℘ x) (L₂ := ℘ (℘ x)) (L₃ := ℘ (℘ (℘ x)))
    (fun _ hx => mem_power_iff.mpr hx) (fun _ hx => mem_power_iff.mpr hx)
    (fun _ hx => mem_power_iff.mpr hx) (fun _ hx => mem_power_iff.mpr hx)

theorem pw_supRel (k : ℕ) : SupRel (pw k : V) (pw (k + 4)) := supRel_pow4 (pw k)

theorem pw_base (k : ℕ) : BaseS (pw (k + 4) : V) :=
  baseS_of_sup (supRel_mono (pw_supRel k) (om_sub_pw k) fun _ hz => hz)

end modelH

def tMonB : BDef (k := 2) (fun V _ v ↦ TMon (v 0) (v 1)) :=
  (BDef.ball 1 (BDef.ball 0 (BDef.ball 0 ((isOpB.comp ![2, 3, 0]).imp ((trB.comp ![0]).and
    (BDef.ball 3 (BDef.ball 5 (BDef.ball 0 (BDef.ball 0 ((isOpB.comp ![2, 3, 0]).imp
      (BDef.ball 0 (BDef.mem 0 5)))))))))))).congr fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem tMon_iff {β h : V} : TMon β h ↔ ∀ y, Pr h β y → (Tr y ∧
    ∀ α, α ∈ β → ∀ x, Pr h α x → ∀ z, z ∈ x → z ∈ y) := by
  constructor
  · rintro H y ⟨q, hq, hop⟩
    obtain ⟨u, hu, hyu⟩ := pr_snd_mem hop
    obtain ⟨h1, h2⟩ := H q hq u hu y hyu hop
    refine ⟨h1, fun α hα x hx => ?_⟩
    obtain ⟨q', hq', hop'⟩ := hx
    obtain ⟨u', hu', hxu'⟩ := pr_snd_mem hop'
    exact h2 α hα q' hq' u' hu' x hxu' hop'
  · intro H q hq u _ y _ hop
    obtain ⟨h1, h2⟩ := H y ⟨q, hq, hop⟩
    exact ⟨h1, fun α hα q' hq' u' _ x _ hop' => h2 α hα x ⟨q', hq', hop'⟩⟩

/-- **The values of the hierarchy are transitive and increasing.** -/
theorem powH_tmon {h θ : V} (H : IsPowH h θ) : ∀ β, β ∈ sc θ → ∀ y, Pr h β y → (Tr y ∧
    ∀ α, α ∈ β → ∀ x, Pr h α x → ∀ z, z ∈ x → z ∈ y) := by
  have hsO : Ord (sc θ) := ord_sc H.ord
  have key := ord_ind tMonB ![h] hsO (fun β hβ ih => by
    show TMon β h
    have ih' : ∀ α, α ∈ β → ∀ y, Pr h α y → (Tr y ∧
        ∀ α', α' ∈ α → ∀ x, Pr h α' x → ∀ z, z ∈ x → z ∈ y) :=
      fun α hα => tMon_iff.mp (ih α hα)
    refine tMon_iff.mpr fun y hy => ?_
    rcases ord_cases_m (ord_mem hsO hβ) with e | ⟨η, hη, e⟩ | hl
    · subst e
      rw [H.fn _ _ _ hy H.zero]
      exact ⟨om_tr, fun α hα => absurd hα (by simp)⟩
    · have hηθ : η ∈ θ := by
        rcases mem_sc.mp hβ with e' | e'
        · rw [← e']
          exact hη
        · exact H.ord.1 β e' η hη
      obtain ⟨x, hx⟩ := H.tot η (mem_sc.mpr (Or.inr hηθ))
      obtain ⟨hxt, hxm⟩ := ih' η hη x hx
      rw [e] at hy
      rw [H.fn _ _ _ hy (H.succ η x hηθ hx)]
      have hsub : ∀ z, z ∈ x → z ∈ ℘ x := fun z hz => mem_power_iff.mpr fun w hw => hxt z hz w hw
      refine ⟨fun z hz w hw => hsub w (mem_power_iff.mp hz w hw), fun α hα x' hx' z hz => ?_⟩
      rw [e] at hα
      rcases mem_sc.mp hα with e' | e'
      · rw [e'] at hx'
        rw [H.fn _ _ _ hx' hx] at hz
        exact hsub z hz
      · exact hsub z (hxm α e' x' hx' z hz)
    · have hm := H.lim β y hβ hl hy
      refine ⟨fun z hz w hw => ?_, fun α hα x hx z hz => (hm z).mpr ⟨α, hα, x, hx, hz⟩⟩
      obtain ⟨α, hα, x, hx, hzx⟩ := (hm z).mp hz
      exact (hm w).mpr ⟨α, hα, x, hx, (ih' α hα x hx).1 z hzx w hw⟩)
  exact fun β hβ => tMon_iff.mp (key β hβ)

theorem powH_mono {h θ α β x y : V} (H : IsPowH h θ) (hβ : β ∈ sc θ) (hαβ : α ∈ β)
    (hx : Pr h α x) (hy : Pr h β y) : ∀ z, z ∈ x → z ∈ y :=
  (powH_tmon H β hβ y hy).2 α hαβ x hx

/-- **The value of the hierarchy at the numeral `k` is the `k`-th iterated power set of
`ω`.** -/
theorem powH_num {h θ : V} (H : IsPowH h θ) : ∀ k : ℕ, (nm k : V) ∈ sc θ → Pr h (nm k) (pw k)
  | 0, _ => H.zero
  | k + 1, hk => by
    have hk' : (nm k : V) ∈ θ := by
      rcases mem_sc.mp hk with e | e
      · rw [← e]
        exact self_mem_sc _
      · exact H.ord.1 _ e _ (self_mem_sc _)
    exact H.succ (nm k) (pw k) hk' (powH_num H k (mem_sc.mpr (Or.inr hk')))

end model

/-! ### The recursion -/

section defs2

variable {V : Type} [SetStructure V]

/-- The rule for the members of the value at `γ`, given the earlier values `f`; `O` is `ω`. -/
def RuleR (γ f z O : V) : Prop :=
  ((∀ w, w ∈ γ → False) ∧ z ∈ O) ∨
  ((∃ η, η ∈ γ ∧ (SuccR γ η ∧ ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ x, x ∈ u ∧
      (IsOp q η x ∧ ∀ w, w ∈ z → w ∈ x))) ∨
  ((∀ η, η ∈ γ → ∃ η', η' ∈ γ ∧ η ∈ η') ∧ ∃ α, α ∈ γ ∧ ∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧
      ∃ x, x ∈ u ∧ (IsOp q α x ∧ z ∈ x)))

/-- `y` is the set of the members of the set that `Sq` gives at `γ` which satisfy the rule. -/
def GRule (γ f y Sq O : V) : Prop :=
  ∃ q, q ∈ Sq ∧ ∃ u, u ∈ q ∧ ∃ S, S ∈ u ∧ (IsOp q γ S ∧
    ((∀ z, z ∈ y → (z ∈ S ∧ RuleR γ f z O)) ∧ ∀ z, z ∈ S → (RuleR γ f z O → z ∈ y)))

end defs2

def ruleB : BDef (k := 4) (fun V _ v ↦ RuleR (v 0) (v 1) (v 2) (v 3)) :=
  (((BDef.ball 0 BDef.fls).and (BDef.mem 2 3)).or
    ((BDef.bex 0 ((succB.comp ![1, 0]).and (BDef.bex 2 (BDef.bex 0 (BDef.bex 0
      ((isOpB.comp ![2, 3, 0]).and (BDef.ball 6 (BDef.mem 0 1)))))))).or
    ((BDef.ball 0 (BDef.bex 1 (BDef.mem 1 0))).and (BDef.bex 0 (BDef.bex 2 (BDef.bex 0
      (BDef.bex 0 ((isOpB.comp ![2, 3, 0]).and (BDef.mem 6 0))))))))).congr
    fun _ _ _ => Iff.rfl

def gRuleB : BDef (k := 5) (fun V _ v ↦ GRule (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 3 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 3, 0]).and
    ((BDef.ball 5 ((BDef.mem 0 1).and (ruleB.comp ![4, 5, 0, 8]))).and
      (BDef.ball 0 ((ruleB.comp ![4, 5, 0, 8]).imp (BDef.mem 0 6)))))))).congr
    fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem prE_iff {f a : V} {P : V → Prop} :
    (∃ q, q ∈ f ∧ ∃ u, u ∈ q ∧ ∃ x, x ∈ u ∧ (IsOp q a x ∧ P x)) ↔ ∃ x, Pr f a x ∧ P x := by
  constructor
  · rintro ⟨q, hq, u, -, x, -, hop, hP⟩
    exact ⟨x, ⟨q, hq, hop⟩, hP⟩
  · rintro ⟨x, ⟨q, hq, hop⟩, hP⟩
    obtain ⟨u, hu, hxu⟩ := pr_snd_mem hop
    exact ⟨q, hq, u, hu, x, hxu, hop, hP⟩

theorem ruleR_iff {γ f z O : V} : RuleR γ f z O ↔
    (((∀ w, w ∈ γ → False) ∧ z ∈ O) ∨
    ((∃ η, η ∈ γ ∧ (SuccR γ η ∧ ∃ x, Pr f η x ∧ ∀ w, w ∈ z → w ∈ x)) ∨
    ((∀ η, η ∈ γ → ∃ η', η' ∈ γ ∧ η ∈ η') ∧ ∃ α, α ∈ γ ∧ ∃ x, Pr f α x ∧ z ∈ x))) :=
  or_congr Iff.rfl (or_congr
    (exists_congr fun _ => and_congr Iff.rfl (and_congr Iff.rfl prE_iff))
    (and_congr Iff.rfl (exists_congr fun _ => and_congr Iff.rfl prE_iff)))

theorem gRule_iff {γ f y Sq O : V} : GRule γ f y Sq O ↔
    ∃ S, Pr Sq γ S ∧ ∀ z, z ∈ y ↔ (z ∈ S ∧ RuleR γ f z O) := by
  constructor
  · rintro ⟨q, hq, u, -, S, -, hop, h1, h2⟩
    exact ⟨S, ⟨q, hq, hop⟩, fun z => ⟨h1 z, fun h => h2 z h.1 h.2⟩⟩
  · rintro ⟨S, ⟨q, hq, hop⟩, h⟩
    obtain ⟨u, hu, hSu⟩ := pr_snd_mem hop
    exact ⟨q, hq, u, hu, S, hSu, hop, fun z hz => (h z).mp hz, fun z h1 h2 => (h z).mpr ⟨h1, h2⟩⟩

/-- **The hierarchy exists on the ordinals up to `ρ`**, when there is a sequence of sets on
those ordinals, each including `ω`, with every subset of an earlier one a member of each later
one. -/
theorem exists_powH {ρ Sq : V} (hρ : Ord ρ)
    (htot : ∀ α, α ∈ sc ρ → ∃ S, Pr Sq α S)
    (hfn : ∀ α S S', Pr Sq α S → Pr Sq α S' → S = S')
    (hom : ∀ α S, α ∈ sc ρ → Pr Sq α S → ∀ n, n ∈ (om : V) → n ∈ S)
    (hmono : ∀ α β S S', α ∈ β → β ∈ sc ρ → Pr Sq α S → Pr Sq β S' →
      (∀ z, z ∈ S → z ∈ S') ∧ ∀ x, (∀ z, z ∈ x → z ∈ S) → x ∈ S') :
    ∃ h, IsPowH h ρ := by
  let G : MRel 5 := fun V _ v ↦ GRule (v 0) (v 1) (v 2) (v 3) (v 4)
  have hsO : Ord (sc ρ) := ord_sc hρ
  obtain ⟨Sρ, hSρ⟩ := htot ρ (self_mem_sc ρ)
  have hloc : ∀ γ f f' y : V, Ord γ → (∀ γ', γ' ∈ γ → ∀ y', Pr f γ' y' ↔ Pr f' γ' y') →
      G V (γ :> f :> y :> ![Sq, (om : V)]) → G V (γ :> f' :> y :> ![Sq, (om : V)]) := by
    intro γ f f' y _ hag hG
    have hG' : GRule γ f y Sq (om : V) := hG
    have hr : ∀ z, RuleR γ f z (om : V) ↔ RuleR γ f' z (om : V) := fun z => by
      rw [ruleR_iff, ruleR_iff]
      refine or_congr Iff.rfl (or_congr ?_ ?_)
      · exact exists_congr fun η => and_congr_right fun hη => and_congr Iff.rfl
          (exists_congr fun x => and_congr (hag η hη x) Iff.rfl)
      · exact and_congr Iff.rfl (exists_congr fun α => and_congr_right fun hα =>
          exists_congr fun x => and_congr (hag α hα x) Iff.rfl)
    obtain ⟨S, hS, hy⟩ := gRule_iff.mp hG'
    show GRule γ f' y Sq (om : V)
    exact gRule_iff.mpr ⟨S, hS, fun z => (hy z).trans (and_congr Iff.rfl (hr z))⟩
  have huniq : ∀ γ f y y' : V, G V (γ :> f :> y :> ![Sq, (om : V)]) →
      G V (γ :> f :> y' :> ![Sq, (om : V)]) → y = y' := by
    intro γ f y y' h1 h2
    have h1' : GRule γ f y Sq (om : V) := h1
    have h2' : GRule γ f y' Sq (om : V) := h2
    obtain ⟨S, hS, hy⟩ := gRule_iff.mp h1'
    obtain ⟨S', hS', hy'⟩ := gRule_iff.mp h2'
    rw [hfn γ S' S hS' hS] at hy'
    exact mem_ext fun z => (hy z).trans (hy' z).symm
  obtain ⟨F, hF⟩ := ord_rec (G := G) (p := ![Sq, (om : V)]) gRuleB hloc huniq ρ (℘ Sρ) hρ
    (fun β hβ f _ _ => by
      obtain ⟨S, hS⟩ := htot β hβ
      let y : V := sepB (k := 3) (ruleB.comp ![1, 2, 0, 3]) S ![β, f, (om : V)]
      have hy : ∀ z, z ∈ y ↔ z ∈ S ∧ RuleR β f z (om : V) := fun z => mem_sepB _ _ _ z
      refine ⟨y, mem_power_iff.mpr fun z hz => ?_, ?_⟩
      · have hzS := ((hy z).mp hz).1
        rcases mem_sc.mp hβ with e | e
        · rw [e] at hS
          rw [hfn ρ Sρ S hSρ hS]
          exact hzS
        · exact (hmono β ρ S Sρ e (self_mem_sc ρ) hS hSρ).1 z hzS
      · show GRule β f y Sq (om : V)
        exact gRule_iff.mpr ⟨S, hS, hy⟩)
  have hval : ∀ γ y, Pr F γ y →
      ∃ S, Pr Sq γ S ∧ ∀ z, z ∈ y ↔ (z ∈ S ∧ RuleR γ F z (om : V)) := fun γ y h => by
    have h1 : GRule γ F y Sq (om : V) := att_G hF h
    exact gRule_iff.mp h1
  have hfnF : ∀ α x x', Pr F α x → Pr F α x' → x = x' := fun α x x' h h' => att_fun hF h h'
  have htotF : ∀ α, α ∈ sc ρ → ∃ x, Pr F α x := fun α hα => by
    obtain ⟨y, hy, -⟩ := att_total hF hα
    exact ⟨y, hy⟩
  have hsub : ∀ γ y S, Pr F γ y → Pr Sq γ S → ∀ z, z ∈ y → z ∈ S := by
    intro γ y S hy hS z hz
    obtain ⟨S', hS', hm⟩ := hval γ y hy
    rw [hfn γ S S' hS hS']
    exact ((hm z).mp hz).1
  refine ⟨F, hρ, hfnF, htotF, ?_, ?_, ?_⟩
  · have h0 : (∅ : V) ∈ sc ρ := by
      rcases ord_tri ord_empty hρ with e | e | e
      · exact mem_sc.mpr (Or.inr e)
      · exact mem_sc.mpr (Or.inl e)
      · exact absurd e (by simp)
    obtain ⟨y, hy⟩ := htotF ∅ h0
    obtain ⟨S, hS, hm⟩ := hval ∅ y hy
    have e : y = (om : V) := mem_ext fun z => by
      rw [hm z, ruleR_iff]
      constructor
      · rintro ⟨-, (⟨-, h⟩ | ⟨η, hη, -⟩ | ⟨-, α, hα, -⟩)⟩
        · exact h
        · exact absurd hη (by simp)
        · exact absurd hα (by simp)
      · intro h
        exact ⟨hom ∅ S h0 hS z h, Or.inl ⟨fun w hw => absurd hw (by simp), h⟩⟩
    rw [← e]
    exact hy
  · intro α x hα hx
    have hs : sc α ∈ sc ρ := by
      rcases ord_sc_le (ord_mem hρ hα) hρ hα with e | e
      · exact mem_sc.mpr (Or.inl e)
      · exact mem_sc.mpr (Or.inr e)
    obtain ⟨y, hy⟩ := htotF (sc α) hs
    obtain ⟨S, hS, hm⟩ := hval (sc α) y hy
    obtain ⟨Sα, hSα⟩ := htot α (mem_sc.mpr (Or.inr hα))
    have e : y = ℘ x := mem_ext fun z => by
      rw [hm z, ruleR_iff]
      constructor
      · rintro ⟨-, (⟨h, -⟩ | ⟨η, -, hsc, x', hx', hz⟩ | ⟨h, -⟩)⟩
        · exact (h α (self_mem_sc α)).elim
        · have e1 : α = η := sc_inj (succR_iff_sc.mp hsc)
          rw [← e1] at hx'
          rw [hfnF _ _ _ hx' hx] at hz
          exact mem_power_iff.mpr hz
        · obtain ⟨η', hη', hlt⟩ := h α (self_mem_sc α)
          rcases mem_sc.mp hη' with e2 | e2
          · rw [e2] at hlt
            exact absurd hlt (mem_irrefl α)
          · exact absurd hlt (mem_asymm e2)
      · intro hz
        have hzx : ∀ w, w ∈ z → w ∈ x := mem_power_iff.mp hz
        exact ⟨(hmono α (sc α) Sα S (self_mem_sc α) hs hSα hS).2 z
            fun w hw => hsub α x Sα hx hSα w (hzx w hw),
          Or.inr (Or.inl ⟨α, self_mem_sc α, succR_iff_sc.mpr rfl, x, hx, hzx⟩)⟩
    rw [← e]
    exact hy
  · intro β y hβ hl hy z
    obtain ⟨S, hS, hm⟩ := hval β y hy
    rw [hm z, ruleR_iff]
    constructor
    · rintro ⟨-, (⟨h, -⟩ | ⟨η, hη, hsc, -⟩ | ⟨-, h⟩)⟩
      · obtain ⟨w, hw⟩ := hl.2.1
        exact (h w hw).elim
      · have h1 := hl.2.2 η hη
        rw [← succR_iff_sc.mp hsc] at h1
        exact absurd h1 (mem_irrefl β)
      · exact h
    · rintro ⟨α, hα, x, hx, hzx⟩
      obtain ⟨Sα, hSα⟩ := htot α (hsO.1 β hβ α hα)
      exact ⟨(hmono α β Sα S hα hβ hSα hS).1 z (hsub α x Sα hx hSα z hzx),
        Or.inr (Or.inr ⟨fun η hη => ⟨sc η, hl.2.2 η hη, self_mem_sc η⟩, α, hα, x, hx, hzx⟩)⟩

end model

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **The rank axiom for `n` holds** if there is such a sequence on the ordinals up to the
least ordinal that does not map one-to-one into the `n`-th iterated power set of `ω`. -/
theorem hasRank_of_levels (n : ℕ) {ρ Sq : V} (hρ : NextS (pw n : V) ρ)
    (htot : ∀ α, α ∈ sc ρ → ∃ S, Pr Sq α S)
    (hfn : ∀ α S S', Pr Sq α S → Pr Sq α S' → S = S')
    (hom : ∀ α S, α ∈ sc ρ → Pr Sq α S → ∀ n, n ∈ (om : V) → n ∈ S)
    (hmono : ∀ α β S S', α ∈ β → β ∈ sc ρ → Pr Sq α S → Pr Sq β S' →
      (∀ z, z ∈ S → z ∈ S') ∧ ∀ x, (∀ z, z ∈ x → z ∈ S) → x ∈ S') :
    HasRank n V := by
  have hρO : Ord ρ := ord_of_ordS hρ.1
  obtain ⟨h, H⟩ := exists_powH hρO htot hfn hom hmono
  have hnO : Ord (nm n : V) := ord_mem ord_om (nm_mem_om n)
  have hsub : ∀ z, z ∈ (nm n : V) → z ∈ (pw n : V) :=
    fun z hz => om_sub_pw n z (om_tr _ (nm_mem_om n) z hz)
  have hv : VInj (nm n : V) (pw n) := vinj_of_sub hsub
  have hnρ : (nm n : V) ∈ ρ := by
    rcases ord_tri hnO hρO with e | e | e
    · exact e
    · rw [e] at hv
      exact absurd hv hρ.2.1
    · exact absurd (vinj_dom_mono hv fun z hz => hnO.1 ρ e z hz) hρ.2.1
  exact ⟨h, ρ, hρO, (powH_iff hρO).mpr H, nm n, isNum_nm n, hnρ, pw n,
    powH_num H n (mem_sc.mpr (Or.inr hnρ)), hρ.2.1⟩

end model

end MH

end FFL.FirstOrder.SetTheory
