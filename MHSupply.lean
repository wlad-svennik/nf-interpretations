module

public import MHLadder

@[expose] public section

set_option autoImplicit false

/-!
# From a supply of sets to a tower whose height is an iterated next height

In a model of `𝗠𝗛`. `NextH κ μ`: `μ` is the next height after `κ` (`lnext_spec`). `IterH n κ μ`:
`μ` is the `n`-th next height after `κ`, for a standard `n`.

A *supply* for the standard number `r` (`Supply r T ρ Sq`) consists of sets `T 0, …, T (r + 2)`,
each satisfying `BaseS` and with every set of relations on it a member of the next; an ordinal
`ρ` that has as members all the ordinals that map one-to-one into `T (r + 2)`; and a set `Sq`
that relates every member of `ρ` to a set that satisfies `BaseS` and includes `T (r + 2)`, the
set at a larger member of `ρ` including and being far above the set at a smaller one.

**`supply_tower`**: then, with `ν₀` the least ordinal whose level does not map one-to-one into
`T 0` and `d` the `r`-th next height after `ν₀`, there is a tower of height `d` in the host at
a full height.

The proof: the levels at the first `r + 1` next heights after `ν₀` map one-to-one into
`T 2, …, T (r + 2)` (`supply_heights`, by `vinj_lim`), so the ordinals up to `d + 2` are
members of `ρ`, and the sets that `Sq` gives for them are a ladder (`exists_level_tower`).

In a model of `𝗠𝗛` that comes from a model of `𝗡𝗙𝗨𝗜𝗖`, the sets of a supply are to be levels of
the cumulative hierarchy of the types: this file is where they will be used.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

section supply

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- `μ` is the next height after `κ`. -/
def NextH (κ μ : V) : Prop :=
  Lim μ ∧ κ ∈ μ ∧ ¬LInj (Lev μ) (Lev κ) ∧ ∀ δ, δ ∈ μ → LInj (Lev δ) (Lev κ)

/-- `μ` is the `n`-th next height after `κ`. -/
def IterH : ℕ → V → V → Prop
  | 0, κ, μ => μ = κ
  | n + 1, κ, μ => ∃ μ' : V, IterH n κ μ' ∧ NextH μ' μ

theorem nextH_full {κ μ : V} (hκ : Lim κ) (hom : (om : V) ∈ κ) (h : NextH κ μ) : Full μ :=
  full_of_sub hκ hom h.1 h.2.1 h.2.2.1 h.2.2.2 (lnext_sub hκ hom h.1 h.2.1 h.2.2.1 h.2.2.2)

theorem iterH_lim {κ : V} (hκ : Lim κ) (hom : (om : V) ∈ κ) :
    ∀ (n : ℕ) (μ : V), IterH n κ μ → Lim μ ∧ (om : V) ∈ μ
  | 0, μ, h => by
    rw [show μ = κ from h]
    exact ⟨hκ, hom⟩
  | n + 1, μ, ⟨μ', h', hn⟩ =>
    ⟨hn.1, hn.1.1.1 μ' hn.2.1 om (iterH_lim hκ hom n μ' h').2⟩

/-- The level at the next height after `κ` maps one-to-one into `T`, when the level at `κ` maps
one-to-one into `S` and every set of relations on `S` is a member of `T`. -/
theorem vinj_nextH {κ μ S T : V} (h : NextH κ μ) (hv : VInj (Lev κ) S) (hST : SupRel S T) :
    VInj (Lev μ) T :=
  vinj_lim h.1 (fun δ hδ => vinj_comp (linj_vinj (h.2.2.2 δ hδ)) hv) hST

/-- **A supply of sets** for the standard number `r`. -/
structure Supply (r : ℕ) (T : ℕ → V) (ρ Sq : V) : Prop where
  base : ∀ i, i ≤ r + 2 → BaseS (T i)
  step : ∀ i, i ≤ r + 1 → SupRel (T i) (T (i + 1))
  rho : Ord ρ
  hart : ∀ ξ : V, Ord ξ → VInj ξ (T (r + 2)) → ξ ∈ ρ
  tot : ∀ α : V, α ∈ ρ → ∃ S : V, Pr Sq α S
  sbase : ∀ α S : V, α ∈ ρ → Pr Sq α S → BaseS S
  low : ∀ α S : V, α ∈ ρ → Pr Sq α S → ∀ z, z ∈ T (r + 2) → z ∈ S
  mono : ∀ α β S S' : V, α ∈ β → β ∈ ρ → Pr Sq α S → Pr Sq β S' →
    (∀ z, z ∈ S → z ∈ S') ∧ Far S S'

/-- The levels at the first next heights map one-to-one into the sets of the supply. -/
theorem supply_heights {r : ℕ} {T : ℕ → V} {ρ Sq : V} (sup : Supply r T ρ Sq) :
    ∀ j, j ≤ r → ∃ ν₀ μ : V, HgtV (T 0) ν₀ ∧ IterH (j + 1) ν₀ μ ∧ VInj (Lev μ) (T (j + 2))
  | 0, _ => by
    obtain ⟨ν₀, hν⟩ := hgtV_exists (T 0)
    obtain ⟨hl, hom⟩ := hgtV_lim (sup.base 0 (by omega)) hν
    obtain ⟨μ, hμ, hνμ, hn, hall⟩ := lnext_spec hl hom
    have h1 : VInj (Lev ν₀) (T 1) := vinj_lim hl hν.2.2 (sup.step 0 (by omega))
    exact ⟨ν₀, μ, hν, ⟨ν₀, rfl, hμ, hνμ, hn, hall⟩,
      vinj_nextH ⟨hμ, hνμ, hn, hall⟩ h1 (sup.step 1 (by omega))⟩
  | j + 1, hj => by
    obtain ⟨ν₀, μ, hν, hit, hv⟩ := supply_heights sup j (by omega)
    obtain ⟨hl, hom⟩ := hgtV_lim (sup.base 0 (by omega)) hν
    obtain ⟨hμl, hμom⟩ := iterH_lim hl hom (j + 1) μ hit
    obtain ⟨μ', hμ', hμμ', hn, hall⟩ := lnext_spec hμl hμom
    exact ⟨ν₀, μ', hν, ⟨μ, hit, hμ', hμμ', hn, hall⟩,
      vinj_nextH ⟨hμ', hμμ', hn, hall⟩ hv (sup.step (j + 2) (by omega))⟩

/-- **A supply for `r` gives a tower whose height is the `r`-th next height** after the least
ordinal whose level does not map one-to-one into `T 0`. -/
theorem supply_tower {r : ℕ} {T : ℕ → V} {ρ Sq : V} (sup : Supply r T ρ Sq) :
    ∃ ν₀ d : V, HgtV (T 0) ν₀ ∧ IterH r ν₀ d ∧
      ∃ (K' : V) (hK' : Full K') (Tw : Host.Tower (levHost hK')),
        hval hK' Tw.d = d ∧ d ∈ K' := by
  obtain ⟨ν₀, μ, hν, ⟨d, hd, hnext⟩, hv⟩ := supply_heights sup r le_rfl
  obtain ⟨hl, hom⟩ := hgtV_lim (sup.base 0 (by omega)) hν
  obtain ⟨hdl, -⟩ := iterH_lim hl hom r d hd
  have hμl : Lim μ := hnext.1
  have hdμ : d ∈ μ := hnext.2.1
  have hτμ : sc (sc d) ∈ μ := hμl.2.2 _ (hμl.2.2 d hdμ)
  have hτO : Ord (sc (sc d)) := ord_sc (ord_sc hdl.1)
  have hρ : ∀ ξ, ξ ∈ μ → ξ ∈ ρ := fun ξ hξ => sup.hart ξ (ord_mem hμl.1 hξ)
    (vinj_dom_mono hv fun z hz => ord_mem_lev_lim hμl z (hμl.1.1 ξ hξ z hz))
  have hτρ : sc (sc d) ∈ ρ := hρ _ hτμ
  have hin : ∀ γ, γ ∈ sc (sc d) → γ ∈ ρ := fun γ hγ => hρ γ (hμl.1.1 _ hτμ γ hγ)
  obtain ⟨U, hU⟩ := sup.tot _ hτρ
  have lad : Ladder (sc (sc d)) Sq U (sc (sc d)) :=
    { tot := fun γ hγ => sup.tot γ (hin γ hγ)
      base := fun γ S hγ hS => sup.sbase γ S (hin γ hγ) hS
      sub := fun γ S hγ hS => (sup.mono γ _ S U hγ hτρ hS hU).1
      top := fun γ S hγ hS => (sup.mono γ _ S U hγ hτρ hS hU).2
      far := fun γ γ' S S' hγγ' hγ' hS hS' => (sup.mono γ γ' S S' hγγ' (hin γ' hγ') hS hS').2
      low := fun γ S hγ hS => vinj_mono (vinj_dom_mono hv (lev_mono hμl.1 hτμ))
        (sup.low γ S (hin γ hγ) hS)
      baseU := sup.sbase _ U hτρ hU }
  have hd0 : d ≠ ∅ := by
    obtain ⟨z, hz⟩ := hdl.2.1
    intro e
    rw [e] at hz
    exact absurd hz (by simp)
  exact ⟨ν₀, d, hν, hd, exists_level_tower hdl.1 hd0 hτO (self_mem_sc (sc d)) lad⟩

end supply

end MH

end FFL.FirstOrder.SetTheory
