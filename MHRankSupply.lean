module

public import MHRank

@[expose] public section

set_option autoImplicit false

/-!
# From the rank axioms to a supply of sets, and `Con(𝗠𝗛𝗥) → Con(𝗡𝗙𝗖)`

In a model of `𝗠𝗛` in which the rank axiom for `4r + 15` holds, with hierarchy `h` on the
ordinals up to `θ`:

* The base sets are `pw 4, pw 8, …` (`Supply.base`, `Supply.step` by `pw_base`, `pw_supRel`).
* `ρ` is the least ordinal that does not map one-to-one into `pw (4r + 12)`.
* `lex_collapse`: the lexicographic order on the pairs of a member of `ρ` and a finite ordinal
  has a collapse `F` onto an ordinal `lam` (the collapse axiom; this is the ordinal `ω · ρ`).
* `lam ⊆ θ`. Otherwise `θ` is a value of `F`, so the inverse of `F` maps `θ` one-to-one into
  the pairs of a member of some `α₀ + 1` and a finite ordinal, where `α₀ ∈ ρ` maps one-to-one
  into `pw (4r + 12)`; so `θ` maps one-to-one into `pw (4r + 15)` (`vinj_sc_pow`,
  `vinj_prod_left`, `prod_pw_sub`), against the axiom.
* The set at `α ∈ ρ` is the value of `h` at `F ⟨α, 4r + 12⟩`. Eight steps of the power set
  lie between the sets at `α < β`, so the later is far above the earlier.

**`supply_of_rank`**: this is a supply for `r`. **`consistent_nfc_of_consistent_mhr`** follows
by `MH.consistent_nfc_of_supplies`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### The collapse of the lexicographic order -/

section collapse

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **The lexicographic order on the pairs of a member of an ordinal `S` and a finite ordinal
has a collapse onto an ordinal.** -/
theorem lex_collapse {S : V} (hS : Ord S) : ∃ F lam : V, Ord lam ∧
    (∀ γ n, γ ∈ S → n ∈ (om : V) → ∃ v, v ∈ lam ∧ (Pr F (kp γ n) v ∧
      ((∀ v', Pr F (kp γ n) v' → v' = v) ∧
        ∀ y, (y ∈ v ↔ ∃ γ' n', γ' ∈ S ∧ (n' ∈ (om : V) ∧
          ((γ' ∈ γ ∨ (γ' = γ ∧ n' ∈ n)) ∧ Pr F (kp γ' n') y)))))) ∧
    (∀ y, y ∈ lam → ∃ γ n, γ ∈ S ∧ (n ∈ (om : V) ∧ Pr F (kp γ n) y)) := by
  let u : V := prodS S (om : V)
  obtain ⟨T, hT, hcol⟩ := hc_of_models (V := V) u
  let r : V := relB (k := 0) lexRB u u ![]
  have hr : ∀ a b, Pr r a b ↔ a ∈ u ∧ b ∈ u ∧ LexR a b := fun a b => pr_relB lexRB u u ![] a b
  have hu : ∀ a, a ∈ u ↔ ∃ γ, γ ∈ S ∧ ∃ n, n ∈ (om : V) ∧ a = kp γ n := fun a => mem_prodS
  have hrk : ∀ γ n γ' n', Pr r (kp γ n) (kp γ' n') ↔ γ ∈ S ∧ n ∈ (om : V) ∧ γ' ∈ S ∧
      n' ∈ (om : V) ∧ (γ ∈ γ' ∨ (γ = γ' ∧ n ∈ n')) := by
    intro γ n γ' n'
    rw [hr, hu, hu, lexR_iff]
    constructor
    · rintro ⟨⟨g, hg, m, hm, e⟩, ⟨g', hg', m', hm', e'⟩, h⟩
      obtain ⟨rfl, rfl⟩ := kp_inj e
      obtain ⟨rfl, rfl⟩ := kp_inj e'
      exact ⟨hg, hm, hg', hm', h⟩
    · rintro ⟨hg, hm, hg', hm', h⟩
      exact ⟨⟨γ, hg, n, hm, rfl⟩, ⟨γ', hg', n', hm', rfl⟩, h⟩
  have hwf : WFon r u := by
    rintro X ⟨c₀, hc₀, -⟩ hXu
    -- least first coordinate
    let A : V := sepB (k := 2) (BDef.bex 1 (BDef.bex 3 (isOpB.comp ![1, 2, 0]))) S ![X, (om : V)]
    have hA : ∀ γ, γ ∈ A ↔ γ ∈ S ∧ ∃ a, a ∈ X ∧ ∃ n, n ∈ (om : V) ∧ IsOp a γ n :=
      fun γ => mem_sepB _ _ _ γ
    obtain ⟨g₀, hg₀, n₀, hn₀, rfl⟩ := (hu c₀).mp (hXu c₀ hc₀)
    obtain ⟨g, hgA, hgmin⟩ := ord_least A (fun z hz => ord_mem hS ((hA z).mp hz).1)
      ⟨g₀, (hA g₀).mpr ⟨hg₀, _, hc₀, n₀, hn₀, isOp_kp g₀ n₀⟩⟩
    let B : V := sepB (k := 2) (BDef.bex 1 (isOpB.comp ![0, 3, 1])) (om : V) ![X, g]
    have hB : ∀ n, n ∈ B ↔ n ∈ (om : V) ∧ ∃ a, a ∈ X ∧ IsOp a g n := fun n => mem_sepB _ _ _ n
    obtain ⟨hgS, a₁, ha₁, n₁, hn₁, hop₁⟩ := (hA g).mp hgA
    obtain ⟨n, hnB, hnmin⟩ := ord_least B (fun z hz => ord_mem ord_om ((hB z).mp hz).1)
      ⟨n₁, (hB n₁).mpr ⟨hn₁, a₁, ha₁, hop₁⟩⟩
    obtain ⟨hn, a, ha, hop⟩ := (hB n).mp hnB
    have ea : a = kp g n := isOp_iff.mp hop
    subst ea
    refine ⟨kp g n, ha, fun b hb hbr => ?_⟩
    obtain ⟨g', hg', n', hn', rfl⟩ := (hu b).mp (hXu b hb)
    rcases ((hrk g' n' g n).mp hbr).2.2.2.2 with h | ⟨rfl, h⟩
    · rcases hgmin g' ((hA g').mpr ⟨hg', _, hb, n', hn', isOp_kp g' n'⟩) with e | e
      · exact mem_irrefl g' (e ▸ h)
      · exact mem_asymm e h
    · rcases hnmin n' ((hB n').mpr ⟨hn', _, hb, isOp_kp g' n'⟩) with e | e
      · exact mem_irrefl n' (e ▸ h)
      · exact mem_asymm e h
  obtain ⟨F, hF⟩ := hcol r hwf
  -- the value of the collapse
  have hFv : ∀ a, a ∈ u → ∃ v, v ∈ T ∧ Pr F a v ∧ (∀ v', Pr F a v' → v' = v) ∧
      ∀ y, (y ∈ v ↔ ∃ a', a' ∈ u ∧ Pr r a' a ∧ Pr F a' y) := hF
  have hrtrans : ∀ a b c, Pr r a b → Pr r b c → Pr r a c := by
    intro a b c hab hbc
    obtain ⟨g, hg, n, hn, rfl⟩ := (hu a).mp ((hr a b).mp hab).1
    obtain ⟨g', hg', n', hn', rfl⟩ := (hu b).mp ((hr _ b).mp hab).2.1
    obtain ⟨g'', hg'', n'', hn'', rfl⟩ := (hu c).mp ((hr _ c).mp hbc).2.1
    refine (hrk g n g'' n'').mpr ⟨hg, hn, hg'', hn'', ?_⟩
    rcases ((hrk g n g' n').mp hab).2.2.2.2 with h1 | ⟨rfl, h1⟩
    · rcases ((hrk g' n' g'' n'').mp hbc).2.2.2.2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl ((ord_mem hS hg'').1 g' h2 g h1)
      · exact Or.inl h1
    · rcases ((hrk g n' g'' n'').mp hbc).2.2.2.2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨rfl, (ord_mem ord_om hn'').1 n' h2 n h1⟩
  -- the values are ordinals
  have hOrd : ∀ a, a ∈ u → ∀ v, Pr F a v → Ord v := by
    by_contra hcon
    let Z : V := sepB (k := 1) (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 ((isOpB.comp ![2, 3, 0]).and
      (ordB.comp ![0]).not)))) u ![F]
    have hZ : ∀ a, a ∈ Z ↔ a ∈ u ∧ ∃ q, q ∈ F ∧ ∃ w, w ∈ q ∧ ∃ y, y ∈ w ∧
        (IsOp q a y ∧ ¬Ord y) := fun a => mem_sepB _ _ _ a
    have hne : ∃ a, a ∈ Z ∧ ¬False := by
      by_contra h
      refine hcon fun a ha v hv => ?_
      by_contra hn
      obtain ⟨q, hq, hop⟩ := hv
      obtain ⟨w, hw, hyw⟩ := pr_snd_mem hop
      exact h ⟨a, (hZ a).mpr ⟨ha, q, hq, w, hw, v, hyw, hop, hn⟩, id⟩
    obtain ⟨a, haZ, hmin⟩ := hwf Z hne (fun c hc => ((hZ c).mp hc).1)
    obtain ⟨hau, q, hq, w, -, y, -, hop, hny⟩ := (hZ a).mp haZ
    obtain ⟨v, -, hav, hvu, hvm⟩ := hFv a hau
    have e : y = v := hvu y ⟨q, hq, hop⟩
    subst e
    have hsmall : ∀ a', a' ∈ u → Pr r a' a → ∀ y', Pr F a' y' → Ord y' := by
      intro a' ha' hra y' hy'
      by_contra hn
      obtain ⟨q', hq', hop'⟩ := hy'
      obtain ⟨w', hw', hyw'⟩ := pr_snd_mem hop'
      exact hmin a' ((hZ a').mpr ⟨ha', q', hq', w', hw', y', hyw', hop', hn⟩) hra
    refine hny ⟨fun z hz t ht => ?_, fun z hz => ?_⟩
    · obtain ⟨a', ha', hra, hFa'⟩ := (hvm z).mp hz
      obtain ⟨v', -, hav', hvu', hvm'⟩ := hFv a' ha'
      have e : z = v' := hvu' z hFa'
      subst e
      obtain ⟨a'', ha'', hra', hFa''⟩ := (hvm' t).mp ht
      exact (hvm t).mpr ⟨a'', ha'', hrtrans _ _ _ hra' hra, hFa''⟩
    · obtain ⟨a', ha', hra, hFa'⟩ := (hvm z).mp hz
      exact (hsmall a' ha' hra z hFa').1
  let lam : V := sepB (k := 2) (BDef.bex 1 (prB.comp ![3, 0, 1])) T ![u, F]
  have hlam : ∀ y, y ∈ lam ↔ y ∈ T ∧ ∃ a, a ∈ u ∧ Pr F a y := fun y => mem_sepB _ _ _ y
  have hlamO : Ord lam := by
    refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
    · obtain ⟨-, a, ha, hay⟩ := (hlam y).mp hy
      obtain ⟨v, -, hav, hvu, hvm⟩ := hFv a ha
      have e : y = v := hvu y hay
      subst e
      obtain ⟨a', ha', -, hFa'⟩ := (hvm z).mp hz
      obtain ⟨v', hv'T, -, hvu', -⟩ := hFv a' ha'
      exact (hlam z).mpr ⟨hvu' z hFa' ▸ hv'T, a', ha', hFa'⟩
    · obtain ⟨-, a, ha, hay⟩ := (hlam y).mp hy
      exact (hOrd a ha y hay).1
  refine ⟨F, lam, hlamO, fun γ n hγ hn => ?_, fun y hy => ?_⟩
  · have hau : kp γ n ∈ u := (hu _).mpr ⟨γ, hγ, n, hn, rfl⟩
    obtain ⟨v, hvT, hav, hvu, hvm⟩ := hFv _ hau
    refine ⟨v, (hlam v).mpr ⟨hvT, _, hau, hav⟩, hav, hvu, fun y => ?_⟩
    rw [hvm]
    constructor
    · rintro ⟨a', ha', hra, hFa'⟩
      obtain ⟨g, hg, m, hm, rfl⟩ := (hu a').mp ha'
      exact ⟨g, m, hg, hm, ((hrk g m γ n).mp hra).2.2.2.2, hFa'⟩
    · rintro ⟨g, m, hg, hm, hlt, hFa'⟩
      exact ⟨kp g m, (hu _).mpr ⟨g, hg, m, hm, rfl⟩,
        (hrk g m γ n).mpr ⟨hg, hm, hγ, hn, hlt⟩, hFa'⟩
  · obtain ⟨-, a, ha, hay⟩ := (hlam y).mp hy
    obtain ⟨g, hg, m, hm, rfl⟩ := (hu a).mp ha
    exact ⟨g, m, hg, hm, hay⟩

end collapse

/-! ### One-to-one maps -/

section defs

variable {V : Type} [SetStructure V]

/-- `v` is the singleton of the value of `g` at `u ∈ α`, or `u = α` and `v` is empty. -/
def ScPow (u v g α : V) : Prop :=
  (u ∈ α ∧ ∃ y, y ∈ v ∧ (Pr g u y ∧ ∀ y', y' ∈ v → y' = y)) ∨ (u = α ∧ ∀ y', y' ∈ v → False)

/-- `p = ⟨a, b⟩` and `q = ⟨g(a), b⟩`. -/
def ProdL (p q g : V) : Prop :=
  ∃ s, s ∈ p ∧ ∃ a, a ∈ s ∧ ∃ s', s' ∈ p ∧ ∃ b, b ∈ s' ∧ ∃ t, t ∈ q ∧ ∃ x, x ∈ t ∧
    (IsOp p a b ∧ (IsOp q x b ∧ Pr g a x))

/-- The set at `α`: the value of `h` at the value of `F` at the pair of `α` and `cb`. -/
def SqR (α S u cb θ F h : V) : Prop :=
  ∃ a, a ∈ u ∧ (IsOp a α cb ∧ ∃ v, v ∈ θ ∧ (Pr F a v ∧ Pr h v S))

end defs

def scPowB : BDef (k := 4) (fun V _ v ↦ ScPow (v 0) (v 1) (v 2) (v 3)) :=
  (((BDef.mem 0 3).and (BDef.bex 1 ((prB.comp ![3, 1, 0]).and
    (BDef.ball 2 (BDef.eq 0 1))))).or
    ((BDef.eq 0 3).and (BDef.ball 1 BDef.fls))).congr fun _ _ _ => Iff.rfl

def prodLB : BDef (k := 3) (fun V _ v ↦ ProdL (v 0) (v 1) (v 2)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 2 (BDef.bex 0 (BDef.bex 5 (BDef.bex 0
    ((isOpB.comp ![6, 4, 2]).and ((isOpB.comp ![7, 0, 2]).and
      (prB.comp ![8, 4, 0]))))))))).congr fun _ _ _ => Iff.rfl

def sqRB : BDef (k := 7) (fun V _ v ↦ SqR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  (BDef.bex 2 ((isOpB.comp ![0, 1, 4]).and (BDef.bex 5 ((prB.comp ![7, 1, 0]).and
    (prB.comp ![8, 0, 3]))))).congr fun _ _ _ => Iff.rfl

section maps

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- A relation with a bounded definition that is total on `A` with values in `B` and
one-to-one gives a one-to-one map. -/
theorem vinj_of_rel {k : ℕ} {R : MRel (k + 2)} (d : BDef R) (A B : V) (p : Fin k → V)
    (htot : ∀ u, u ∈ A → ∃ v, v ∈ B ∧ R V (u :> v :> p))
    (hinj : ∀ u u' v, u ∈ A → u' ∈ A → v ∈ B → R V (u :> v :> p) → R V (u' :> v :> p) →
      u = u') : VInj A B := by
  refine ⟨relB d A B p, fun u hu => ?_, fun u u' v hu hu' h1 h2 => ?_⟩
  · obtain ⟨v, hv, hR⟩ := htot u hu
    exact ⟨v, hv, hin_rl_iff.mpr (pr_iff.mp ((pr_relB d A B p u v).mpr ⟨hu, hv, hR⟩))⟩
  · obtain ⟨-, hv, k1⟩ := (pr_relB d A B p u v).mp (pr_iff.mpr (hin_rl_iff.mp h1))
    obtain ⟨-, -, k2⟩ := (pr_relB d A B p u' v).mp (pr_iff.mpr (hin_rl_iff.mp h2))
    exact hinj u u' v hu hu' hv k1 k2

/-- If `α` maps one-to-one into `X`, then `α + 1` maps one-to-one into the power set of `X`. -/
theorem vinj_sc_pow {α X : V} (h : VInj α X) : VInj (sc α) (℘ X) := by
  obtain ⟨g, hg1, hg2⟩ := h
  refine vinj_of_rel scPowB (sc α) (℘ X) ![g, α] (fun u hu => ?_)
    (fun u u' v _ _ _ h1 h2 => ?_)
  · rcases mem_sc.mp hu with e | e
    · refine ⟨∅, mem_power_iff.mpr fun z hz => absurd hz (by simp), ?_⟩
      show ScPow u ∅ g α
      exact Or.inr ⟨e, fun y hy => absurd hy (by simp)⟩
    · obtain ⟨y, hy, hr⟩ := hg1 u e
      refine ⟨{y}, mem_power_iff.mpr fun z hz => ?_, ?_⟩
      · rw [show z = y by simpa using hz]
        exact hy
      · show ScPow u {y} g α
        exact Or.inl ⟨e, y, by simp, pr_iff.mpr (hin_rl_iff.mp hr),
          fun y' hy' => by simpa using hy'⟩
  · have h1' : ScPow u v g α := h1
    have h2' : ScPow u' v g α := h2
    rcases h1' with ⟨hu1, y, hy, hr, -⟩ | ⟨e1, hemp⟩
    · rcases h2' with ⟨hu2, y', -, hr', hyu'⟩ | ⟨-, hemp'⟩
      · have e : y = y' := hyu' y hy
        rw [← e] at hr'
        exact hg2 u u' y hu1 hu2 (hin_rl_iff.mpr (pr_iff.mp hr)) (hin_rl_iff.mpr (pr_iff.mp hr'))
      · exact (hemp' y hy).elim
    · rcases h2' with ⟨-, y', hy', -⟩ | ⟨e2, -⟩
      · exact (hemp y' hy').elim
      · rw [e1, e2]

theorem prodL_iff {a b q g : V} : ProdL (kp a b) q g ↔ ∃ x, q = kp x b ∧ Pr g a x := by
  constructor
  · rintro ⟨s, -, a', -, s', -, b', -, t, -, x, -, h1, h2, h3⟩
    obtain ⟨rfl, rfl⟩ := op_inj (isOp_kp a b) h1
    exact ⟨x, isOp_iff.mp h2, h3⟩
  · rintro ⟨x, rfl, h3⟩
    obtain ⟨s, hs, has⟩ := pr_fst_mem (isOp_kp a b)
    obtain ⟨s', hs', hbs⟩ := pr_snd_mem (isOp_kp a b)
    obtain ⟨t, ht, hxt⟩ := pr_fst_mem (isOp_kp x b)
    exact ⟨s, hs, a, has, s', hs', b, hbs, t, ht, x, hxt, isOp_kp a b, isOp_kp x b, h3⟩

/-- A one-to-one map on the first components of pairs. -/
theorem vinj_prod_left {A X B : V} (h : VInj A X) : VInj (prodS A B) (prodS X B) := by
  obtain ⟨g, hg1, hg2⟩ := h
  refine vinj_of_rel prodLB (prodS A B) (prodS X B) ![g] (fun p hp => ?_)
    (fun p p' q hp hp' _ h1 h2 => ?_)
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_prodS.mp hp
    obtain ⟨x, hx, hr⟩ := hg1 a ha
    refine ⟨kp x b, mem_prodS.mpr ⟨x, hx, b, hb, rfl⟩, ?_⟩
    show ProdL (kp a b) (kp x b) g
    exact prodL_iff.mpr ⟨x, rfl, pr_iff.mpr (hin_rl_iff.mp hr)⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_prodS.mp hp
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_prodS.mp hp'
    have h1' : ProdL (kp a b) q g := h1
    have h2' : ProdL (kp a' b') q g := h2
    obtain ⟨x, e, hr⟩ := prodL_iff.mp h1'
    obtain ⟨x', e', hr'⟩ := prodL_iff.mp h2'
    obtain ⟨e1, e2⟩ := kp_inj (e.symm.trans e')
    rw [← e1] at hr'
    rw [hg2 a a' x ha ha' (hin_rl_iff.mpr (pr_iff.mp hr)) (hin_rl_iff.mpr (pr_iff.mp hr')), e2]

/-- The pairs of a member of `pw (j + 1)` and a finite ordinal are members of `pw (j + 3)`. -/
theorem prod_pw_sub (j : ℕ) :
    ∀ z : V, z ∈ prodS (pw (j + 1) : V) (om : V) → z ∈ (pw (j + 3) : V) := by
  intro z hz
  obtain ⟨x, hx, n, hn, rfl⟩ := mem_prodS.mp hz
  have hn' : n ∈ (pw (j + 1) : V) := om_sub_pw _ n hn
  show kp x n ∈ ℘ (℘ (pw (j + 1) : V))
  refine mem_power_iff.mpr fun s hs => mem_power_iff.mpr fun t ht => ?_
  rcases (by simpa [kp] using hs : s = {x} ∨ s = {x, n}) with rfl | rfl
  · rw [show t = x by simpa using ht]
    exact hx
  · rcases (by simpa using ht : t = x ∨ t = n) with rfl | rfl
    · exact hx
    · exact hn'

end maps

/-! ### The supply -/

section supply

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **In a model of `𝗠𝗛`, the rank axiom for `4r + 15` gives a supply of sets for `r`.** -/
theorem supply_of_rank (r : ℕ) (hR : HasRank (4 * r + 15) V) :
    ∃ ρ Sq : V, Supply r (fun j => (pw (4 * j + 4) : V)) ρ Sq := by
  obtain ⟨h, θ, hθ, hP, k, hk, hkθ, w, hw, hno⟩ := hR
  have H : IsPowH h θ := (powH_iff hθ).mp hP
  have ek : k = nm (4 * r + 15) := (isNum_iff _ _).mp hk
  subst ek
  have ew : w = pw (4 * r + 15) := H.fn _ _ _ hw (powH_num H _ (mem_sc.mpr (Or.inr hkθ)))
  subst ew
  have hno' : ¬VInj θ (pw (4 * r + 15) : V) := hno
  -- the least ordinal that does not map one-to-one into the last base set
  obtain ⟨ρ, hρ⟩ := next_exists (pw (4 * (r + 2) + 4) : V)
  have hρO : Ord ρ := ord_of_ordS hρ.1
  have hρinj : ∀ ζ : V, ζ ∈ ρ → VInj ζ (pw (4 * (r + 2) + 4) : V) := fun ζ hζ => hρ.2.2 ζ hζ
  have hart : ∀ ξ : V, Ord ξ → VInj ξ (pw (4 * (r + 2) + 4) : V) → ξ ∈ ρ := by
    intro ξ hξ hv
    rcases ord_tri hξ hρO with e | e | e
    · exact e
    · rw [e] at hv
      exact (hρ.2.1 hv).elim
    · exact (hρ.2.1 (vinj_dom_mono hv fun z hz => hξ.1 ρ e z hz)).elim
  -- the collapse of the pairs
  obtain ⟨F, lam, hlamO, hF, honto⟩ := lex_collapse hρO
  have hFfn : ∀ γ n v v', γ ∈ ρ → n ∈ (om : V) → Pr F (kp γ n) v → Pr F (kp γ n) v' →
      v = v' := by
    intro γ n v v' hγ hn h1 h2
    obtain ⟨v₀, -, -, hu, -⟩ := hF γ n hγ hn
    rw [hu v h1, hu v' h2]
  have key : ¬ θ ∈ lam := by
    intro hθl
    obtain ⟨α₀, k₀, hα₀, hk₀, hFθ⟩ := honto θ hθl
    obtain ⟨v, -, hv, -, hmem⟩ := hF α₀ k₀ hα₀ hk₀
    have e : θ = v := hFfn α₀ k₀ θ v hα₀ hk₀ hFθ hv
    rw [← e] at hmem
    have hsub : ∀ γ, γ ∈ sc α₀ → γ ∈ ρ := fun γ hγ => by
      rcases mem_sc.mp hγ with e' | e'
      · rw [e']
        exact hα₀
      · exact hρO.1 α₀ hα₀ γ e'
    have h1 : VInj θ (prodS (sc α₀) (om : V)) :=
      vinj_of_rel (prB.comp ![2, 1, 0]) θ (prodS (sc α₀) (om : V)) ![F]
        (fun y hy => by
          obtain ⟨γ', n', -, hn', hlt, hFy⟩ := (hmem y).mp hy
          refine ⟨kp γ' n', mem_prodS.mpr ⟨γ', ?_, n', hn', rfl⟩, hFy⟩
          rcases hlt with h' | ⟨h', -⟩
          · exact mem_sc.mpr (Or.inr h')
          · exact mem_sc.mpr (Or.inl h'))
        (fun y y' a _ _ ha k1 k2 => by
          obtain ⟨γ, hγ, n, hn, rfl⟩ := mem_prodS.mp ha
          exact hFfn γ n y y' (hsub γ hγ) hn k1 k2)
    have h2 : VInj (sc α₀) (℘ (pw (4 * (r + 2) + 4) : V)) := vinj_sc_pow (hρinj α₀ hα₀)
    have h3 : VInj θ (prodS (℘ (pw (4 * (r + 2) + 4) : V)) (om : V)) :=
      vinj_comp h1 (vinj_prod_left h2)
    have h4 : VInj θ (pw (4 * (r + 2) + 4 + 3) : V) :=
      vinj_mono h3 (prod_pw_sub (4 * (r + 2) + 4))
    have ec : 4 * (r + 2) + 4 + 3 = 4 * r + 15 := by omega
    rw [ec] at h4
    exact hno' h4
  have hlamθ : ∀ v, v ∈ lam → v ∈ θ := by
    intro v hv
    rcases ord_tri (ord_mem hlamO hv) hθ with e | e | e
    · exact e
    · rw [e] at hv
      exact absurd hv key
    · exact absurd (hlamO.1 v hv θ e) key
  -- the values of the collapse
  have fval : ∀ α, α ∈ ρ → ∀ n, n ∈ (om : V) → ∃ v, v ∈ θ ∧ Pr F (kp α n) v :=
    fun α hα n hn => by
      obtain ⟨v, hvl, hv, -⟩ := hF α n hα hn
      exact ⟨v, hlamθ v hvl, hv⟩
  have fsucc : ∀ α, α ∈ ρ → ∀ n, n ∈ (om : V) → ∀ v v', Pr F (kp α n) v →
      Pr F (kp α (sc n)) v' → v' = sc v := by
    intro α hα n hn v v' hv hv'
    obtain ⟨w, -, hw, -, hwm⟩ := hF α n hα hn
    obtain ⟨w', -, hw', -, hwm'⟩ := hF α (sc n) hα (sc_mem_om hn)
    have e := hFfn α n v w hα hn hv hw
    have e' := hFfn α (sc n) v' w' hα (sc_mem_om hn) hv' hw'
    rw [e, e']
    refine mem_ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨g, m, hg, hm, hlt, hFy⟩ := (hwm' y).mp hy
      rcases hlt with h' | ⟨rfl, h'⟩
      · exact mem_sc.mpr (Or.inr ((hwm y).mpr ⟨g, m, hg, hm, Or.inl h', hFy⟩))
      · rcases mem_sc.mp h' with rfl | h''
        · exact mem_sc.mpr (Or.inl (hFfn g m y w hg hm hFy hw))
        · exact mem_sc.mpr (Or.inr ((hwm y).mpr ⟨g, m, hg, hm, Or.inr ⟨rfl, h''⟩, hFy⟩))
    · rcases mem_sc.mp hy with rfl | hy'
      · exact (hwm' y).mpr ⟨α, n, hα, hn, Or.inr ⟨rfl, self_mem_sc n⟩, hw⟩
      · obtain ⟨g, m, hg, hm, hlt, hFy⟩ := (hwm y).mp hy'
        refine (hwm' y).mpr ⟨g, m, hg, hm, ?_, hFy⟩
        rcases hlt with h' | ⟨rfl, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨rfl, mem_sc.mpr (Or.inr h')⟩
  have fmono : ∀ α β, α ∈ β → β ∈ ρ → ∀ n n', n ∈ (om : V) → n' ∈ (om : V) → ∀ v v',
      Pr F (kp α n) v → Pr F (kp β n') v' → v ∈ v' := by
    intro α β hαβ hβ n n' hn hn' v v' hv hv'
    obtain ⟨w', -, hw', -, hwm'⟩ := hF β n' hβ hn'
    rw [hFfn β n' v' w' hβ hn' hv' hw']
    exact (hwm' v).mpr ⟨α, n, hρO.1 β hβ α hαβ, hn, Or.inl hαβ, hv⟩
  -- one step and four steps along the finite ordinals
  have step1 : ∀ α, α ∈ ρ → ∀ j : ℕ, ∀ v x, Pr F (kp α (nm j)) v → Pr h v x →
      Pr F (kp α (nm (j + 1))) (sc v) ∧ Pr h (sc v) (℘ x) := by
    intro α hα j v x hv hx
    obtain ⟨v₀, hv₀θ, hv₀⟩ := fval α hα (nm j) (nm_mem_om j)
    have e0 := hFfn α (nm j) v v₀ hα (nm_mem_om j) hv hv₀
    obtain ⟨v₁, -, hv₁⟩ := fval α hα (nm (j + 1)) (nm_mem_om (j + 1))
    have e1 : v₁ = sc v := fsucc α hα (nm j) (nm_mem_om j) v v₁ hv hv₁
    rw [e1] at hv₁
    rw [← e0] at hv₀θ
    exact ⟨hv₁, H.succ v x hv₀θ hx⟩
  have step4 : ∀ α, α ∈ ρ → ∀ j : ℕ, ∀ v x, Pr F (kp α (nm j)) v → Pr h v x →
      ∃ v' x', Pr F (kp α (nm (j + 4))) v' ∧ (Pr h v' x' ∧ SupRel x x') := by
    intro α hα j v x hv hx
    obtain ⟨a1, b1⟩ := step1 α hα j v x hv hx
    obtain ⟨a2, b2⟩ := step1 α hα (j + 1) _ _ a1 b1
    obtain ⟨a3, b3⟩ := step1 α hα (j + 2) _ _ a2 b2
    obtain ⟨a4, b4⟩ := step1 α hα (j + 3) _ _ a3 b3
    exact ⟨_, _, a4, b4, supRel_pow4 x⟩
  -- the value at `⟨α, j⟩` includes the `j`-th iterated power set of `ω`
  have low0 : ∀ α, α ∈ ρ → ∀ j : ℕ, ∀ v x, Pr F (kp α (nm j)) v → Pr h v x →
      ∀ z, z ∈ (pw j : V) → z ∈ x := by
    intro α hα j
    induction j with
    | zero =>
      intro v x hv hx z hz
      obtain ⟨v₀, hv₀θ, hv₀⟩ := fval α hα (nm 0) (nm_mem_om 0)
      have e0 := hFfn α (nm 0) v v₀ hα (nm_mem_om 0) hv hv₀
      rw [← e0] at hv₀θ
      rcases ord_tri ord_empty (ord_mem hθ hv₀θ) with e | e | e
      · exact powH_mono H (mem_sc.mpr (Or.inr hv₀θ)) e H.zero hx z hz
      · rw [← e] at hx
        rw [H.fn _ _ _ hx H.zero]
        exact hz
      · exact absurd e (by simp)
    | succ j ih =>
      intro v x hv hx z hz
      obtain ⟨v₀, hv₀θ, hv₀⟩ := fval α hα (nm j) (nm_mem_om j)
      obtain ⟨x₀, hx₀⟩ := H.tot v₀ (mem_sc.mpr (Or.inr hv₀θ))
      obtain ⟨a1, b1⟩ := step1 α hα j v₀ x₀ hv₀ hx₀
      have e1 := hFfn α (nm (j + 1)) v (sc v₀) hα (nm_mem_om (j + 1)) hv a1
      rw [e1] at hx
      rw [H.fn _ _ _ hx b1]
      exact mem_power_iff.mpr fun t ht => ih v₀ x₀ hv₀ hx₀ t (mem_power_iff.mp hz t ht)
  -- the sequence
  obtain ⟨hθv, hhθ⟩ := H.tot θ (self_mem_sc θ)
  have hcb : (nm (4 * (r + 2) + 4) : V) ∈ (om : V) := nm_mem_om _
  let Sq : V := relB sqRB ρ (℘ hθv) ![prodS ρ (om : V), nm (4 * (r + 2) + 4), θ, F, h]
  have hSq : ∀ α S, Pr Sq α S ↔
      α ∈ ρ ∧ ∃ v, v ∈ θ ∧ (Pr F (kp α (nm (4 * (r + 2) + 4))) v ∧ Pr h v S) := by
    intro α S
    have h0 := pr_relB sqRB ρ (℘ hθv) ![prodS ρ (om : V), nm (4 * (r + 2) + 4), θ, F, h] α S
    constructor
    · intro hh
      obtain ⟨hα, -, hs⟩ := h0.mp hh
      have hs' : SqR α S (prodS ρ (om : V)) (nm (4 * (r + 2) + 4)) θ F h := hs
      obtain ⟨a, -, hop, v, hv, hFa, hhv⟩ := hs'
      rw [isOp_iff.mp hop] at hFa
      exact ⟨hα, v, hv, hFa, hhv⟩
    · rintro ⟨hα, v, hv, hFa, hhv⟩
      refine h0.mpr ⟨hα, mem_power_iff.mpr (powH_mono H (self_mem_sc θ) hv hhv hhθ), ?_⟩
      show SqR α S (prodS ρ (om : V)) (nm (4 * (r + 2) + 4)) θ F h
      exact ⟨kp α (nm (4 * (r + 2) + 4)), mem_prodS.mpr ⟨α, hα, _, hcb, rfl⟩, isOp_kp _ _,
        v, hv, hFa, hhv⟩
  refine ⟨ρ, Sq, ⟨fun j _ => pw_base (4 * j), fun j _ => ?_, hρO, hart, ?_, ?_, ?_, ?_⟩⟩
  · have e : 4 * (j + 1) + 4 = 4 * j + 4 + 4 := by omega
    show SupRel (pw (4 * j + 4) : V) (pw (4 * (j + 1) + 4))
    rw [e]
    exact pw_supRel (4 * j + 4)
  · intro α hα
    obtain ⟨v, hvθ, hv⟩ := fval α hα _ hcb
    obtain ⟨x, hx⟩ := H.tot v (mem_sc.mpr (Or.inr hvθ))
    exact ⟨x, (hSq α x).mpr ⟨hα, v, hvθ, hv, hx⟩⟩
  · intro α S hα hS
    obtain ⟨-, v, -, hv, hx⟩ := (hSq α S).mp hS
    exact ⟨vinj_mono (pw_base (4 * (r + 2))).om (low0 α hα _ v S hv hx)⟩
  · intro α S hα hS
    obtain ⟨-, v, -, hv, hx⟩ := (hSq α S).mp hS
    exact low0 α hα _ v S hv hx
  · intro α β S S' hαβ hβ hS hS'
    have hα : α ∈ ρ := hρO.1 β hβ α hαβ
    obtain ⟨-, v, -, hv, hx⟩ := (hSq α S).mp hS
    obtain ⟨-, v', hv'θ, hv', hx'⟩ := (hSq β S').mp hS'
    have hv's : v' ∈ sc θ := mem_sc.mpr (Or.inr hv'θ)
    obtain ⟨v₄, x₄, a4, b4, s4⟩ := step4 α hα _ v S hv hx
    obtain ⟨v₈, x₈, a8, b8, s8⟩ := step4 α hα _ v₄ x₄ a4 b4
    have h8 : v₈ ∈ v' := fmono α β hαβ hβ _ _ (nm_mem_om _) hcb v₈ v' a8 hv'
    exact ⟨powH_mono H hv's (fmono α β hαβ hβ _ _ hcb hcb v v' hv hv') hx hx',
      x₄, s4, supRel_mono s8 (fun _ hz => hz) (powH_mono H hv's h8 b8 hx')⟩

end supply

end MH

/-- **If `𝗠𝗛` with the rank axioms is consistent, then NF with the Axiom of Counting is
consistent.** A model of `𝗠𝗛𝗥` has a supply of sets for every radius (`MH.supply_of_rank`), so
the consistency follows by `MH.consistent_nfc_of_supplies`. -/
theorem consistent_nfc_of_consistent_mhr (h : Entailment.Consistent 𝗠𝗛𝗥) :
    Entailment.Consistent 𝗡𝗙𝗖 := by
  by_contra hU
  refine Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable ?_) h
  apply SetTheory.complete.{0}
  intro M _ _ hTR
  exfalso
  apply hU
  have hMH : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := mhr_models_mh
  exact MH.consistent_nfc_of_supplies fun q => by
    obtain ⟨ρ, Sq, sup⟩ := MH.supply_of_rank (V := M) _ (mhr_rank _)
    exact ⟨M, inferInstance, inferInstance, hMH, _, ρ, Sq, sup⟩

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.supply_of_rank
#print axioms FFL.FirstOrder.SetTheory.consistent_nfc_of_consistent_mhr
