module

public import MHRankSupply

@[expose] public section

set_option autoImplicit false

/-!
# Hartogs' ordinal maps one-to-one into an iterated power set

In a model of `𝗠𝗛`. Let `ρ` be the least ordinal that does not map one-to-one into `X`
(`NextS X ρ`). **`hart_inj`**: `ρ` maps one-to-one into `℘℘(℘X × ℘X)`.

A member `ξ` of `ρ` is sent to the set of the relations `R` on `℘X` that are the image of the
order `≤` of `ξ` under a one-to-one function from `ξ` to `℘X`. There is such a function: a
one-to-one relation `f` from `ξ` into `X` gives the function `a ↦ {x ∈ X | f(a, x)}`. Two
ordinals with a common image are equal (`rigid_ord`): the two functions give an isomorphism of
the orders, which is the identity by induction.

No choice is made, which is why the values are in `℘X` and not in `X`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

section defs

variable {V : Type} [SetStructure V]

/-- `g` is a one-to-one function from `ξ` to `Y`. -/
def FunInj (g ξ Y : V) : Prop :=
  (∀ a, a ∈ ξ → ∃ y, y ∈ Y ∧ Pr g a y) ∧
  ((∀ a, a ∈ ξ → ∀ y, y ∈ Y → ∀ y', y' ∈ Y → (Pr g a y → (Pr g a y' → y = y'))) ∧
  (∀ a, a ∈ ξ → ∀ a', a' ∈ ξ → ∀ y, y ∈ Y → (Pr g a y → (Pr g a' y → a = a'))))

/-- `x` and `y` are the values of `g` at some `a ≤ b` in `ξ`. -/
def RO (x y ξ g : V) : Prop :=
  ∃ a, a ∈ ξ ∧ ∃ b, b ∈ ξ ∧ ((a ∈ b ∨ a = b) ∧ (Pr g a x ∧ Pr g b y))

/-- On `Y`, the relation `R` is the image of the order of `ξ` under `g`. -/
def ROf (g ξ Y R : V) : Prop := ∀ x, x ∈ Y → ∀ y, y ∈ Y → (Pr R x y ↔ RO x y ξ g)

/-- `y` is the set of the members `x` of `X` with `f(a, x)`. -/
def ImgS (a y X f : V) : Prop :=
  (∀ x, x ∈ y → (x ∈ X ∧ Pr f a x)) ∧ ∀ x, x ∈ X → (Pr f a x → x ∈ y)

/-- `w` is the set of the relations in `P` that are images of the order of `ξ`. -/
def HartG (ξ w P PF Y : V) : Prop :=
  ∀ R, R ∈ P → (R ∈ w ↔ ∃ g, g ∈ PF ∧ (FunInj g ξ Y ∧ ROf g ξ Y R))

end defs

def funInjB : BDef (k := 3) (fun V _ v ↦ FunInj (v 0) (v 1) (v 2)) :=
  ((BDef.ball 1 (BDef.bex 3 (prB.comp ![2, 1, 0]))).and
    ((BDef.ball 1 (BDef.ball 3 (BDef.ball 4 ((prB.comp ![3, 2, 1]).imp
      ((prB.comp ![3, 2, 0]).imp (BDef.eq 1 0)))))).and
    (BDef.ball 1 (BDef.ball 2 (BDef.ball 4 ((prB.comp ![3, 2, 0]).imp
      ((prB.comp ![3, 1, 0]).imp (BDef.eq 2 1)))))))).congr fun _ _ _ => Iff.rfl

def roB : BDef (k := 4) (fun V _ v ↦ RO (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 2 (BDef.bex 3 (((BDef.mem 1 0).or (BDef.eq 1 0)).and
    ((prB.comp ![5, 1, 2]).and (prB.comp ![5, 0, 3]))))).congr fun _ _ _ => Iff.rfl

def rOfB : BDef (k := 4) (fun V _ v ↦ ROf (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.ball 2 (BDef.ball 3 ((prB.comp ![5, 1, 0]).iff (roB.comp ![1, 0, 3, 2])))).congr
    fun _ _ _ => Iff.rfl

def imgSB : BDef (k := 4) (fun V _ v ↦ ImgS (v 0) (v 1) (v 2) (v 3)) :=
  ((BDef.ball 1 ((BDef.mem 0 3).and (prB.comp ![4, 1, 0]))).and
    (BDef.ball 2 ((prB.comp ![4, 1, 0]).imp (BDef.mem 0 2)))).congr fun _ _ _ => Iff.rfl

def hartGB : BDef (k := 5) (fun V _ v ↦ HartG (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.ball 2 ((BDef.mem 0 2).iff (BDef.bex 4 ((funInjB.comp ![0, 2, 6]).and
    (rOfB.comp ![0, 2, 6, 1]))))).congr fun _ _ _ => Iff.rfl

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **Two ordinals whose orders have a common image under one-to-one functions are equal.** -/
theorem rigid_ord {ξ ξ' Y g g' R : V} (hξ : Ord ξ) (hξ' : Ord ξ') (hg : FunInj g ξ Y)
    (hg' : FunInj g' ξ' Y) (hR : ROf g ξ Y R) (hR' : ROf g' ξ' Y R) : ξ = ξ' := by
  let e : V := relB (k := 3) (BDef.bex 2 ((prB.comp ![4, 1, 0]).and (prB.comp ![5, 2, 0])))
    ξ ξ' ![Y, g, g']
  have he : ∀ a a', Pr e a a' ↔ a ∈ ξ ∧ a' ∈ ξ' ∧ ∃ y, y ∈ Y ∧ (Pr g a y ∧ Pr g' a' y) :=
    fun a a' => pr_relB _ ξ ξ' ![Y, g, g'] a a'
  have le_tr : ∀ a b a' b', Pr e a a' → Pr e b b' →
      ((a ∈ b ∨ a = b) ↔ (a' ∈ b' ∨ a' = b')) := by
    intro a b a' b' h1 h2
    obtain ⟨ha, ha', y, hy, gy, gy'⟩ := (he a a').mp h1
    obtain ⟨hb, hb', z, hz, gz, gz'⟩ := (he b b').mp h2
    constructor
    · intro h
      obtain ⟨c, hc, d, hd, hcd, k1, k2⟩ :=
        (hR' y hy z hz).mp ((hR y hy z hz).mpr ⟨a, ha, b, hb, h, gy, gz⟩)
      rw [hg'.2.2 c hc a' ha' y hy k1 gy', hg'.2.2 d hd b' hb' z hz k2 gz'] at hcd
      exact hcd
    · intro h
      obtain ⟨c, hc, d, hd, hcd, k1, k2⟩ :=
        (hR y hy z hz).mp ((hR' y hy z hz).mpr ⟨a', ha', b', hb', h, gy', gz'⟩)
      rw [hg.2.2 c hc a ha y hy k1 gy, hg.2.2 d hd b hb z hz k2 gz] at hcd
      exact hcd
  have e_tot : ∀ a, a ∈ ξ → ∃ a', Pr e a a' := by
    intro a ha
    obtain ⟨y, hy, gy⟩ := hg.1 a ha
    obtain ⟨c, hc, d, -, -, k1, -⟩ :=
      (hR' y hy y hy).mp ((hR y hy y hy).mpr ⟨a, ha, a, ha, Or.inr rfl, gy, gy⟩)
    exact ⟨c, (he a c).mpr ⟨ha, hc, y, hy, gy, k1⟩⟩
  have e_sur : ∀ a', a' ∈ ξ' → ∃ a, Pr e a a' := by
    intro a' ha'
    obtain ⟨y, hy, gy'⟩ := hg'.1 a' ha'
    obtain ⟨c, hc, d, -, -, k1, -⟩ :=
      (hR y hy y hy).mp ((hR' y hy y hy).mpr ⟨a', ha', a', ha', Or.inr rfl, gy', gy'⟩)
    exact ⟨c, (he c a').mpr ⟨hc, ha', y, hy, k1, gy'⟩⟩
  have e_fun : ∀ a a' a'', Pr e a a' → Pr e a a'' → a' = a'' := by
    intro a a' a'' h1 h2
    obtain ⟨ha, ha', y, hy, gy, gy'⟩ := (he a a').mp h1
    obtain ⟨-, ha'', z, hz, gz, gz'⟩ := (he a a'').mp h2
    rw [← hg.2.1 a ha y hy z hz gy gz] at gz'
    exact hg'.2.2 a' ha' a'' ha'' y hy gy' gz'
  have e_inj : ∀ a b a', Pr e a a' → Pr e b a' → a = b := by
    intro a b a' h1 h2
    obtain ⟨ha, ha', y, hy, gy, gy'⟩ := (he a a').mp h1
    obtain ⟨hb, -, z, hz, gz, gz'⟩ := (he b a').mp h2
    rw [← hg'.2.1 a' ha' y hy z hz gy' gz'] at gz
    exact hg.2.2 a ha b hb y hy gy gz
  have key0 := ord_ind (BDef.ball 1 (BDef.ball 0 (BDef.ball 0 ((isOpB.comp ![2, 3, 0]).imp
    (BDef.eq 0 3))))) ![e] hξ (fun a ha ih => by
      show ∀ q, q ∈ e → ∀ u, u ∈ q → ∀ a', a' ∈ u → (IsOp q a a' → a' = a)
      have ih' : ∀ b, b ∈ a → ∀ b', Pr e b b' → b' = b := fun b hb b' hb' => by
        obtain ⟨q, hq, hop⟩ := hb'
        obtain ⟨u, hu, hbu⟩ := pr_snd_mem hop
        exact ih b hb q hq u hu b' hbu hop
      intro q hq u _ a' _ hop
      have hea : Pr e a a' := ⟨q, hq, hop⟩
      obtain ⟨-, ha'ξ', -⟩ := (he a a').mp hea
      refine mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
      · obtain ⟨b, hb⟩ := e_sur z (hξ'.1 a' ha'ξ' z hz)
        rcases (le_tr b a z a' hb hea).mpr (Or.inl hz) with h1 | h1
        · rw [ih' b h1 z hb]
          exact h1
        · rw [h1] at hb
          rw [e_fun a z a' hb hea] at hz
          exact absurd hz (mem_irrefl _)
      · obtain ⟨z', hz'⟩ := e_tot z (hξ.1 a ha z hz)
        rw [ih' z hz z' hz'] at hz'
        rcases (le_tr z a z a' hz' hea).mp (Or.inl hz) with h1 | h1
        · exact h1
        · have hz'' : Pr e z a' := by
            rw [← h1]
            exact hz'
          rw [e_inj z a a' hz'' hea] at hz
          exact absurd hz (mem_irrefl _))
  have key : ∀ a, a ∈ ξ → ∀ a', Pr e a a' → a' = a := fun a ha a' ha' => by
    obtain ⟨q, hq, hop⟩ := ha'
    obtain ⟨u, hu, hau⟩ := pr_snd_mem hop
    exact key0 a ha q hq u hu a' hau hop
  refine mem_ext fun a => ⟨fun ha => ?_, fun ha' => ?_⟩
  · obtain ⟨a', ha'⟩ := e_tot a ha
    rw [key a ha a' ha'] at ha'
    exact ((he a a).mp ha').2.1
  · obtain ⟨b, hb⟩ := e_sur a ha'
    have hbξ := ((he b a).mp hb).1
    rw [key b hbξ a hb]
    exact hbξ

/-- **Hartogs' ordinal of `X` maps one-to-one into `℘℘(℘X × ℘X)`.** -/
theorem hart_inj {X ρ : V} (hρ : NextS X ρ) :
    VInj ρ (℘ (℘ (prodS (℘ X) (℘ X)))) := by
  have hρO : Ord ρ := ord_of_ordS hρ.1
  refine vinj_of_rel hartGB ρ (℘ (℘ (prodS (℘ X) (℘ X))))
    ![℘ (prodS (℘ X) (℘ X)), ℘ (prodS ρ (℘ X)), ℘ X] (fun ξ _ => ?_)
    (fun ξ ξ' w hξ hξ' _ h1 h2 => ?_)
  · let w : V := sepB (k := 3) (BDef.bex 2 ((funInjB.comp ![0, 2, 4]).and
      (rOfB.comp ![0, 2, 4, 1]))) (℘ (prodS (℘ X) (℘ X))) ![ξ, ℘ (prodS ρ (℘ X)), ℘ X]
    have hw : ∀ R, R ∈ w ↔ R ∈ ℘ (prodS (℘ X) (℘ X)) ∧
        ∃ g, g ∈ ℘ (prodS ρ (℘ X)) ∧ (FunInj g ξ (℘ X) ∧ ROf g ξ (℘ X) R) :=
      fun R => mem_sepB _ _ _ R
    refine ⟨w, mem_power_iff.mpr fun R hR => ((hw R).mp hR).1, ?_⟩
    show HartG ξ w (℘ (prodS (℘ X) (℘ X))) (℘ (prodS ρ (℘ X))) (℘ X)
    exact fun R hR => ⟨fun h => ((hw R).mp h).2, fun h => (hw R).mpr ⟨hR, h⟩⟩
  · have h1' : HartG ξ w (℘ (prodS (℘ X) (℘ X))) (℘ (prodS ρ (℘ X))) (℘ X) := h1
    have h2' : HartG ξ' w (℘ (prodS (℘ X) (℘ X))) (℘ (prodS ρ (℘ X))) (℘ X) := h2
    obtain ⟨f, hf1, hf2⟩ := hρ.2.2 ξ hξ
    -- the function `a ↦ {x ∈ X | f(a, x)}`
    let g : V := relB (k := 2) imgSB ξ (℘ X) ![X, f]
    have hg : ∀ a y, Pr g a y ↔ a ∈ ξ ∧ y ∈ ℘ X ∧ ImgS a y X f :=
      fun a y => pr_relB imgSB ξ (℘ X) ![X, f] a y
    have hgF : FunInj g ξ (℘ X) := by
      refine ⟨fun a ha => ?_, fun a _ y _ y' _ k k' => ?_, fun a ha a' ha' y _ k k' => ?_⟩
      · let y : V := sepB (k := 2) (prB.comp ![2, 1, 0]) X ![a, f]
        have hy : ∀ x, x ∈ y ↔ x ∈ X ∧ Pr f a x := fun x => mem_sepB _ _ _ x
        have hyY : y ∈ ℘ X := mem_power_iff.mpr fun x hx => ((hy x).mp hx).1
        exact ⟨y, hyY, (hg a y).mpr ⟨ha, hyY, fun x hx => (hy x).mp hx,
          fun x hx hp => (hy x).mpr ⟨hx, hp⟩⟩⟩
      · obtain ⟨-, -, i1, i2⟩ := (hg a y).mp k
        obtain ⟨-, -, j1, j2⟩ := (hg a y').mp k'
        exact mem_ext fun x => ⟨fun hx => j2 x (i1 x hx).1 (i1 x hx).2,
          fun hx => i2 x (j1 x hx).1 (j1 x hx).2⟩
      · obtain ⟨-, -, -, i2⟩ := (hg a y).mp k
        obtain ⟨-, -, j1, -⟩ := (hg a' y).mp k'
        obtain ⟨x₀, hx₀, hr⟩ := hf1 a ha
        have hx₀y : x₀ ∈ y := i2 x₀ hx₀ (pr_iff.mpr (hin_rl_iff.mp hr))
        exact hf2 a a' x₀ ha ha' hr (hin_rl_iff.mpr (pr_iff.mp (j1 x₀ hx₀y).2))
    have hgPF : g ∈ ℘ (prodS ρ (℘ X)) := mem_power_iff.mpr fun z hz => by
      obtain ⟨a, ha, y, hy, e⟩ := mem_prodS.mp (relB_sub imgSB ξ (℘ X) ![X, f] hz)
      exact mem_prodS.mpr ⟨a, hρO.1 ξ hξ a ha, y, hy, e⟩
    -- the image of the order of `ξ`
    let R₀ : V := relB (k := 2) roB (℘ X) (℘ X) ![ξ, g]
    have hR₀ : ROf g ξ (℘ X) R₀ := fun x hx y hy =>
      (pr_relB roB (℘ X) (℘ X) ![ξ, g] x y).trans ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩
    have hR₀P : R₀ ∈ ℘ (prodS (℘ X) (℘ X)) :=
      mem_power_iff.mpr fun z hz => relB_sub roB (℘ X) (℘ X) ![ξ, g] hz
    obtain ⟨g', -, hg'F, hR'⟩ := (h2' R₀ hR₀P).mp ((h1' R₀ hR₀P).mpr ⟨g, hgPF, hgF, hR₀⟩)
    exact rigid_ord (ord_mem hρO hξ) (ord_mem hρO hξ') hgF hg'F hR₀ hR'

/-- Hartogs' ordinal of `pw n` maps one-to-one into `pw (n + 5)`. -/
theorem hart_pw {n : ℕ} {ρ : V} (hρ : NextS (pw n : V) ρ) : VInj ρ (pw (n + 5) : V) := by
  refine vinj_mono (hart_inj hρ) fun C hC => ?_
  show C ∈ ℘ (℘ (pw (n + 3) : V))
  refine mem_power_iff.mpr fun R hR => mem_power_iff.mpr fun p hp => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prodS.mp (mem_power_iff.mp (mem_power_iff.mp hC R hR) p hp)
  show kp x y ∈ ℘ (℘ (pw (n + 1) : V))
  refine mem_power_iff.mpr fun s hs => mem_power_iff.mpr fun t ht => ?_
  rcases (by simpa [kp] using hs : s = {x} ∨ s = {x, y}) with rfl | rfl
  · rw [show t = x by simpa using ht]
    exact hx
  · rcases (by simpa using ht : t = x ∨ t = y) with rfl | rfl
    · exact hx
    · exact hy

end model

end MH

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.hart_inj
