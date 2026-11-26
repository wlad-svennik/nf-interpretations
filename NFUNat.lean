module

public import NFUBF
public import CountAxioms

@[expose] public section

set_option autoImplicit false

/-!
# Frege's natural numbers in a model of `𝗡𝗙𝗨𝗜`, in terms of membership

The natural numbers of `CountAxioms.lean` (`JensenNFU.IsZeroN`, `IsSuccN`, `IsNatN`), which are
written with membership only, in a model of Jensen's NFU + Infinity. Everything is proved with
stratified comprehension (`SDef.comprehensionU`) and extensionality for objects with a member.

* `zeroND`, `succND`, `natND`: stratified definitions.
* `natN_ind`: induction for every relation with a stratified definition.
* `natN_nonempty`, `natN_mem_omit`: every natural number has a member, and no member of a
  natural number is the universe. This is the axiom of Infinity.
* `natN_rem`: removing an element from a member of `n + 1` gives a member of `n`.
* `succN_inj`, `zero_not_succ`, `natN_cases`.
-/

namespace FFL.FirstOrder.SetTheory

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD)

/-! ### Definitions -/

section defs

variable {V : Type} [SetStructure V]

/-- `z` is Frege's zero: its members are the objects without members. -/
def ZeroN (z : V) : Prop := JensenNFU.IsZeroN (fun a b : V => a ∈ b) z

/-- `k'` is the successor of `k`. -/
def SuccN (k k' : V) : Prop := JensenNFU.IsSuccN (fun a b : V => a ∈ b) k k'

/-- `n` is a natural number. -/
def NatN (n : V) : Prop := JensenNFU.IsNatN (fun a b : V => a ∈ b) n

end defs

section sdefs

def zeroND : SDef ![2] (fun _ _ v ↦ ZeroN (v 0)) :=
  (SDef.all 1 ((SDef.mem 0 1).iff (SDef.all 0 (SDef.mem 0 1).not))).congr fun _ _ _ => Iff.rfl

def succND : SDef ![2, 2] (fun _ _ v ↦ SuccN (v 0) (v 1)) :=
  (SDef.all 1 ((SDef.mem 0 2).iff (SDef.ex 1 ((SDef.mem 0 2).and (SDef.ex 0
    ((SDef.mem 0 1).not.and
      (SDef.all 0 ((SDef.mem 0 3).iff ((SDef.mem 0 2).or (SDef.eq 0 1)))))))))).congr
    fun _ _ _ => Iff.rfl

def natND : SDef ![2] (fun _ _ v ↦ NatN (v 0)) :=
  (SDef.all 3 (((SDef.all 2 ((zeroND.comp ![0] 0).imp (SDef.mem 0 1))).and
    (SDef.all 2 ((SDef.mem 0 1).imp (SDef.all 2 ((succND.comp ![1, 0] 0).imp
      (SDef.mem 0 2)))))).imp (SDef.mem 1 0))).congr fun _ _ _ => Iff.rfl

end sdefs

/-! ### In a model of `𝗡𝗙𝗨𝗜` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hT : V↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

theorem exists_zeroN : ∃ z : V, ZeroN z :=
  (SDef.all (τ := ![1]) 0 (SDef.mem 0 1).not).comprehensionU (![] : Fin 0 → V)

theorem zeroN_unique {z z' : V} (h : ZeroN z) (h' : ZeroN z') : z = z' := by
  obtain ⟨e, he⟩ := exists_empty (V := V)
  exact nfu_ext ⟨e, (h e).mpr he⟩ fun x => (h x).trans (h' x).symm

omit [Nonempty V] hT in
theorem natN_zero {z : V} (hz : ZeroN z) : NatN z := fun _ h => h.1 z hz

omit [Nonempty V] hT in
theorem natN_succ {n n' : V} (hn : NatN n) (h : SuccN n n') : NatN n' :=
  fun F hF => hF.2 n (hn F hF) n' h

/-- **Induction on the natural numbers**, for a relation with a stratified definition. The
induction step may use that the number is a natural number. -/
theorem natN_ind (c : ℕ) {k : ℕ} {τ : Fin k → ℕ} {R : URel (k + 1)} (d : SDef ((2 + c) :> τ) R)
    (p : Fin k → V) (h0 : ∀ z, ZeroN z → R V (z :> p))
    (h1 : ∀ n, NatN n → R V (n :> p) → ∀ n', SuccN n n' → R V (n' :> p)) :
    ∀ n, NatN n → R V (n :> p) := by
  have hf : ∀ i, ((2 + c) :> τ) (![0] i) = ![2] i + c := by intro i; fin_cases i; rfl
  obtain ⟨Y, hY⟩ := ((natND.comp (τ' := (2 + c) :> τ) ![0] c hf).and d).comprehensionU p
  have hY' : ∀ x, x ∈ Y ↔ NatN x ∧ R V (x :> p) := hY
  exact fun n hn => ((hY' n).mp (hn Y ⟨fun z hz => (hY' z).mpr ⟨natN_zero hz, h0 z hz⟩,
    fun m hm m' hm' => (hY' m').mpr ⟨natN_succ ((hY' m).mp hm).1 hm',
      h1 m ((hY' m).mp hm).1 ((hY' m).mp hm).2 m' hm'⟩⟩)).2

theorem exists_adj (s b : V) : ∃ s' : V, ∀ z, z ∈ s' ↔ z ∈ s ∨ z = b :=
  ((SDef.mem (τ := ![0, 1, 0]) 0 1).or (SDef.eq 0 2)).comprehensionU ![s, b]

theorem exists_rem (s c : V) : ∃ s' : V, ∀ z, z ∈ s' ↔ z ∈ s ∧ ¬ z = c :=
  ((SDef.mem (τ := ![0, 1, 0]) 0 1).and (SDef.eq 0 2).not).comprehensionU ![s, c]

theorem exists_succN (k : V) : ∃ k' : V, SuccN k k' :=
  (SDef.ex (τ := ![1, 2]) 1 ((SDef.mem 0 2).and (SDef.ex 0
    ((SDef.mem 0 1).not.and
      (SDef.all 0 ((SDef.mem 0 3).iff ((SDef.mem 0 2).or (SDef.eq 0 1)))))))).comprehensionU ![k]

/-- The members of the natural numbers belong to every family that contains the objects
without members and is closed under adjoining one element; and every natural number has a
member, if no such family contains the universe. -/
theorem natN_fin {F : V} (h1 : ∀ e : V, (∀ z, z ∉ e) → e ∈ F)
    (h2 : ∀ s ∈ F, ∀ b s' : V, (∀ z, z ∈ s' ↔ z ∈ s ∨ z = b) → s' ∈ F)
    (h3 : ∀ u : V, (∀ z, z ∈ u) → u ∉ F) :
    ∀ n : V, NatN n → (∃ x, x ∈ n) ∧ ∀ x, x ∈ n → x ∈ F := by
  refine natN_ind 0 ((SDef.ex (τ := ![2, 2]) 1 (SDef.mem 0 1)).and
    (SDef.all 1 ((SDef.mem 0 1).imp (SDef.mem 0 2)))) ![F] (fun z hz => ?_)
    (fun n _ ih n' hs => ?_)
  · show (∃ x, x ∈ z) ∧ ∀ x, x ∈ z → x ∈ F
    obtain ⟨e, he⟩ := exists_empty (V := V)
    exact ⟨⟨e, (hz e).mpr he⟩, fun x hx => h1 x ((hz x).mp hx)⟩
  · show (∃ x, x ∈ n') ∧ ∀ x, x ∈ n' → x ∈ F
    have ih' : (∃ x, x ∈ n) ∧ ∀ x, x ∈ n → x ∈ F := ih
    obtain ⟨⟨x, hx⟩, hall⟩ := ih'
    have hb : ∃ b, b ∉ x := by
      by_contra hn'
      exact h3 x (fun z => by by_contra hz; exact hn' ⟨z, hz⟩) (hall x hx)
    obtain ⟨b, hb⟩ := hb
    obtain ⟨x', hx'⟩ := exists_adj x b
    refine ⟨⟨x', (hs x').mpr ⟨x, hx, b, hb, hx'⟩⟩, fun y hy => ?_⟩
    obtain ⟨x₀, hx₀, b₀, -, hy'⟩ := (hs y).mp hy
    exact h2 x₀ (hall x₀ hx₀) b₀ y hy'

/-- **Every natural number has a member.** -/
theorem natN_nonempty {n : V} (hn : NatN n) : ∃ x, x ∈ n := by
  obtain ⟨F, h1, h2, h3⟩ := nfui_infinite (V := V)
  exact (natN_fin h1 h2 h3 n hn).1

/-- **No member of a natural number is the universe.** -/
theorem natN_mem_omit {n x : V} (hn : NatN n) (hx : x ∈ n) : ∃ b, b ∉ x := by
  obtain ⟨F, h1, h2, h3⟩ := nfui_infinite (V := V)
  by_contra h
  exact h3 x (fun z => by by_contra hz; exact h ⟨z, hz⟩) ((natN_fin h1 h2 h3 n hn).2 x hx)

theorem succN_nonempty {k k' : V} (hk : NatN k) (h : SuccN k k') : ∃ y, y ∈ k' := by
  obtain ⟨x, hx⟩ := natN_nonempty hk
  obtain ⟨b, hb⟩ := natN_mem_omit hk hx
  obtain ⟨x', hx'⟩ := exists_adj x b
  exact ⟨x', (h x').mpr ⟨x, hx, b, hb, hx'⟩⟩

theorem succN_unique {k n n' : V} (hk : NatN k) (h : SuccN k n) (h' : SuccN k n') : n = n' :=
  nfu_ext (succN_nonempty hk h) fun y => (h y).trans (h' y).symm

/-- Zero is not a successor. -/
theorem zero_not_succ {z k : V} (hz : ZeroN z) (h : SuccN k z) : False := by
  obtain ⟨e, he⟩ := exists_empty (V := V)
  obtain ⟨x, -, b, -, hb⟩ := (h e).mp ((hz e).mpr he)
  exact he b ((hb b).mpr (Or.inr rfl))

/-- **Removing an element from a member of `m + 1` gives a member of `m`.** -/
theorem natN_rem {m m' y' y c : V} (hm : NatN m) (hs : SuccN m m') (hy' : y' ∈ m') (hc : c ∈ y')
    (hy : ∀ z, z ∈ y ↔ z ∈ y' ∧ ¬ z = c) : y ∈ m := by
  have key := natN_ind 0 (SDef.all (τ := ![2]) 2 (SDef.all 1 (SDef.all 1 (SDef.all 0
    ((succND.comp ![4, 3] 0).imp ((SDef.mem 2 3).imp ((SDef.mem 0 2).imp
      ((SDef.all 0 ((SDef.mem 0 2).iff ((SDef.mem 0 3).and (SDef.eq 0 1).not))).imp
        (SDef.mem 1 4)))))))))
    (![] : Fin 0 → V) (fun z hz => ?_) (fun n _ ih n' hs0 => ?_) m hm
  · exact key m' y' y c hs hy' hc hy
  · show ∀ m' y' y c : V, SuccN z m' → y' ∈ m' → c ∈ y' → (∀ w, w ∈ y ↔ w ∈ y' ∧ ¬ w = c) → y ∈ z
    intro m' y' y c hs hy' hc hy
    obtain ⟨x, hx, b, -, hxy⟩ := (hs y').mp hy'
    have hx0 : ∀ w, ¬ w ∈ x := (hz x).mp hx
    have hcb : c = b := ((hxy c).mp hc).resolve_left (hx0 c)
    refine (hz y).mpr fun w hw => ?_
    obtain ⟨hw1, hw2⟩ := (hy w).mp hw
    rcases (hxy w).mp hw1 with h | h
    · exact hx0 w h
    · exact hw2 (h.trans hcb.symm)
  · show ∀ m' y' y c : V, SuccN n' m' → y' ∈ m' → c ∈ y' → (∀ w, w ∈ y ↔ w ∈ y' ∧ ¬ w = c) →
      y ∈ n'
    have ih' : ∀ m' y' y c : V, SuccN n m' → y' ∈ m' → c ∈ y' →
        (∀ w, w ∈ y ↔ w ∈ y' ∧ ¬ w = c) → y ∈ n := ih
    intro m' y' y c hs hy' hc hy
    obtain ⟨x, hx, b, hb, hxy⟩ := (hs y').mp hy'
    by_cases hcb : c = b
    · have hyx : ∀ w, w ∈ x ↔ w ∈ y := fun w =>
        ⟨fun hw => (hy w).mpr ⟨(hxy w).mpr (Or.inl hw), fun e => hb (by rw [← hcb, ← e]; exact hw)⟩,
          fun hw => ((hxy w).mp ((hy w).mp hw).1).resolve_right
            fun e => ((hy w).mp hw).2 (e.trans hcb.symm)⟩
      obtain ⟨x₀, -, b₀, -, hx₀⟩ := (hs0 x).mp hx
      have e : x = y := nfu_ext ⟨b₀, (hx₀ b₀).mpr (Or.inr rfl)⟩ hyx
      exact e ▸ hx
    · have hcx : c ∈ x := ((hxy c).mp hc).resolve_right hcb
      obtain ⟨x₁, hx₁⟩ := exists_rem x c
      have hx₁n : x₁ ∈ n := ih' n' x x₁ c hs0 hx hcx hx₁
      refine (hs0 y).mpr ⟨x₁, hx₁n, b, fun hbx => hb ((hx₁ b).mp hbx).1, fun w => ?_⟩
      show w ∈ y ↔ w ∈ x₁ ∨ w = b
      have h1 : w ∈ y' ↔ w ∈ x ∨ w = b := hxy w
      constructor
      · intro hw
        obtain ⟨hw1, hne⟩ := (hy w).mp hw
        rcases h1.mp hw1 with h | h
        · exact Or.inl ((hx₁ w).mpr ⟨h, hne⟩)
        · exact Or.inr h
      · rintro (h | h)
        · obtain ⟨h', hne⟩ := (hx₁ w).mp h
          exact (hy w).mpr ⟨h1.mpr (Or.inl h'), hne⟩
        · exact (hy w).mpr ⟨h1.mpr (Or.inr h), fun e => hcb (e.symm.trans h)⟩

/-- **The successor is one-to-one on the natural numbers.** -/
theorem succN_inj {n k s : V} (hn : NatN n) (hk : NatN k) (h1 : SuccN n s) (h2 : SuccN k s) :
    n = k := by
  have key : ∀ {n k : V}, NatN n → NatN k → SuccN n s → SuccN k s → ∀ x, x ∈ n → x ∈ k := by
    intro n k hn hk h1 h2 x hx
    obtain ⟨b, hb⟩ := natN_mem_omit hn hx
    obtain ⟨x', hx'⟩ := exists_adj x b
    have hx's : x' ∈ s := (h1 x').mpr ⟨x, hx, b, hb, hx'⟩
    exact natN_rem hk h2 hx's ((hx' b).mpr (Or.inr rfl)) fun z =>
      ⟨fun hz => ⟨(hx' z).mpr (Or.inl hz), fun e => hb (e ▸ hz)⟩,
        fun hz => ((hx' z).mp hz.1).resolve_right hz.2⟩
  exact nfu_ext (natN_nonempty hn) fun x => ⟨key hn hk h1 h2 x, key hk hn h2 h1 x⟩

/-- A natural number is zero or the successor of a natural number. -/
theorem natN_cases {n : V} (hn : NatN n) : ZeroN n ∨ ∃ k, NatN k ∧ SuccN k n :=
  natN_ind 0 ((zeroND.comp (τ' := ![2]) ![0] 0).or
    (SDef.ex 2 ((natND.comp ![0] 0).and (succND.comp ![0, 1] 0))))
    (![] : Fin 0 → V) (fun _ hz => Or.inl hz) (fun m hm _ _ hs => Or.inr ⟨m, hm, hs⟩) n hn

/-- A natural number with a member that has no members is zero. -/
theorem zeroN_of_mem_empty {m e : V} (hm : NatN m) (he : ∀ z, z ∉ e) (hem : e ∈ m) : ZeroN m := by
  rcases natN_cases hm with h | ⟨k, -, hs⟩
  · exact h
  · obtain ⟨x, -, b, -, hb⟩ := (hs e).mp hem
    exact absurd ((hb b).mpr (Or.inr rfl)) (he b)

end model

end HinU

end FFL.FirstOrder.SetTheory
