module

public import FnCountNFU

@[expose] public section

set_option autoImplicit false

/-!
# Bringing the Axiom of Counting into the sets of a model of FunctionNF

Let `N` be a model of `𝗙𝗡𝗙`, and let `Mv` be a model of NFU + Infinity + the Axiom of Counting
whose objects are those of `N` (through a bijection `c`). Suppose an object `s₀` of `N` turns
every object `y` into the set `s₀ · y` of `N` whose members are the members of `y` in `Mv`:

  `x ∈ s₀ · y`  in `N`   ↔   `x ∈ y`  in `Mv`.

Then the sets of `N` satisfy the Axiom of Counting (`counting_of_transfer`).

This is how the Axiom of Counting passes from a model of NF to the model of FunctionNF built
in it, where a set and the object that labels its characteristic function are different
objects. The proof gives a strongly cantorian set of `N` with a proper injection into itself:

* `d = s₀ · ℕ`, the set of the natural numbers of `Mv`;
* the graph of the singleton map on `d` is `{(n', {n}) : n, n' ∈ d, n' = T n}`, where `n' = T n`
  is written with the membership of `Mv` and has `n'` one level above `n` (`tEB`); this is the
  graph of `n ↦ {n}` because `T n = n`;
* the graph of the successor of `Mv` on `d` (`succEB`).
-/

namespace FFL.FirstOrder

namespace FNF

open JensenNFU (Counting IsSuccN)
open JensenNFU.TFm (scons scons_zero scons_succ)

noncomputable section

variable {N : Type} [Tarski.Structure ℒλ N] [Tarski.Structure.Eq ℒλ N] [Nonempty N]
  [hN : N↓[ℒλ] ⊧* 𝗙𝗡𝗙]

local infixl:70 " ⬝ " => App

/-- `v₀ ∈ v₂ · v₁`. -/
def eB : BT [0, 1, 2] (fun v : ℕ → N => Mem (v 0) (v 2 ⬝ v 1)) :=
  BT.congr (BT.ex 1 ((BT.app 3 2 0 1 rfl rfl rfl).and (BT.mem 1 0 0 rfl rfl)))
    fun v => ⟨fun ⟨w, (h1 : v 2 ⬝ v 1 = w), (h2 : Mem (v 0) w)⟩ => by rw [h1]; exact h2,
      fun h => ⟨_, rfl, h⟩⟩

/-- "`v₁` is the successor of `v₀`", for the membership `x ∈ s · y`. The object `s` is used at
two levels: `v₂` and `v₃`. -/
def succEB : BT [2, 2, 3, 2] (fun v : ℕ → N =>
    ∀ y, Mem y (v 2 ⬝ v 1) ↔ ∃ x, Mem x (v 2 ⬝ v 0) ∧ ∃ b, ¬Mem b (v 3 ⬝ x) ∧
      ∀ z, Mem z (v 3 ⬝ y) ↔ Mem z (v 3 ⬝ x) ∨ z = b) :=
  BT.congr (BT.all 1 ((eB.sub [0, 2, 3] 1).iff (BT.ex 1 ((eB.sub [0, 2, 4] 1).and
    (BT.ex 0 (((eB.sub [0, 1, 6] 0).not).and (BT.all 0 ((eB.sub [0, 3, 7] 0).iff
      ((eB.sub [0, 2, 7] 0).or (BT.eq 0 1 0 rfl rfl)))))))))) fun _ => Iff.rfl

/-- "`v₁ = T v₀`", for the membership `x ∈ s · y`: some member `x` of `v₀` has
`{{a} : a ∈ x} ∈ v₁`. Here `v₁` is one level above `v₀`. The object `s` is used at three
levels: `v₂`, `v₃` and `v₄`. -/
def tEB : BT [2, 3, 4, 3, 2] (fun v : ℕ → N =>
    ∃ x y, Mem x (v 3 ⬝ v 0) ∧ Mem y (v 2 ⬝ v 1) ∧
      ∀ c, Mem c (v 3 ⬝ y) ↔ ∃ a, Mem a (v 4 ⬝ x) ∧ ∀ e, Mem e (v 4 ⬝ c) ↔ e = a) :=
  BT.congr (BT.ex 1 (BT.ex 2 ((eB.sub [1, 2, 5] 1).and ((eB.sub [0, 3, 4] 2).and
    (BT.all 1 ((eB.sub [0, 1, 6] 1).iff (BT.ex 0 ((eB.sub [0, 3, 8] 0).and
      (BT.all 0 ((eB.sub [0, 2, 9] 0).iff (BT.eq 0 1 0 rfl rfl))))))))))) fun _ => Iff.rfl

/-- **The Axiom of Counting passes to the sets of a model of FunctionNF** from a model of
NFU + Infinity on the same objects whose membership is `x ∈ s₀ · y`. -/
theorem counting_of_transfer {W : Type} [Nonempty W] (Mv : NFUCut.Model W) [Fact Mv.Infinity]
    (hT : ∀ n : Mv.Num, Mv.T n = n) (c : N → W) (u : W → N) (hcu : ∀ w, c (u w) = w)
    (huc : ∀ a, u (c a) = a) (s₀ : N)
    (hE : ∀ x y, Mem x (s₀ ⬝ y) ↔ Mv.mem (c x) (c y)) : Counting (Mem (M := N)) := by
  have hinj : Function.Injective c := fun a b h => by rw [← huc a, ← huc b, h]
  have hsurj : Function.Surjective c := fun w => ⟨u w, hcu w⟩
  -- the set of the natural numbers of `Mv`
  obtain ⟨d, hd⟩ : ∃ d : N, ∀ x, Mem x d ↔ Mv.mem (c x) Mv.nat :=
    ⟨s₀ ⬝ u Mv.nat, fun x => by rw [hE, hcu]⟩
  -- "`c y` is the set of the singletons of the members of `c x`"
  have hsimg : ∀ x y : N, Mv.isSet (c y) →
      ((∀ c', Mem c' (s₀ ⬝ y) ↔ ∃ a, Mem a (s₀ ⬝ x) ∧ ∀ e, Mem e (s₀ ⬝ c') ↔ e = a) ↔
        c y = Mv.simg (c x)) := by
    intro x y hy
    have key : ∀ c' : N, (∃ a, Mem a (s₀ ⬝ x) ∧ ∀ e, Mem e (s₀ ⬝ c') ↔ e = a) ↔
        ∃ a, Mv.mem a (c x) ∧ c c' = Mv.sing a := by
      intro c'
      constructor
      · rintro ⟨a, ha, he⟩
        refine ⟨c a, (hE _ _).mp ha, Mv.eq_sing_iff.mp fun z => ?_⟩
        obtain ⟨z', rfl⟩ := hsurj z
        rw [← hE, he z']
        exact ⟨fun h' => by rw [h'], fun h' => hinj h'⟩
      · rintro ⟨a, ha, he⟩
        obtain ⟨a', rfl⟩ := hsurj a
        refine ⟨a', (hE _ _).mpr ha, fun e => ?_⟩
        rw [hE, he, Mv.mem_sing]
        exact ⟨fun h' => hinj h', fun h' => by rw [h']⟩
    rw [← Mv.eq_simg_iff]
    constructor
    · intro h
      refine ⟨hy, fun w => ?_⟩
      obtain ⟨w', rfl⟩ := hsurj w
      rw [← hE, h w']
      exact key w'
    · rintro ⟨-, h⟩ c'
      rw [hE, h (c c')]
      exact (key c').symm
  -- "`n' = T n`" means `n' = n`
  have htr : ∀ n n' : N, Mem n d → Mem n' d →
      ((∃ x y, Mem x (s₀ ⬝ n) ∧ Mem y (s₀ ⬝ n') ∧
        ∀ c', Mem c' (s₀ ⬝ y) ↔ ∃ a, Mem a (s₀ ⬝ x) ∧ ∀ e, Mem e (s₀ ⬝ c') ↔ e = a) ↔
        n' = n) := by
    intro n n' hn hn'
    have hn1 := (hd n).mp hn
    have hn1' := (hd n').mp hn'
    constructor
    · rintro ⟨x, y, hx, hy, h⟩
      have hx1 := (hE x n).mp hx
      have hy1 := (hE y n').mp hy
      have e := (hsimg x y (Mv.isSet_of_mem_nat hn1' hy1)).mp h
      rw [e] at hy1
      have := Mv.T_eq_of_mem (m := ⟨c n, hn1⟩) (n := ⟨c n', hn1'⟩) hx1 hy1
      rw [hT] at this
      exact hinj (congrArg Subtype.val this).symm
    · intro e
      rw [e]
      obtain ⟨x, hx⟩ := Mv.nat_nonempty hn1
      have hs := Mv.simg_mem_T (m := ⟨c n, hn1⟩) hx
      rw [hT] at hs
      refine ⟨u x, u (Mv.simg x), (hE _ _).mpr (by rw [hcu]; exact hx),
        (hE _ _).mpr (by rw [hcu]; exact hs), ?_⟩
      exact (hsimg (u x) (u (Mv.simg x)) (by rw [hcu]; exact Mv.simg_isSet x)).mpr
        (by rw [hcu, hcu])
  -- the graph of the singleton map on `d`
  obtain ⟨G, hG, hGmem⟩ : ∃ G : N, IsSet G ∧ ∀ p, Mem p G ↔ ∃ n n' s, Mem n d ∧ Mem n' d ∧
      (∃ x y, Mem x (s₀ ⬝ n) ∧ Mem y (s₀ ⬝ n') ∧
        ∀ c', Mem c' (s₀ ⬝ y) ↔ ∃ a, Mem a (s₀ ⬝ x) ∧ ∀ e, Mem e (s₀ ⬝ c') ↔ e = a) ∧
      s = sing n ∧ p = kp n' s :=
    (BT.ex (Γ := [5, 3, 4, 4, 3, 2]) 2 (BT.ex 3 (BT.ex 3 ((BT.mem 2 4 2 rfl rfl).and
      ((BT.mem 1 5 3 rfl rfl).and ((tEB.sub [2, 1, 6, 7, 8] 0).and
        ((singB.sub [0, 2] 2).and (kpB.sub [3, 1, 0] 3)))))))).set
      (scons d (scons d (scons s₀ (scons s₀ (fun _ => s₀)))))
  have strong : CountSet.Strong d := by
    refine ⟨G, hG, fun p => (hGmem p).trans ⟨?_, ?_⟩⟩
    · rintro ⟨n, n', s, hn, hn', htr', rfl, rfl⟩
      rw [(htr n n' hn hn').mp htr']
      exact ⟨n, hn, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, x, sing x, hx, hx, (htr x x hx hx).mpr rfl, rfl, rfl⟩
  -- the graph of the successor on `d`
  obtain ⟨f, hf, hfmem⟩ : ∃ f : N, IsSet f ∧ ∀ p, Mem p f ↔ ∃ n m, Mem n d ∧
      (∀ y, Mem y (s₀ ⬝ m) ↔ ∃ x, Mem x (s₀ ⬝ n) ∧ ∃ b, ¬Mem b (s₀ ⬝ x) ∧
        ∀ z, Mem z (s₀ ⬝ y) ↔ Mem z (s₀ ⬝ x) ∨ z = b) ∧ p = kp n m :=
    (BT.ex (Γ := [4, 3, 3, 2]) 2 (BT.ex 2 ((BT.mem 1 3 2 rfl rfl).and
      ((succEB.sub [1, 0, 4, 5] 0).and (kpB.sub [2, 1, 0] 2))))).set
      (scons d (scons s₀ (fun _ => s₀)))
  have hsucc : ∀ n m : N, Mem n d →
      ((∀ y, Mem y (s₀ ⬝ m) ↔ ∃ x, Mem x (s₀ ⬝ n) ∧ ∃ b, ¬Mem b (s₀ ⬝ x) ∧
        ∀ z, Mem z (s₀ ⬝ y) ↔ Mem z (s₀ ⬝ x) ∨ z = b) ↔ c m = Mv.succ (c n)) := by
    intro n m hn
    have hn1 := (hd n).mp hn
    have key : IsSuccN (fun a b : N => Mem a (s₀ ⬝ b)) n m ↔ IsSuccN Mv.mem (c n) (c m) :=
      isSuccN_map c hinj hsurj hE n m
    refine Iff.trans key ⟨fun h => Mv.eq_succ_of_isSuccN (Mv.exists_omit hn1) h, fun h => ?_⟩
    rw [h]
    exact Mv.isSuccN_succ (c n)
  have hap : ∀ x y : N, Ap f x y ↔ Mem x d ∧ c y = Mv.succ (c x) := by
    intro x y
    change Mem (kp x y) f ↔ _
    rw [hfmem]
    constructor
    · rintro ⟨n, m, hn, hs', e⟩
      obtain ⟨rfl, rfl⟩ := kp_inj e
      exact ⟨hn, (hsucc _ _ hn).mp hs'⟩
    · rintro ⟨hx, e⟩
      exact ⟨x, y, hx, (hsucc x y hx).mpr e, rfl⟩
  have inj : Inj f d d := by
    constructor
    · intro x y h
      obtain ⟨hx, e⟩ := (hap x y).mp h
      refine ⟨hx, (hd y).mpr ?_⟩
      rw [e]
      exact Mv.succ_mem_nat ((hd x).mp hx)
    · intro x hx
      exact ⟨u (Mv.succ (c x)), (hap _ _).mpr ⟨hx, hcu _⟩⟩
    · intro x y y' h h'
      exact hinj (((hap x y).mp h).2.trans ((hap x y').mp h').2.symm)
    · intro x x' y h h'
      obtain ⟨hx, e⟩ := (hap x y).mp h
      obtain ⟨hx', e'⟩ := (hap x' y).mp h'
      exact hinj (Mv.succ_inj ((hd x).mp hx) ((hd x').mp hx') (e.symm.trans e'))
  have ded : CountSet.Dedekind d :=
    ⟨f, u Mv.zero, hf, inj, (hd _).mpr (by rw [hcu]; exact Mv.zero_mem_nat), fun x hx => by
      obtain ⟨-, e⟩ := (hap _ _).mp hx
      rw [hcu] at e
      exact Mv.zero_ne_succ _ e⟩
  exact counting_of_T (T_eq_of_strong_dedekind d strong ded)

end

end FNF

end FFL.FirstOrder

#print axioms FFL.FirstOrder.FNF.counting_of_transfer
