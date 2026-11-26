module

public import MHHier

@[expose] public section

set_option autoImplicit false

/-!
# A constructible hull, with constructible codes

In a model of `𝗠𝗛`. Let `W` be a constructible set, `G₀ ⊆ W` a constructible set of
generators that maps one-to-one into a constructible set `S` of codes by a constructible
relation `j₀`, and `g` a constructible set that is a function of four arguments on `W`
(`Ap4`). If `S` has the empty set as a member and is closed under pairs, then there is a
constructible `N ⊆ W` that includes `G₀`, is closed under the function, and maps one-to-one
into `S` by a constructible relation: `exists_chull`.

There is no recursion on stages. A relation `R ⊆ W × S` is *closed* (`ClR`) if it relates
every generator `x` to the pair of the empty set and a code of `x`, and relates the value of
the function at `y₀, …, y₃` to the pair of two pairs of codes of the `yᵢ` (`InstR`). `RL` is the
set of the pairs that are in every closed relation that is a member of one fixed level, which
has all the constructible relations of this kind as members (`bound_exists`). It is defined by
a bounded formula from constructible parameters, so it is constructible, and it is the least
constructible closed relation. Two uses of that leastness give that every pair of `RL` is an
instance of the rules (inversion) and that a code is the code of one set only. The hull is the
domain of `RL`.

`con_sepB`: a subset of a constructible set defined by a bounded formula from constructible
parameters is constructible.
-/

namespace FFL.FirstOrder.SetTheory

namespace MH

/-- **One step of coding.** `C` is a code of `x` given the codes in `R`: `x` is a generator and
`C` is the pair of the empty set and a code of `x` by `j₀`; or `x` is the value of the function
`g` at four sets and `C` is the pair of two pairs of codes of these by `R`. -/
def InstR {V : Type} [SetStructure V] (x C R j₀ G₀ g W S : V) : Prop :=
  (x ∈ G₀ ∧ ∃ c, c ∈ S ∧ (Pr j₀ x c ∧ ∃ e, e ∈ S ∧ ((∀ w, w ∈ e → False) ∧ IsOp C e c))) ∨
  (∃ y₀, y₀ ∈ W ∧ ∃ y₁, y₁ ∈ W ∧ ∃ y₂, y₂ ∈ W ∧ ∃ y₃, y₃ ∈ W ∧ ∃ c₀, c₀ ∈ S ∧ ∃ c₁, c₁ ∈ S ∧
    ∃ c₂, c₂ ∈ S ∧ ∃ c₃, c₃ ∈ S ∧ (Pr R y₀ c₀ ∧ (Pr R y₁ c₁ ∧ (Pr R y₂ c₂ ∧ (Pr R y₃ c₃ ∧
      (Ap4 g y₀ y₁ y₂ y₃ x ∧ Code4 C c₀ c₁ c₂ c₃ S))))))

def instRB : BDef (k := 8) (fun V _ v ↦
    InstR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) :=
  (((BDef.mem 0 4).and (BDef.bex 7 ((prB.comp ![4, 1, 0]).and (BDef.bex 8
      ((BDef.ball 0 BDef.fls).and (isOpB.comp ![3, 0, 1])))))).or
    (BDef.bex 6 (BDef.bex 7 (BDef.bex 8 (BDef.bex 9 (BDef.bex 11 (BDef.bex 12 (BDef.bex 13
      (BDef.bex 14 ((prB.comp ![10, 7, 3]).and ((prB.comp ![10, 6, 2]).and
        ((prB.comp ![10, 5, 1]).and ((prB.comp ![10, 4, 0]).and
          ((ap4B.comp ![13, 7, 6, 5, 4, 8]).and
            (code4B.comp ![9, 3, 2, 1, 0, 15]))))))))))))))).congr fun _ _ _ => Iff.rfl

/-- `R` is closed under the steps of coding. -/
def ClR {V : Type} [SetStructure V] (R j₀ G₀ g W S : V) : Prop :=
  ∀ x, x ∈ W → ∀ C, C ∈ S → InstR x C R j₀ G₀ g W S → Pr R x C

def clRB : BDef (k := 6) (fun V _ v ↦ ClR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  (BDef.ball 4 (BDef.ball 6 ((instRB.comp ![1, 0, 2, 3, 4, 5, 6, 7]).imp
    (prB.comp ![2, 1, 0])))).congr fun _ _ _ => Iff.rfl

section clos

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **A subset of a constructible set defined by a bounded formula from constructible
parameters is constructible.** -/
theorem con_sepB {k : ℕ} {R : MRel (k + 1)} (d : BDef R) {a : V} (ha : Con a) (p : Fin k → V)
    (hp : ∀ i, Con (p i)) : Con (sepB d a p) := by
  obtain ⟨γ, hγ, -, haγ, hl⟩ := good_common (good_of_con ha) (List.ofFn p) (by
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    rw [← hi]
    exact good_of_con (hp i))
  obtain ⟨y, hy, hyz⟩ := sep_good_bdef (closed_true (V := V)) d (good_of_con (con_lev hγ.1))
    (lev_tr hγ.1) p
    (fun i => ⟨hl (p i) (List.mem_ofFn.mpr ⟨i, rfl⟩), good_of_con (hp i)⟩)
  obtain ⟨S, hS, hSz⟩ := con_inter (con_of_good hy) ha
  have e : sepB d a p = S := mem_ext fun z => by
    rw [hSz, hyz]
    exact (mem_sepB d a p z).trans
      ⟨fun h => ⟨⟨lev_tr hγ.1 a haγ z h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  rw [e]
  exact hS

omit [Nonempty V] hH in
theorem instR_mono {x C R R' j₀ G₀ g W S : V} (h : ∀ a b, Pr R a b → Pr R' a b)
    (hi : InstR x C R j₀ G₀ g W S) : InstR x C R' j₀ G₀ g W S := by
  rcases hi with hb | ⟨y₀, h0, y₁, h1, y₂, h2, y₃, h3, c₀, k0, c₁, k1, c₂, k2, c₃, k3,
    p0, p1, p2, p3, ha, hc⟩
  · exact Or.inl hb
  · exact Or.inr ⟨y₀, h0, y₁, h1, y₂, h2, y₃, h3, c₀, k0, c₁, k1, c₂, k2, c₃, k3,
      h _ _ p0, h _ _ p1, h _ _ p2, h _ _ p3, ha, hc⟩

theorem code4_inj {C c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ S : V} (h : Code4 C c₀ c₁ c₂ c₃ S)
    (h' : Code4 C d₀ d₁ d₂ d₃ S) : c₀ = d₀ ∧ c₁ = d₁ ∧ c₂ = d₂ ∧ c₃ = d₃ := by
  obtain ⟨p₁, -, p₂, -, o1, o2, o3⟩ := h
  obtain ⟨q₁, -, q₂, -, o1', o2', o3'⟩ := h'
  obtain ⟨e1, e2⟩ := kp_inj ((isOp_iff.mp o3).symm.trans (isOp_iff.mp o3'))
  obtain ⟨a1, a2⟩ := kp_inj ((isOp_iff.mp o1).symm.trans (e1.trans (isOp_iff.mp o1')))
  obtain ⟨a3, a4⟩ := kp_inj ((isOp_iff.mp o2).symm.trans (e2.trans (isOp_iff.mp o2')))
  exact ⟨a1, a2, a3, a4⟩

theorem code4_not_base {C c₀ c₁ c₂ c₃ S e c : V} (h : Code4 C c₀ c₁ c₂ c₃ S)
    (hop : IsOp C e c) (he : ∀ w, w ∈ e → False) : False := by
  obtain ⟨p₁, -, p₂, -, o1, -, o3⟩ := h
  obtain ⟨e1, -⟩ := kp_inj ((isOp_iff.mp o3).symm.trans (isOp_iff.mp hop))
  obtain ⟨w, hw⟩ := isOp_nonempty o1
  rw [e1] at hw
  exact he w hw

/-- **A constructible hull with constructible codes.** -/
theorem exists_chull {W S g j₀ G₀ lam : V} (hlam : Big lam)
    (hW : Con W) (hS : Con S) (hg : Con g) (hj : Con j₀) (hG : Con G₀)
    (hWl : ∀ x, x ∈ W → x ∈ Lev lam) (hSl : ∀ c, c ∈ S → c ∈ Lev lam)
    (hGW : ∀ x, x ∈ G₀ → x ∈ W)
    (hjt : ∀ x, x ∈ G₀ → ∃ c, c ∈ S ∧ Pr j₀ x c)
    (hji : ∀ x, x ∈ G₀ → ∀ x', x' ∈ G₀ → ∀ c, Pr j₀ x c → Pr j₀ x' c → x = x')
    (hSp : ∀ a b, a ∈ S → b ∈ S → kp a b ∈ S) (h0 : (∅ : V) ∈ S)
    (hgf : ∀ y₀ y₁ y₂ y₃ x x', Ap4 g y₀ y₁ y₂ y₃ x → Ap4 g y₀ y₁ y₂ y₃ x' → x = x') :
    ∃ N : V, Con N ∧ (∀ x, x ∈ N → x ∈ W) ∧ (∀ x, x ∈ G₀ → x ∈ N) ∧
      (∀ y₀ y₁ y₂ y₃ x, y₀ ∈ N → y₁ ∈ N → y₂ ∈ N → y₃ ∈ N → x ∈ W →
        Ap4 g y₀ y₁ y₂ y₃ x → x ∈ N) ∧ LInj N S := by
  have h4 := big_scn hlam 4
  have hT4 : Con (Lev (scn 4 lam)) := con_lev h4.1
  obtain ⟨κK, hκK, hbK⟩ := bound_exists h4
  have hK : Con (Lev κK) := con_lev hκK
  have hpair : ∀ x C, x ∈ W → C ∈ S → kp x C ∈ Lev (scn 4 lam) :=
    fun x C hx hC => kp_mem_lev hlam (hWl x hx) (hSl C hC)
  have hemp : ∀ w, w ∈ (∅ : V) → False := fun w hw => absurd hw (by simp)
  -- the least closed relation
  let RL : V := sepB (k := 6) (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
    (BDef.ball 5 ((clRB.comp ![0, 7, 8, 9, 4, 5]).imp (prB.comp ![0, 2, 1]))))))
    (Lev (scn 4 lam)) ![W, S, Lev κK, j₀, G₀, g]
  have hRLz : ∀ q, q ∈ RL ↔ q ∈ Lev (scn 4 lam) ∧ ∃ x, x ∈ W ∧ ∃ C, C ∈ S ∧
      (IsOp q x C ∧ ∀ R, R ∈ Lev κK → ClR R j₀ G₀ g W S → Pr R x C) :=
    fun q => mem_sepB _ _ _ q
  have hRLc : Con RL := con_sepB _ hT4 _ (by
    intro i
    match i with
    | 0 => exact hW
    | 1 => exact hS
    | 2 => exact hK
    | 3 => exact hj
    | 4 => exact hG
    | 5 => exact hg)
  have hRL : ∀ x C, Pr RL x C ↔ x ∈ W ∧ C ∈ S ∧
      ∀ R, R ∈ Lev κK → ClR R j₀ G₀ g W S → Pr R x C := by
    intro x C
    rw [pr_iff, hRLz]
    constructor
    · rintro ⟨-, x', hx', C', hC', hop, h⟩
      obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
      rw [e1, e2]
      exact ⟨hx', hC', h⟩
    · rintro ⟨hx, hC, h⟩
      exact ⟨hpair x C hx hC, x, hx, C, hC, isOp_kp x C, h⟩
  have hRLsub : ∀ q, q ∈ RL → q ∈ Lev (scn 4 lam) := fun q hq => ((hRLz q).mp hq).1
  have hRLcl : ClR RL j₀ G₀ g W S := by
    intro x hx C hC hi
    exact (hRL x C).mpr ⟨hx, hC, fun R hR hcl => hcl x hx C hC
      (instR_mono (fun a b hab => ((hRL a b).mp hab).2.2 R hR hcl) hi)⟩
  have hmin : ∀ R, Con R → (∀ q, q ∈ R → q ∈ Lev (scn 4 lam)) → ClR R j₀ G₀ g W S →
      ∀ x C, Pr RL x C → Pr R x C := by
    intro R hRc hRsub hcl x C h
    obtain ⟨δ, hδ, hRδ⟩ := hRc
    exact ((hRL x C).mp h).2.2 R (hbK δ R hδ hRδ hRsub) hcl
  -- inversion
  let Rv : V := sepB (k := 6) (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
    ((prB.comp ![5, 1, 0]).and (instRB.comp ![1, 0, 5, 6, 7, 8, 3, 4])))))
    (Lev (scn 4 lam)) ![W, S, RL, j₀, G₀, g]
  have hRvz : ∀ q, q ∈ Rv ↔ q ∈ Lev (scn 4 lam) ∧ ∃ x, x ∈ W ∧ ∃ C, C ∈ S ∧
      (IsOp q x C ∧ (Pr RL x C ∧ InstR x C RL j₀ G₀ g W S)) := fun q => mem_sepB _ _ _ q
  have hRvc : Con Rv := con_sepB _ hT4 _ (by
    intro i
    match i with
    | 0 => exact hW
    | 1 => exact hS
    | 2 => exact hRLc
    | 3 => exact hj
    | 4 => exact hG
    | 5 => exact hg)
  have hRv : ∀ x C, Pr Rv x C ↔ Pr RL x C ∧ InstR x C RL j₀ G₀ g W S := by
    intro x C
    rw [pr_iff, hRvz]
    constructor
    · rintro ⟨-, x', -, C', -, hop, h⟩
      obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
      rw [e1, e2]
      exact h
    · intro h
      obtain ⟨hx, hC, -⟩ := (hRL x C).mp h.1
      exact ⟨hpair x C hx hC, x, hx, C, hC, isOp_kp x C, h⟩
  have hinv : ∀ x C, Pr RL x C → InstR x C RL j₀ G₀ g W S := by
    intro x C h
    refine ((hRv x C).mp (hmin Rv hRvc (fun q hq => ((hRvz q).mp hq).1) ?_ x C h)).2
    intro x hx C hC hi
    have hi' : InstR x C RL j₀ G₀ g W S := instR_mono (fun a b hab => ((hRv a b).mp hab).1) hi
    exact (hRv x C).mpr ⟨hRLcl x hx C hC hi', hi'⟩
  -- a code is the code of one set only
  let Rj : V := sepB (k := 3) (BDef.bex 1 (BDef.bex 3 ((isOpB.comp ![2, 1, 0]).and
    ((prB.comp ![5, 1, 0]).and (BDef.ball 3 ((prB.comp ![6, 0, 1]).imp (BDef.eq 0 2)))))))
    (Lev (scn 4 lam)) ![W, S, RL]
  have hRjz : ∀ q, q ∈ Rj ↔ q ∈ Lev (scn 4 lam) ∧ ∃ x, x ∈ W ∧ ∃ C, C ∈ S ∧
      (IsOp q x C ∧ (Pr RL x C ∧ ∀ x', x' ∈ W → Pr RL x' C → x' = x)) :=
    fun q => mem_sepB _ _ _ q
  have hRjc : Con Rj := con_sepB _ hT4 _ (by
    intro i
    match i with
    | 0 => exact hW
    | 1 => exact hS
    | 2 => exact hRLc)
  have hRj : ∀ x C, Pr Rj x C ↔ Pr RL x C ∧ ∀ x', x' ∈ W → Pr RL x' C → x' = x := by
    intro x C
    rw [pr_iff, hRjz]
    constructor
    · rintro ⟨-, x', -, C', -, hop, h⟩
      obtain ⟨e1, e2⟩ := kp_inj (isOp_iff.mp hop)
      rw [e1, e2]
      exact h
    · intro h
      obtain ⟨hx, hC, -⟩ := (hRL x C).mp h.1
      exact ⟨hpair x C hx hC, x, hx, C, hC, isOp_kp x C, h⟩
  have hRjcl : ClR Rj j₀ G₀ g W S := by
    intro x hx C hC hi
    have hi' : InstR x C RL j₀ G₀ g W S := instR_mono (fun a b hab => ((hRj a b).mp hab).1) hi
    refine (hRj x C).mpr ⟨hRLcl x hx C hC hi', fun x' hx' hx'C => ?_⟩
    have hv := hinv x' C hx'C
    rcases hi with ⟨hxG, c, -, hjc, e, -, he, hop⟩ |
      ⟨y₀, -, y₁, -, y₂, -, y₃, -, c₀, -, c₁, -, c₂, -, c₃, -, p0, p1, p2, p3, ha, hc⟩
    · rcases hv with ⟨hxG', c', -, hjc', e', -, -, hop'⟩ |
        ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, -, -, -, -, -, hc'⟩
      · obtain ⟨-, ec⟩ := kp_inj ((isOp_iff.mp hop).symm.trans (isOp_iff.mp hop'))
        rw [← ec] at hjc'
        exact (hji x hxG x' hxG' c hjc hjc').symm
      · exact (code4_not_base hc' hop he).elim
    · rcases hv with ⟨-, c', -, -, e', -, he', hop'⟩ |
        ⟨z₀, hz0, z₁, hz1, z₂, hz2, z₃, hz3, d₀, -, d₁, -, d₂, -, d₃, -, r0, r1, r2, r3,
          ha', hc'⟩
      · exact (code4_not_base hc hop' he').elim
      · obtain ⟨a0, a1, a2, a3⟩ := code4_inj hc hc'
        rw [← a0] at r0
        rw [← a1] at r1
        rw [← a2] at r2
        rw [← a3] at r3
        rw [((hRj y₀ c₀).mp p0).2 z₀ hz0 r0, ((hRj y₁ c₁).mp p1).2 z₁ hz1 r1,
          ((hRj y₂ c₂).mp p2).2 z₂ hz2 r2, ((hRj y₃ c₃).mp p3).2 z₃ hz3 r3] at ha'
        exact hgf y₀ y₁ y₂ y₃ x' x ha' ha
  have hRLinj : ∀ x x' C, Pr RL x C → Pr RL x' C → x' = x := fun x x' C h h' =>
    ((hRj x C).mp (hmin Rj hRjc (fun q hq => ((hRjz q).mp hq).1) hRjcl x C h)).2 x'
      ((hRL x' C).mp h').1 h'
  -- the hull
  let N : V := sepB (k := 2) (BDef.bex 1 (prB.comp ![3, 1, 0])) W ![S, RL]
  have hN : ∀ x, x ∈ N ↔ x ∈ W ∧ ∃ C, C ∈ S ∧ Pr RL x C := fun x => mem_sepB _ _ _ x
  have hNc : Con N := con_sepB _ hW _ (by
    intro i
    match i with
    | 0 => exact hS
    | 1 => exact hRLc)
  refine ⟨N, hNc, fun x hx => ((hN x).mp hx).1, fun x hx => ?_,
    fun y₀ y₁ y₂ y₃ x h0' h1 h2 h3 hx ha => ?_, RL, hRLc, fun x hx => ?_,
    fun x x' C _ _ h1 h2 => ?_⟩
  · obtain ⟨c, hc, hjc⟩ := hjt x hx
    exact (hN x).mpr ⟨hGW x hx, kp ∅ c, hSp _ _ h0 hc, hRLcl x (hGW x hx) _ (hSp _ _ h0 hc)
      (Or.inl ⟨hx, c, hc, hjc, ∅, h0, hemp, isOp_kp ∅ c⟩)⟩
  · obtain ⟨hy0, c₀, k0, p0⟩ := (hN y₀).mp h0'
    obtain ⟨hy1, c₁, k1, p1⟩ := (hN y₁).mp h1
    obtain ⟨hy2, c₂, k2, p2⟩ := (hN y₂).mp h2
    obtain ⟨hy3, c₃, k3, p3⟩ := (hN y₃).mp h3
    have q1 := hSp _ _ k0 k1
    have q2 := hSp _ _ k2 k3
    exact (hN x).mpr ⟨hx, kp (kp c₀ c₁) (kp c₂ c₃), hSp _ _ q1 q2,
      hRLcl x hx _ (hSp _ _ q1 q2) (Or.inr ⟨y₀, hy0, y₁, hy1, y₂, hy2, y₃, hy3, c₀, k0, c₁, k1,
        c₂, k2, c₃, k3, p0, p1, p2, p3, ha, kp c₀ c₁, q1, kp c₂ c₃, q2, isOp_kp _ _,
        isOp_kp _ _, isOp_kp _ _⟩)⟩
  · obtain ⟨-, C, hC, h⟩ := (hN x).mp hx
    exact ⟨C, hC, hin_rl_iff.mpr (pr_iff.mp h)⟩
  · exact (hRLinj x x' C (pr_iff.mpr (hin_rl_iff.mp h1)) (pr_iff.mpr (hin_rl_iff.mp h2))).symm

end clos

end MH

end FFL.FirstOrder.SetTheory
