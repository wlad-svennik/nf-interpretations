module

public import HostTerm

@[expose] public section

set_option autoImplicit false

/-!
# A partition theorem of Erdős–Rado type in a host

Part 1: preliminaries. The ordinals of a closed level (`ords`), which are bounded under the
functions whose domain is a member of the level (`Closed.ords_bd`); sets of `r` ordinals
(`Card`, from `HostTerm.lean`): adding a largest member, removing it, images and inverse images
under increasing functions, and the set of the `r`-element subsets of a member of a closed
level (`Closed.cards_mem`).
-/

namespace Host

variable {H : Host}

/-! ### Ordinals -/

theorem on_un_of {x : H.W} (h : ∀ y, y ∈ x → H.On y) : H.On (H.un x) := by
  refine ⟨fun a b hab hb => ?_, fun b hb => ?_⟩
  · obtain ⟨y, hy, hby⟩ := H.mem_un.mp hb
    exact H.mem_un.mpr ⟨y, hy, (h y hy).1 a b hab hby⟩
  · obtain ⟨y, hy, hby⟩ := H.mem_un.mp hb
    exact (H.on_mem (h y hy) hby).1

/-- For ordinals, the order of the host is membership. -/
theorem on_lt_iff {a b : H.W} (ha : H.On a) (hb : H.On b) : H.lt a b ↔ a ∈ b := by
  refine ⟨fun h => ?_, H.mem_lt a b⟩
  rcases H.on_tri a ha b hb with e | e | e
  · exact e
  · rw [e] at h
    exact (H.lt_irrefl b h).elim
  · exact (H.lt_irrefl a (H.lt_trans a b a h (H.mem_lt b a e))).elim

theorem on_le_of_sub {a b : H.W} (ha : H.On a) (hb : H.On b) (h : ∀ z, z ∈ a → z ∈ b) :
    a = b ∨ a ∈ b := by
  rcases H.on_tri a ha b hb with e | e | e
  · exact Or.inr e
  · exact Or.inl e
  · exact (H.mem_irrefl b (h b e)).elim

/-- The ordinals in `M`. -/
noncomputable def ords (H : Host) (M : H.W) : H.W := H.sepS M (fun a => H.On a) (by hdef)

theorem mem_ords {M a : H.W} : a ∈ H.ords M ↔ a ∈ M ∧ H.On a := H.mem_sepS

theorem on_ords {M : H.W} (hM : H.Closed M) : H.On (H.ords M) :=
  ⟨fun x y hxy hy => H.mem_ords.mpr ⟨hM.trans x y hxy (H.mem_ords.mp hy).1,
      H.on_mem (H.mem_ords.mp hy).2 hxy⟩,
    fun y hy => (H.mem_ords.mp hy).2.1⟩

theorem ords_suc {M a : H.W} (hM : H.Closed M) (ha : a ∈ H.ords M) : H.suc a ∈ H.ords M :=
  H.mem_ords.mpr ⟨hM.suc_mem (H.mem_ords.mp ha).1, H.suc_on (H.mem_ords.mp ha).2⟩

theorem ords_not_mem {M : H.W} (hM : H.Closed M) : ¬ H.ords M ∈ M :=
  fun h => H.mem_irrefl _ (H.mem_ords.mpr ⟨h, H.on_ords hM⟩)

theorem Closed.ords_mem {M M' : H.W} (hM' : H.Closed M') (hMM' : M ∈ M') : H.ords M ∈ M' :=
  hM'.sepS_mem hMM' _ _

/-- **The ordinals of a closed level are bounded under the functions whose domain is a member
of the level.** -/
theorem Closed.ords_bd {M f : H.W} (hM : H.Closed M) (hf : H.IsFun f) (hd : H.dom f ∈ M)
    (hv : ∀ a b, H.App f a b → b ∈ H.ords M) :
    ∃ β, β ∈ H.ords M ∧ ∀ a b, H.App f a b → b ∈ β := by
  have hR : H.ran f ∈ M := hM.ran_mem hf hd (fun a b h => (H.mem_ords.mp (hv a b h)).1)
  have hRo : ∀ y, y ∈ H.ran f → H.On y := fun y hy => by
    obtain ⟨a, ha⟩ := H.mem_ran.mp hy
    exact (H.mem_ords.mp (hv a y ha)).2
  have hσ : H.On (H.un (H.ran f)) := H.on_un_of hRo
  refine ⟨H.suc (H.un (H.ran f)), H.mem_ords.mpr ⟨hM.suc_mem (hM.un_mem hR), H.suc_on hσ⟩,
    fun a b h => ?_⟩
  have hb : b ∈ H.ran f := H.mem_ran.mpr ⟨a, h⟩
  rcases H.on_tri b (hRo b hb) _ hσ with e | e | e
  · exact H.mem_suc.mpr (Or.inl e)
  · exact H.mem_suc.mpr (Or.inr e)
  · exact (H.mem_irrefl _ (H.mem_un.mpr ⟨b, hb, e⟩)).elim

/-- `X` has a member and no largest member. -/
def Large (X : H.W) : Prop := (∃ x, x ∈ X) ∧ ∀ x, x ∈ X → ∃ y, y ∈ X ∧ x ∈ y

/-! ### Sets of `r` ordinals -/

theorem card_emp : H.Card H.emp H.emp :=
  ⟨H.emp, H.incSeq_emp, fun z => ⟨fun h => (H.not_mem_emp z h).elim,
    fun ⟨_, h⟩ => (H.not_mem_emp _ (H.app_iff.mp h)).elim⟩⟩

theorem card_emp_iff {B : H.W} : H.Card B H.emp ↔ B = H.emp := by
  constructor
  · rintro ⟨s, hs, hB⟩
    refine H.eq_emp fun z hz => ?_
    obtain ⟨i, hi⟩ := (hB z).mp hz
    exact H.not_mem_emp i (hs.dom hi)
  · intro e
    rw [e]
    exact H.card_emp

theorem Card.on {B r z : H.W} (h : H.Card B r) (hz : z ∈ B) : H.On z := by
  obtain ⟨s, hs, hB⟩ := h
  obtain ⟨i, hi⟩ := (hB z).mp hz
  exact hs.2.2.1 i z hi

theorem Card.om {B r : H.W} (h : H.Card B r) : r ∈ H.om := by
  obtain ⟨s, hs, -⟩ := h
  exact hs.2.1

/-- Adding a member above all members. -/
theorem card_snoc {B r x : H.W} (hB : H.Card B r) (hx : H.On x) (hbel : H.Below B x) :
    H.Card (H.bun B (H.sg x)) (H.suc r) := by
  obtain ⟨s, hs, hsB⟩ := hB
  refine ⟨H.ins s r x, hs.snoc hx (fun i b h => hbel b ((hsB b).mpr ⟨i, h⟩)), fun z => ?_⟩
  rw [H.mem_bun, H.mem_sg, hsB z]
  constructor
  · rintro (⟨i, hi⟩ | e)
    · exact ⟨i, H.app_ins.mpr (Or.inl hi)⟩
    · exact ⟨r, H.app_ins.mpr (Or.inr ⟨rfl, e⟩)⟩
  · rintro ⟨i, hi⟩
    rcases H.app_ins.mp hi with h | ⟨-, h⟩
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr h

/-- Removing the largest member. -/
theorem card_suc_inv {B' r : H.W} (h : H.Card B' (H.suc r)) :
    ∃ B x, H.Card B r ∧ H.On x ∧ H.Below B x ∧ x ∈ B' ∧ (∀ z, z ∈ B → z ∈ B') ∧
      B' = H.bun B (H.sg x) := by
  obtain ⟨s, hs, hsB⟩ := h
  have hrr : r ∈ H.suc r := H.mem_suc.mpr (Or.inr rfl)
  have hr : r ∈ H.om := H.mem_om_of_mem hs.2.1 hrr
  obtain ⟨x, hx⟩ := hs.tot hrr
  have hs0 : H.IncSeq (H.res s r) r := hs.res hr (fun i hi => H.mem_suc.mpr (Or.inl hi))
  refine ⟨H.ran (H.res s r), x, ⟨H.res s r, hs0, fun z => H.mem_ran⟩, hs.2.2.1 r x hx,
    fun b hb => ?_, (hsB x).mpr ⟨r, hx⟩, fun z hz => ?_, H.ext' fun z => ?_⟩
  · obtain ⟨i, hi⟩ := H.mem_ran.mp hb
    obtain ⟨hir, hib⟩ := H.app_res.mp hi
    exact hs.2.2.2 i r b x hib hx hir
  · obtain ⟨i, hi⟩ := H.mem_ran.mp hz
    exact (hsB z).mpr ⟨i, (H.app_res.mp hi).2⟩
  · rw [hsB z, H.mem_bun, H.mem_sg, H.mem_ran]
    constructor
    · rintro ⟨i, hi⟩
      rcases H.mem_suc.mp (hs.dom hi) with h | h
      · exact Or.inl ⟨i, H.app_res.mpr ⟨h, hi⟩⟩
      · rw [h] at hi
        exact Or.inr (hs.fn hi hx)
    · rintro (⟨i, hi⟩ | e)
      · exact ⟨i, (H.app_res.mp hi).2⟩
      · rw [e]
        exact ⟨r, hx⟩

/-- A set of `r` members of a closed level is a member of the level. -/
theorem Closed.card_mem {M B r : H.W} (hM : H.Closed M) (hB : H.Card B r)
    (hsub : ∀ z, z ∈ B → z ∈ M) : B ∈ M := by
  obtain ⟨s, hs, hsB⟩ := hB
  have e : B = H.ran s := H.ext' fun z => (hsB z).trans H.mem_ran.symm
  have hd : H.dom s = r := H.domIs_unique (H.domIs_dom s) hs.1.2
  rw [e]
  exact hM.ran_mem hs.1.1 (by rw [hd]; exact hM.nat_mem hs.2.1)
    (fun a b h => hsub b ((hsB b).mpr ⟨a, h⟩))

/-- The image of the set `B` under the set of pairs `b`. -/
noncomputable def imgO (H : Host) (b B : H.W) : H.W :=
  H.sepS (H.ran b) (fun y => ∃ x, x ∈ B ∧ H.App b x y) (by hdef)

theorem mem_imgO {b B y : H.W} : y ∈ H.imgO b B ↔ ∃ x, x ∈ B ∧ H.App b x y :=
  H.mem_sepS.trans ⟨fun h => h.2, fun ⟨x, hx, h⟩ => ⟨H.mem_ran.mpr ⟨x, h⟩, x, hx, h⟩⟩

/-- The image of a set of `r` ordinals under a function that is increasing on a set that
includes it. -/
theorem card_img {b B r D : H.W} (hb : H.IsFun b)
    (hinc : ∀ u v u' v', u ∈ D → v ∈ D → H.App b u u' → H.App b v v' → u ∈ v → u' ∈ v')
    (hon : ∀ u u', u ∈ D → H.App b u u' → H.On u') (htot : ∀ u, u ∈ D → ∃ u', H.App b u u')
    (hBD : ∀ z, z ∈ B → z ∈ D) (hB : H.Card B r) : H.Card (H.imgO b B) r := by
  obtain ⟨s, hs, hsB⟩ := hB
  have hsD : ∀ i z, H.App s i z → z ∈ D := fun i z h => hBD z ((hsB z).mpr ⟨i, h⟩)
  refine ⟨H.comp b s, ⟨H.funOn_comp hb hs.1 (fun j v hv => htot v (hsD j v hv)), hs.2.1,
    fun i a h => ?_, fun i j a c h h' hij => ?_⟩, fun y => ?_⟩
  · obtain ⟨z, hz, hza⟩ := H.app_comp.mp h
    exact hon z a (hsD i z hz) hza
  · obtain ⟨z, hz, hza⟩ := H.app_comp.mp h
    obtain ⟨z', hz', hzc⟩ := H.app_comp.mp h'
    exact hinc z z' a c (hsD i z hz) (hsD j z' hz') hza hzc (hs.2.2.2 i j z z' hz hz' hij)
  · rw [H.mem_imgO]
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨i, hi⟩ := (hsB x).mp hx
      exact ⟨i, H.app_comp.mpr ⟨x, hi, hxy⟩⟩
    · rintro ⟨i, hi⟩
      obtain ⟨z, hz, hzy⟩ := H.app_comp.mp hi
      exact ⟨z, (hsB z).mpr ⟨i, hz⟩, hzy⟩

/-- The inverse image, in a set `D` of ordinals, of a set of `r` values of a function that is
increasing on `D`. -/
theorem card_pre {b B r D : H.W} (hb : H.IsFun b) (hD : ∀ u, u ∈ D → H.On u)
    (hinc : ∀ u v u' v', u ∈ D → v ∈ D → H.App b u u' → H.App b v v' → u ∈ v → u' ∈ v')
    (hsurj : ∀ y, y ∈ B → ∃ x, x ∈ D ∧ H.App b x y) (hB : H.Card B r) :
    ∃ B₀, H.Card B₀ r ∧ (∀ x, x ∈ B₀ ↔ x ∈ D ∧ ∃ y, y ∈ B ∧ H.App b x y) := by
  obtain ⟨s, hs, hsB⟩ := hB
  have hrefl : ∀ u v u' v', u ∈ D → v ∈ D → H.App b u u' → H.App b v v' → u' ∈ v' → u ∈ v := by
    intro u v u' v' hu hv h h' hlt
    rcases H.on_tri u (hD u hu) v (hD v hv) with e | e | e
    · exact e
    · rw [e] at h
      rw [hb.2 v u' v' h h'] at hlt
      exact (H.mem_irrefl _ hlt).elim
    · exact (H.mem_asymm hlt (hinc v u v' u' hv hu h' h e)).elim
  have hinj : ∀ u v w, u ∈ D → v ∈ D → H.App b u w → H.App b v w → u = v := by
    intro u v w hu hv h h'
    rcases H.on_tri u (hD u hu) v (hD v hv) with e | e | e
    · exact (H.mem_irrefl _ (hinc u v w w hu hv h h' e)).elim
    · exact e
    · exact (H.mem_irrefl _ (hinc v u w w hv hu h' h e)).elim
  have hfun : ∀ i ∈ r, ∀ x x', (x ∈ D ∧ ∃ y, H.App s i y ∧ H.App b x y) →
      (x' ∈ D ∧ ∃ y, H.App s i y ∧ H.App b x' y) → x = x' := by
    rintro i - x x' ⟨hx, y, hy, hxy⟩ ⟨hx', y', hy', hxy'⟩
    rw [← hs.fn hy hy'] at hxy'
    exact hinj x x' y hx hx' hxy hxy'
  let s₀ := H.mkFun r (fun i x => x ∈ D ∧ ∃ y, H.App s i y ∧ H.App b x y) (by hdef) hfun
  have happ : ∀ {i x : H.W}, H.App s₀ i x ↔ i ∈ r ∧ (x ∈ D ∧ ∃ y, H.App s i y ∧ H.App b x y) :=
    H.app_mkFun
  refine ⟨H.ran s₀, ⟨s₀, ⟨⟨H.isFun_mkFun, fun i => ⟨fun hi => ?_, fun ⟨x, hx⟩ => (happ.mp hx).1⟩⟩,
    hs.2.1, fun i x h => hD x (happ.mp h).2.1, fun i j x x' h h' hij => ?_⟩,
    fun z => H.mem_ran⟩, fun x => ?_⟩
  · obtain ⟨y, hy⟩ := hs.tot hi
    obtain ⟨x, hx, hxy⟩ := hsurj y ((hsB y).mpr ⟨i, hy⟩)
    exact ⟨x, happ.mpr ⟨hi, hx, y, hy, hxy⟩⟩
  · obtain ⟨-, hx, y, hy, hxy⟩ := happ.mp h
    obtain ⟨-, hx', y', hy', hxy'⟩ := happ.mp h'
    exact hrefl x x' y y' hx hx' hxy hxy' (hs.2.2.2 i j y y' hy hy' hij)
  · rw [H.mem_ran]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨-, hx, y, hy, hxy⟩ := happ.mp hi
      exact ⟨hx, y, (hsB y).mpr ⟨i, hy⟩, hxy⟩
    · rintro ⟨hx, y, hy, hxy⟩
      obtain ⟨i, hi⟩ := (hsB y).mp hy
      exact ⟨i, happ.mpr ⟨hs.dom hi, hx, y, hi, hxy⟩⟩

/-- **The set of the `r`-element subsets of a member of a closed level is a member of the
level.** -/
theorem Closed.cards_mem {M A : H.W} (hM : H.Closed M) (hA : A ∈ M) (hAo : ∀ z, z ∈ A → H.On z) :
    ∀ r, r ∈ H.om → ∃ P, P ∈ M ∧ ∀ B, B ∈ P ↔ H.Card B r ∧ ∀ z, z ∈ B → z ∈ A := by
  have hc := H.def_card
  refine H.om_ind (fun r => ∃ P, P ∈ M ∧ ∀ B, B ∈ P ↔ H.Card B r ∧ ∀ z, z ∈ B → z ∈ A)
    (by hdef) ?_ ?_
  · refine ⟨H.sg H.emp, hM.sg_mem hM.emp_mem, fun B => ?_⟩
    rw [H.mem_sg, H.card_emp_iff]
    exact ⟨fun e => ⟨e, fun z hz => by rw [e] at hz; exact (H.not_mem_emp z hz).elim⟩,
      fun h => h.1⟩
  · rintro r hr ⟨P, hP, hPB⟩
    let Dm := H.sepS (H.prod P A) (fun p => ∃ B x, p = H.op B x ∧ H.Below B x) (by hdef)
    have hDm : ∀ {p : H.W}, p ∈ Dm ↔ p ∈ H.prod P A ∧ ∃ B x, p = H.op B x ∧ H.Below B x :=
      H.mem_sepS
    have hfun : ∀ p ∈ Dm, ∀ y y', (∃ B x, p = H.op B x ∧ y = H.bun B (H.sg x)) →
        (∃ B x, p = H.op B x ∧ y' = H.bun B (H.sg x)) → y = y' := by
      rintro p - y y' ⟨B, x, e, ey⟩ ⟨B', x', e', ey'⟩
      obtain ⟨e1, e2⟩ := H.op_inj (e.symm.trans e')
      rw [ey, ey', e1, e2]
    let f := H.mkFun Dm (fun p y => ∃ B x, p = H.op B x ∧ y = H.bun B (H.sg x)) (by hdef) hfun
    have happ : ∀ {p y : H.W}, H.App f p y ↔ p ∈ Dm ∧ ∃ B x, p = H.op B x ∧ y = H.bun B (H.sg x) :=
      H.app_mkFun
    have hdom : H.dom f = Dm := H.ext' fun p => by
      rw [H.mem_dom]
      constructor
      · rintro ⟨y, hy⟩
        exact (happ.mp hy).1
      · intro hp
        obtain ⟨-, B, x, e, -⟩ := hDm.mp hp
        exact ⟨_, happ.mpr ⟨hp, B, x, e, rfl⟩⟩
    have hval : ∀ p y, H.App f p y → y ∈ M := by
      intro p y h
      obtain ⟨hp, B, x, e, ey⟩ := happ.mp h
      rw [e] at hp
      obtain ⟨hB, hx⟩ := H.op_mem_prod.mp (hDm.mp hp).1
      rw [ey]
      exact hM.bun_mem (hM.trans B P hB hP) (hM.sg_mem (hM.trans x A hx hA))
    have hDmM : Dm ∈ M := hM.sepS_mem (hM.prod_mem hP hA) _ _
    have hdomM : H.dom f ∈ M := by
      rw [hdom]
      exact hDmM
    refine ⟨H.ran f, hM.ran_mem H.isFun_mkFun hdomM hval, fun B' => ?_⟩
    rw [H.mem_ran]
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨hpD, B, x, e, ey⟩ := happ.mp hp
      obtain ⟨hpP, B₁, x₁, e₁, hbel⟩ := hDm.mp hpD
      obtain ⟨e1, e2⟩ := H.op_inj (e.symm.trans e₁)
      rw [e] at hpP
      obtain ⟨hB, hx⟩ := H.op_mem_prod.mp hpP
      rw [← e1, ← e2] at hbel
      rw [ey]
      refine ⟨H.card_snoc ((hPB B).mp hB).1 (hAo x hx) hbel, fun z hz => ?_⟩
      rcases H.mem_bun.mp hz with h | h
      · exact ((hPB B).mp hB).2 z h
      · rw [H.mem_sg.mp h]
        exact hx
    · rintro ⟨hcard, hsub⟩
      obtain ⟨B, x, hB, -, hbel, hxB', hBB', e⟩ := H.card_suc_inv hcard
      have hBP : B ∈ P := (hPB B).mpr ⟨hB, fun z hz => hsub z (hBB' z hz)⟩
      have hpD : H.op B x ∈ Dm :=
        hDm.mpr ⟨H.op_mem_prod.mpr ⟨hBP, hsub x hxB'⟩, B, x, rfl, hbel⟩
      exact ⟨H.op B x, happ.mpr ⟨hpD, B, x, rfl, e⟩⟩

/-! ## Part 2: types over small sequences

`M ∈ M'` are closed levels such that every member of `M'` maps one-to-one into `M` by a
function of the host; `col` is a colouring of the sets of `r + 1` ordinals of `M'` with colours
in a member `C` of `M` (`ERCtx`). A *small sequence* is an increasing function `p` whose domain
is an ordinal of `M` and whose values are ordinals of `M'`. Two ordinals above the values of
`p` are *equivalent over `p`* (`Eqv`) if they give the same colour with every set of `r` values
of `p`. -/

def imgO.graph (H : Host) (y b B : H.W) : Prop := ∀ z, z ∈ y ↔ ∃ x, x ∈ B ∧ H.App b x z

theorem imgO.flat (H : Host) (b B : H.W) (Q : H.W → Prop) :
    (∃ y, Host.imgO.graph H y b B ∧ Q y) ↔ Q (H.imgO b B) :=
  ⟨fun ⟨y, hy, hQ⟩ => (H.ext' fun z => (hy z).trans H.mem_imgO.symm : y = H.imgO b B) ▸ hQ,
    fun h => ⟨_, fun _ => H.mem_imgO, h⟩⟩

/-- `p` is an increasing function on `ξ` with ordinals as values. -/
def IncF (H : Host) (p ξ : H.W) : Prop :=
  H.FunOn p ξ ∧ (∀ i a, H.App p i a → H.On a) ∧
    ∀ i j a b, H.App p i a → H.App p j b → i ∈ j → a ∈ b

/-- `a` is above all values of `p`. -/
def AboveF (H : Host) (p a : H.W) : Prop := ∀ i b, H.App p i b → b ∈ a

/-- `a` and `a'` give the same colours with the sets of `r` values of `p`. -/
def Eqv (H : Host) (col r p a a' : H.W) : Prop :=
  ∀ B, H.Card B r → H.SubV B p → ∀ c,
    (H.App col (H.bun B (H.sg a)) c ↔ H.App col (H.bun B (H.sg a')) c)

/-- `t` is the type of `a` over `p`: a function on `P`, the set of the sets of `r` members of
the domain of `p`, that gives the colour of the image with `a`. -/
def IsTy (H : Host) (col p P t a : H.W) : Prop :=
  H.FunOn t P ∧ ∀ B c, H.App t B c → H.App col (H.bun (H.imgO p B) (H.sg a)) c

/-- `w` is an ordinal of `M'` above the values of `p` with the type `t`. -/
def Rz (H : Host) (col p P M' t w : H.W) : Prop :=
  w ∈ H.ords M' ∧ H.AboveF p w ∧ H.IsTy col p P t w

theorem fun_ext' {f f' : H.W} (hf : H.IsFun f) (hf' : H.IsFun f')
    (h : ∀ a b, H.App f a b ↔ H.App f' a b) : f = f' :=
  H.ext' fun q => ⟨fun hq => by
      obtain ⟨a, b, hab⟩ := hf.1 q hq
      rw [H.isOp_iff.mp hab] at hq ⊢
      exact H.app_iff.mp ((h a b).mp (H.app_iff.mpr hq)),
    fun hq => by
      obtain ⟨a, b, hab⟩ := hf'.1 q hq
      rw [H.isOp_iff.mp hab] at hq ⊢
      exact H.app_iff.mp ((h a b).mpr (H.app_iff.mpr hq))⟩

/-- `p` is a small sequence into `δ₀`: an increasing function on an ordinal `ξ` of `M` with
values in `δ₀`. -/
def Small (H : Host) (M δ₀ ξ p : H.W) : Prop :=
  ξ ∈ H.ords M ∧ H.IncF p ξ ∧ ∀ i a, H.App p i a → a ∈ δ₀

/-- Below `β`, every ordinal of `M'` above the values of `p` has an equivalent over `p`. -/
def Ap (H : Host) (col r M' p β : H.W) : Prop :=
  β ∈ H.ords M' ∧ ∀ a₀, a₀ ∈ H.ords M' → H.AboveF p a₀ →
    ∃ a, a ∈ β ∧ H.AboveF p a ∧ H.Eqv col r p a a₀

/-- The same for all small sequences into `δ₀`. -/
def ClStep (H : Host) (col r M M' δ₀ β : H.W) : Prop :=
  ∀ ξ p, H.Small M δ₀ ξ p → ∀ a₀, a₀ ∈ H.ords M' → H.AboveF p a₀ →
    ∃ a, a ∈ β ∧ H.AboveF p a ∧ H.Eqv col r p a a₀

/-- `y` is an ordinal of `M'` above the values of `h` and closed for each of them. -/
def GoodD (H : Host) (col r M M' h y : H.W) : Prop :=
  y ∈ H.ords M' ∧ ∀ u z, H.App h u z → z ∈ y ∧ H.ClStep col r M M' z y

/-- The step of the recursion for the closure ordinal. -/
def StepD (H : Host) (col r M M' h v y : H.W) : Prop :=
  (H.GoodD col r M M' h y ∧ ∀ y', H.lt y' y → ¬ H.GoodD col r M M' h y') ∨
    ((¬ ∃ y', H.GoodD col r M M' h y') ∧ y = H.emp ∧ v = v)

/-- `y` is below `δ`, above the values of `h`, and equivalent to `δ` over `h`. -/
def GoodB (H : Host) (col r δ h y : H.W) : Prop :=
  y ∈ δ ∧ H.AboveF h y ∧ H.Eqv col r h y δ

/-- The step of the recursion for the pre-homogeneous sequence. -/
def StepB (H : Host) (col r δ h v y : H.W) : Prop :=
  (H.GoodB col r δ h y ∧ ∀ y', H.lt y' y → ¬ H.GoodB col r δ h y') ∨
    ((¬ ∃ y', H.GoodB col r δ h y') ∧ y = H.emp ∧ v = v)

/-- `w` is an ordinal of `M'` above `z` and closed for `z`. -/
def QD (H : Host) (col r M M' z w : H.W) : Prop :=
  w ∈ H.ords M' ∧ z ∈ w ∧ H.ClStep col r M M' z w

/-- The value of `p` at `i` is a member of the value of `F` at `v`. -/
def QJ (H : Host) (F p i v : H.W) : Prop := ∃ a y, H.App p i a ∧ H.App F v y ∧ a ∈ y

/-- **The setting of one step.** -/
structure ERCtx (H : Host) (M M' C r col : H.W) : Prop where
  hM : H.Closed M
  hM' : H.Closed M'
  hMM' : M ∈ M'
  cons : ∀ x, x ∈ M' → ∃ g, H.IsFun g ∧ (∀ a, a ∈ x → ∃ c, c ∈ M ∧ H.App g a c) ∧
    ∀ a a' c, a ∈ x → a' ∈ x → H.App g a c → H.App g a' c → a = a'
  hC : C ∈ M
  hr : r ∈ H.om
  hcol : H.IsFun col
  ctot : ∀ B, H.Card B (H.suc r) → (∀ z, z ∈ B → z ∈ H.ords M') → ∃ c, c ∈ C ∧ H.App col B c

namespace ERCtx

variable {M M' C r col : H.W} (cx : H.ERCtx M M' C r col)

include cx in
/-- **Over a small sequence there are few types**: below some ordinal of `M'`, every ordinal of
`M'` above the values of `p` has an equivalent. -/
theorem types_bd {p ξ : H.W} (hp : H.IncF p ξ) (hξ : ξ ∈ H.ords M)
    (hpv : ∀ i a, H.App p i a → a ∈ H.ords M') :
    ∃ β, β ∈ H.ords M' ∧ ∀ a₀, a₀ ∈ H.ords M' → H.AboveF p a₀ →
      ∃ a, a ∈ β ∧ H.AboveF p a ∧ H.Eqv col r p a a₀ := by
  have hξM : ξ ∈ M := (H.mem_ords.mp hξ).1
  have hξo : H.On ξ := (H.mem_ords.mp hξ).2
  obtain ⟨P, hP, hPB⟩ := cx.hM.cards_mem hξM (fun z hz => H.on_mem hξo hz) r cx.hr
  have hdefd : ∀ B a, B ∈ P → a ∈ H.ords M' → H.AboveF p a →
      ∃ c, c ∈ C ∧ H.App col (H.bun (H.imgO p B) (H.sg a)) c := by
    intro B a hB ha hab
    obtain ⟨hcard, hsub⟩ := (hPB B).mp hB
    have hci : H.Card (H.imgO p B) r := H.card_img hp.1.1 (D := ξ)
      (fun u v u' v' _ _ h h' huv => hp.2.2 u v u' v' h h' huv) (fun u u' _ h => hp.2.1 u u' h)
      (fun u hu => (hp.1.2 u).mp hu) hsub hcard
    refine cx.ctot _ (H.card_snoc hci (H.mem_ords.mp ha).2 (fun b hb => ?_)) (fun z hz => ?_)
    · obtain ⟨x, -, hxb⟩ := H.mem_imgO.mp hb
      exact hab x b hxb
    · rcases H.mem_bun.mp hz with h | h
      · obtain ⟨x, -, hxz⟩ := H.mem_imgO.mp h
        exact hpv x z hxz
      · rw [H.mem_sg.mp h]
        exact ha
  have hTyEx : ∀ a, a ∈ H.ords M' → H.AboveF p a → ∃ t, t ∈ M ∧ H.IsTy col p P t a := by
    intro a ha hab
    let t := H.mkFun P (fun B c => H.App col (H.bun (H.imgO p B) (H.sg a)) c) (by hdef)
      (fun u _ v v' h h' => cx.hcol.2 _ v v' h h')
    have happ : ∀ {B c : H.W}, H.App t B c ↔
        B ∈ P ∧ H.App col (H.bun (H.imgO p B) (H.sg a)) c := H.app_mkFun
    have hfo : H.FunOn t P := ⟨H.isFun_mkFun, fun B => ⟨fun hB => by
        obtain ⟨c, -, hc⟩ := hdefd B a hB ha hab
        exact ⟨c, happ.mpr ⟨hB, hc⟩⟩, fun ⟨c, hc⟩ => (happ.mp hc).1⟩⟩
    refine ⟨t, cx.hM.fun_mem hfo hP (fun B c h => ?_), hfo, fun B c h => (happ.mp h).2⟩
    obtain ⟨hB, hc⟩ := happ.mp h
    obtain ⟨c', hc'C, hc'⟩ := hdefd B a hB ha hab
    rw [cx.hcol.2 _ c c' hc hc']
    exact cx.hM.trans c' C hc'C cx.hC
  have hTyEqv : ∀ t a a', H.IsTy col p P t a → H.IsTy col p P t a' → H.Eqv col r p a a' := by
    intro t a a' h h' B hB hBp c
    obtain ⟨B₀, hB₀c, hB₀⟩ := H.card_pre hp.1.1 (D := ξ) (fun u hu => H.on_mem hξo hu)
      (fun u v u' v' _ _ k k' huv => hp.2.2 u v u' v' k k' huv)
      (fun y hy => by
        obtain ⟨j, hj⟩ := hBp y hy
        exact ⟨j, (hp.1.2 j).mpr ⟨y, hj⟩, hj⟩) hB
    have hB₀P : B₀ ∈ P := (hPB B₀).mpr ⟨hB₀c, fun z hz => ((hB₀ z).mp hz).1⟩
    have e : H.imgO p B₀ = B := H.ext' fun y => by
      rw [H.mem_imgO]
      constructor
      · rintro ⟨x, hx, hxy⟩
        obtain ⟨-, y', hy', hxy'⟩ := (hB₀ x).mp hx
        rw [hp.1.1.2 x y y' hxy hxy']
        exact hy'
      · intro hy
        obtain ⟨j, hj⟩ := hBp y hy
        exact ⟨j, (hB₀ j).mpr ⟨(hp.1.2 j).mpr ⟨y, hj⟩, y, hy, hj⟩, hj⟩
    obtain ⟨c₀, hc₀⟩ := (h.1.2 B₀).mp hB₀P
    have k1 := h.2 B₀ c₀ hc₀
    have k2 := h'.2 B₀ c₀ hc₀
    rw [e] at k1 k2
    exact ⟨fun hc => by rw [cx.hcol.2 _ c c₀ hc k1]; exact k2,
      fun hc => by rw [cx.hcol.2 _ c c₀ hc k2]; exact k1⟩
  let T := H.sepS M (fun t => ∃ a, a ∈ H.ords M' ∧ H.AboveF p a ∧ H.IsTy col p P t a) (by hdef)
  have hT : ∀ {t : H.W}, t ∈ T ↔ t ∈ M ∧ ∃ a, a ∈ H.ords M' ∧ H.AboveF p a ∧ H.IsTy col p P t a :=
    H.mem_sepS
  have hTM' : T ∈ M' := cx.hM'.sepS_mem cx.hMM' _ _
  let Fw := H.mkFun T (fun t w => H.Rz col p P M' t w ∧ ∀ w', H.lt w' w → ¬ H.Rz col p P M' t w')
    (by hdef) (fun t _ w w' h h' => by
      rcases H.lt_tri w w' with e | e | e
      · exact (h'.2 w e h.1).elim
      · exact e
      · exact (h.2 w' e h'.1).elim)
  have happ : ∀ {t w : H.W}, H.App Fw t w ↔ t ∈ T ∧ (H.Rz col p P M' t w ∧
      ∀ w', H.lt w' w → ¬ H.Rz col p P M' t w') := H.app_mkFun
  have hdom : H.dom Fw = T := H.ext' fun t => by
    rw [H.mem_dom]
    constructor
    · rintro ⟨w, hw⟩
      exact (happ.mp hw).1
    · intro ht
      obtain ⟨-, a, ha, hab, hty⟩ := hT.mp ht
      obtain ⟨m, hm, hmin⟩ := H.least' (fun w => H.Rz col p P M' t w) (by hdef) (a := a)
        ⟨ha, hab, hty⟩
      exact ⟨m, happ.mpr ⟨ht, hm, hmin⟩⟩
  have hdomM' : H.dom Fw ∈ M' := by
    rw [hdom]
    exact hTM'
  obtain ⟨β, hβ, hβv⟩ := cx.hM'.ords_bd H.isFun_mkFun hdomM' (fun t w h => (happ.mp h).2.1.1)
  refine ⟨β, hβ, fun a₀ ha₀ hab₀ => ?_⟩
  obtain ⟨t, htM, hty⟩ := hTyEx a₀ ha₀ hab₀
  have htT : t ∈ T := hT.mpr ⟨htM, a₀, ha₀, hab₀, hty⟩
  obtain ⟨w, hw⟩ : ∃ w, H.App Fw t w := by
    rw [← H.mem_dom, hdom]
    exact htT
  obtain ⟨-, ⟨-, hwab, hwty⟩, -⟩ := happ.mp hw
  exact ⟨w, hβv t w hw, hwab, hTyEqv t w a₀ hwty hty⟩

include cx in
theorem ords_sub {a b : H.W} (hb : b ∈ H.ords M') (ha : a ∈ b) : a ∈ H.ords M' :=
  (H.on_ords cx.hM').1 a b ha hb

include cx in
/-- **One step of closure.** -/
theorem step_bd {δ₀ : H.W} (hδ₀ : δ₀ ∈ H.ords M') :
    ∃ β, β ∈ H.ords M' ∧ H.ClStep col r M M' δ₀ β := by
  have hc := H.def_card
  obtain ⟨g, hg, hgt, hgi⟩ := cx.cons δ₀ (H.mem_ords.mp hδ₀).1
  have huniqP : ∀ q ξ p ξ' p', H.Small M δ₀ ξ p → H.Small M δ₀ ξ' p' → H.IsCompOf q g p →
      H.IsCompOf q g p' → p = p' := by
    have key : ∀ q ξ p ξ' p', H.Small M δ₀ ξ p → H.Small M δ₀ ξ' p' → H.IsCompOf q g p →
        H.IsCompOf q g p' → ∀ i a, H.App p i a → H.App p' i a := by
      intro q ξ p ξ' p' hs hs' hq hq' i a hia
      have haδ := hs.2.2 i a hia
      obtain ⟨c, -, hac⟩ := hgt a haδ
      obtain ⟨v, z, w, e, hvz, hzw⟩ := (hq' (H.op i c)).mp ((hq (H.op i c)).mpr ⟨i, a, c, rfl, hia, hac⟩)
      obtain ⟨e1, e2⟩ := H.op_inj e
      rw [← e1] at hvz
      rw [← e2] at hzw
      rw [hgi a z c haδ (hs'.2.2 i z hvz) hac hzw]
      exact hvz
    intro q ξ p ξ' p' hs hs' hq hq'
    exact H.fun_ext' hs.2.1.1.1 hs'.2.1.1.1 fun i a =>
      ⟨key q ξ p ξ' p' hs hs' hq hq' i a, key q ξ' p' ξ p hs' hs hq' hq i a⟩
  let D₀ := H.sepS M (fun q => ∃ ξ p, H.Small M δ₀ ξ p ∧ H.IsCompOf q g p) (by hdef)
  have hD₀ : ∀ {q : H.W}, q ∈ D₀ ↔ q ∈ M ∧ ∃ ξ p, H.Small M δ₀ ξ p ∧ H.IsCompOf q g p := H.mem_sepS
  have hfun : ∀ q ∈ D₀, ∀ β β', (∃ ξ p, H.Small M δ₀ ξ p ∧ H.IsCompOf q g p ∧ H.Ap col r M' p β ∧
        ∀ β₁, H.lt β₁ β → ¬ H.Ap col r M' p β₁) →
      (∃ ξ p, H.Small M δ₀ ξ p ∧ H.IsCompOf q g p ∧ H.Ap col r M' p β' ∧
        ∀ β₁, H.lt β₁ β' → ¬ H.Ap col r M' p β₁) → β = β' := by
    rintro q - β β' ⟨ξ, p, hs, hq, hA, hmin⟩ ⟨ξ', p', hs', hq', hA', hmin'⟩
    have e := huniqP q ξ p ξ' p' hs hs' hq hq'
    rw [← e] at hA' hmin'
    rcases H.lt_tri β β' with k | k | k
    · exact (hmin' β k hA).elim
    · exact k
    · exact (hmin β' k hA').elim
  let FN := H.mkFun D₀ (fun q β => ∃ ξ p, H.Small M δ₀ ξ p ∧ H.IsCompOf q g p ∧
    H.Ap col r M' p β ∧ ∀ β₁, H.lt β₁ β → ¬ H.Ap col r M' p β₁) (by hdef) hfun
  have happ : ∀ {q β : H.W}, H.App FN q β ↔ q ∈ D₀ ∧ ∃ ξ p, H.Small M δ₀ ξ p ∧
      H.IsCompOf q g p ∧ H.Ap col r M' p β ∧ ∀ β₁, H.lt β₁ β → ¬ H.Ap col r M' p β₁ := H.app_mkFun
  have hval : ∀ ξ p, H.Small M δ₀ ξ p → ∀ i a, H.App p i a → a ∈ H.ords M' :=
    fun ξ p hs i a h => cx.ords_sub hδ₀ (hs.2.2 i a h)
  have hex : ∀ ξ p, H.Small M δ₀ ξ p → ∃ β, H.Ap col r M' p β ∧
      ∀ β₁, H.lt β₁ β → ¬ H.Ap col r M' p β₁ := by
    intro ξ p hs
    obtain ⟨β, hβ, hβa⟩ := cx.types_bd hs.2.1 hs.1 (hval ξ p hs)
    exact H.least' (fun β => H.Ap col r M' p β) (by hdef) (a := β) ⟨hβ, hβa⟩
  have hdom : H.dom FN = D₀ := H.ext' fun q => by
    rw [H.mem_dom]
    constructor
    · rintro ⟨β, hβ⟩
      exact (happ.mp hβ).1
    · intro hq
      obtain ⟨-, ξ, p, hs, hqp⟩ := hD₀.mp hq
      obtain ⟨β, hβ, hmin⟩ := hex ξ p hs
      exact ⟨β, happ.mpr ⟨hq, ξ, p, hs, hqp, hβ, hmin⟩⟩
  have hdomM' : H.dom FN ∈ M' := by
    rw [hdom]
    exact cx.hM'.sepS_mem cx.hMM' _ _
  obtain ⟨βs, hβs, hβv⟩ := cx.hM'.ords_bd H.isFun_mkFun hdomM' (fun q β h => by
    obtain ⟨-, ξ, p, -, -, hA, -⟩ := happ.mp h
    exact hA.1)
  have hβso : H.On βs := (H.mem_ords.mp hβs).2
  refine ⟨βs, hβs, fun ξ p hs a₀ ha₀ hab₀ => ?_⟩
  have hfo : H.FunOn (H.comp g p) ξ := H.funOn_comp hg hs.2.1.1 (fun j v hv => by
    obtain ⟨c, -, hc⟩ := hgt v (hs.2.2 j v hv)
    exact ⟨c, hc⟩)
  have hqM : H.comp g p ∈ M := cx.hM.fun_mem hfo (H.mem_ords.mp hs.1).1 (fun i c h => by
    obtain ⟨z, hz, hzc⟩ := H.app_comp.mp h
    obtain ⟨c', hc', hzc'⟩ := hgt z (hs.2.2 i z hz)
    rw [hg.2 z c c' hzc hzc']
    exact hc')
  have hqD : H.comp g p ∈ D₀ := hD₀.mpr ⟨hqM, ξ, p, hs, H.isCompOf_comp g p⟩
  obtain ⟨β, hβ⟩ : ∃ β, H.App FN (H.comp g p) β := by
    rw [← H.mem_dom, hdom]
    exact hqD
  obtain ⟨-, ξ', p', hs', hq', hA, -⟩ := happ.mp hβ
  have e := huniqP _ ξ p ξ' p' hs hs' (H.isCompOf_comp g p) hq'
  rw [← e] at hA
  obtain ⟨a, ha, hab, heq⟩ := hA.2 a₀ ha₀ hab₀
  exact ⟨a, hβso.1 a β ha (hβv _ β hβ), hab, heq⟩

include cx in
/-- **A closure ordinal**: an ordinal `δ` of `M'` below which every ordinal of `M'` has an
equivalent over every small sequence into `δ`. -/
theorem closure_ord : ∃ δ, δ ∈ H.ords M' ∧ H.ClStep col r M M' δ δ := by
  have hc := H.def_card
  have hempM' : H.emp ∈ H.ords M' := H.mem_ords.mpr ⟨cx.hM'.emp_mem, H.on_emp⟩
  have hmono : ∀ z β β', H.ClStep col r M M' z β → (∀ a, a ∈ β → a ∈ β') →
      H.ClStep col r M M' z β' := fun z β β' h hsub ξ p hs a₀ ha₀ hab₀ =>
    let ⟨a, ha, hab, heq⟩ := h ξ p hs a₀ ha₀ hab₀
    ⟨a, hsub a ha, hab, heq⟩
  have huniq : ∀ h v y y', H.StepD col r M M' h v y → H.StepD col r M M' h v y' → y = y' := by
    rintro h v y y' (⟨hg, hmin⟩ | ⟨hn, e, -⟩) (⟨hg', hmin'⟩ | ⟨hn', e', -⟩)
    · rcases H.lt_tri y y' with k | k | k
      · exact (hmin' y k hg).elim
      · exact k
      · exact (hmin y' k hg').elim
    · exact (hn' ⟨y, hg⟩).elim
    · exact (hn ⟨y', hg'⟩).elim
    · rw [e, e']
  have hex : ∀ h v, ∃ y, H.StepD col r M M' h v y := by
    intro h v
    by_cases hg : ∃ y', H.GoodD col r M M' h y'
    · obtain ⟨y', hy'⟩ := hg
      obtain ⟨m, hm, hmin⟩ := H.least' (fun y => H.GoodD col r M M' h y) (by hdef) hy'
      exact ⟨m, Or.inl ⟨hm, hmin⟩⟩
    · exact ⟨H.emp, Or.inr ⟨hg, rfl, rfl⟩⟩
  have hGd : Def3 H (fun h v y => H.StepD col r M M' h v y) := by hdef
  obtain ⟨F, hF, hFs⟩ := Host.wo_rec (G := fun h v y => H.StepD col r M M' h v y) huniq hGd hex
    (H.ords M)
  have hval : ∀ v y, H.App F v y → y ∈ H.ords M' := by
    intro v y hvy
    obtain ⟨h, -, hs⟩ := hFs v y hvy
    rcases hs with ⟨hg, -⟩ | ⟨-, e, -⟩
    · exact hg.1
    · rw [e]
      exact hempM'
  have hQ : ∀ z, z ∈ H.ords M' → ∃ w, H.QD col r M M' z w := by
    intro z hz
    obtain ⟨β, hβ, hcl⟩ := cx.step_bd hz
    have hzo := (H.mem_ords.mp hz).2
    have hβo := (H.mem_ords.mp hβ).2
    have hzz : z ∈ H.suc z := H.mem_suc.mpr (Or.inr rfl)
    rcases H.on_tri (H.suc z) (H.suc_on hzo) β hβo with k | k | k
    · exact ⟨β, hβ, hβo.1 z _ hzz k, hcl⟩
    · exact ⟨β, hβ, k ▸ hzz, hcl⟩
    · exact ⟨H.suc z, H.ords_suc cx.hM' hz, hzz,
        hmono z β _ hcl (fun a ha => (H.suc_on hzo).1 a β ha k)⟩
  have hgood : ∀ v y h, H.App F v y → H.IsBelow F v h → H.GoodD col r M M' h y := by
    intro v y h hvy hb
    obtain ⟨h', hb', hs⟩ := hFs v y hvy
    rw [Host.isBelow_unique hb' hb] at hs
    rcases hs with ⟨hg, -⟩ | ⟨hn, -, -⟩
    · exact hg
    · exfalso
      apply hn
      have happh : ∀ {u z : H.W}, H.App h u z ↔ H.App F u z ∧ H.lt u v := Host.app_below hb
      have hhfun : ∀ a c c', H.App h a c → H.App h a c' → c = c' :=
        fun a c c' k k' => hF.1.2 a c c' (happh.mp k).1 (happh.mp k').1
      have hdomh : H.dom h ∈ M' := cx.hM'.sub _ (H.ords M) (fun u hu => by
        obtain ⟨z, hz⟩ := H.mem_dom.mp hu
        exact (hF.2 u).mpr ⟨z, (happh.mp hz).1⟩) (cx.hM'.ords_mem cx.hMM')
      have hKfun : ∀ u ∈ H.dom h, ∀ w w', (∃ z, H.App h u z ∧ H.QD col r M M' z w ∧
            ∀ w₁, H.lt w₁ w → ¬ H.QD col r M M' z w₁) →
          (∃ z, H.App h u z ∧ H.QD col r M M' z w' ∧
            ∀ w₁, H.lt w₁ w' → ¬ H.QD col r M M' z w₁) → w = w' := by
        rintro u - w w' ⟨z, hz, hq, hmin⟩ ⟨z', hz', hq', hmin'⟩
        rw [← hhfun u z z' hz hz'] at hq' hmin'
        rcases H.lt_tri w w' with k | k | k
        · exact (hmin' w k hq).elim
        · exact k
        · exact (hmin w' k hq').elim
      let K := H.mkFun (H.dom h) (fun u w => ∃ z, H.App h u z ∧ H.QD col r M M' z w ∧
        ∀ w₁, H.lt w₁ w → ¬ H.QD col r M M' z w₁) (by hdef) hKfun
      have happK : ∀ {u w : H.W}, H.App K u w ↔ u ∈ H.dom h ∧ ∃ z, H.App h u z ∧
          H.QD col r M M' z w ∧ ∀ w₁, H.lt w₁ w → ¬ H.QD col r M M' z w₁ := H.app_mkFun
      have hKtot : ∀ u z, H.App h u z → ∃ w, H.App K u w := by
        intro u z huz
        obtain ⟨w, hw⟩ := hQ z (hval u z (happh.mp huz).1)
        obtain ⟨m, hm, hmin⟩ := H.least' (fun w => H.QD col r M M' z w) (by hdef) hw
        exact ⟨m, happK.mpr ⟨H.mem_dom.mpr ⟨z, huz⟩, z, huz, hm, hmin⟩⟩
      have hdomK : H.dom K = H.dom h := H.ext' fun u => by
        rw [H.mem_dom]
        constructor
        · rintro ⟨w, hw⟩
          exact (happK.mp hw).1
        · intro hu
          obtain ⟨z, hz⟩ := H.mem_dom.mp hu
          exact hKtot u z hz
      have hdomKM' : H.dom K ∈ M' := by
        rw [hdomK]
        exact hdomh
      obtain ⟨y₀, hy₀, hy₀v⟩ := cx.hM'.ords_bd H.isFun_mkFun hdomKM' (fun u w hw => by
        obtain ⟨-, z, -, hq, -⟩ := happK.mp hw
        exact hq.1)
      have hy₀o := (H.mem_ords.mp hy₀).2
      refine ⟨y₀, hy₀, fun u z huz => ?_⟩
      obtain ⟨w, hw⟩ := hKtot u z huz
      obtain ⟨-, z', hz', hq, -⟩ := happK.mp hw
      rw [← hhfun u z z' huz hz'] at hq
      have hwy : w ∈ y₀ := hy₀v u w hw
      exact ⟨hy₀o.1 z w hq.2.1 hwy, hmono z w y₀ hq.2.2 (fun a ha => hy₀o.1 a w ha hwy)⟩
  have hlink : ∀ u v z y, H.App F u z → H.App F v y → H.lt u v →
      z ∈ y ∧ H.ClStep col r M M' z y := by
    intro u v z y huz hvy hlt
    obtain ⟨h, hb, -⟩ := hFs v y hvy
    exact (hgood v y h hvy hb).2 u z ((Host.app_below hb).mpr ⟨huz, hlt⟩)
  have hdomF : H.dom F = H.ords M := H.domIs_unique (H.domIs_dom F) hF.2
  have hdomFM' : H.dom F ∈ M' := by
    rw [hdomF]
    exact cx.hM'.ords_mem cx.hMM'
  have hranM' : H.ran F ∈ M' := cx.hM'.ran_mem hF.1 hdomFM'
    (fun v y h => (H.mem_ords.mp (hval v y h)).1)
  have hδo : H.On (H.un (H.ran F)) := H.on_un_of (fun y hy => by
    obtain ⟨v, hv⟩ := H.mem_ran.mp hy
    exact (H.mem_ords.mp (hval v y hv)).2)
  refine ⟨H.un (H.ran F), H.mem_ords.mpr ⟨cx.hM'.un_mem hranM', hδo⟩,
    fun ξ p hs a₀ ha₀ hab₀ => ?_⟩
  have hQJ : ∀ i a, H.App p i a → ∃ v, H.QJ F p i v := by
    intro i a hia
    obtain ⟨y, hy, hay⟩ := H.mem_un.mp (hs.2.2 i a hia)
    obtain ⟨v, hv⟩ := H.mem_ran.mp hy
    exact ⟨v, a, y, hia, hv, hay⟩
  let J := H.mkFun ξ (fun i v => H.QJ F p i v ∧ ∀ v', H.lt v' v → ¬ H.QJ F p i v') (by hdef)
    (fun i _ v v' k k' => by
      rcases H.lt_tri v v' with e | e | e
      · exact (k'.2 v e k.1).elim
      · exact e
      · exact (k.2 v' e k'.1).elim)
  have happJ : ∀ {i v : H.W}, H.App J i v ↔ i ∈ ξ ∧ (H.QJ F p i v ∧
      ∀ v', H.lt v' v → ¬ H.QJ F p i v') := H.app_mkFun
  have hJtot : ∀ i, i ∈ ξ → ∃ v, H.App J i v := by
    intro i hi
    obtain ⟨a, hia⟩ := (hs.2.1.1.2 i).mp hi
    obtain ⟨v, hv⟩ := hQJ i a hia
    obtain ⟨m, hm, hmin⟩ := H.least' (fun v => H.QJ F p i v) (by hdef) hv
    exact ⟨m, happJ.mpr ⟨hi, hm, hmin⟩⟩
  have hdomJ : H.dom J = ξ := H.ext' fun i => by
    rw [H.mem_dom]
    exact ⟨fun ⟨v, hv⟩ => (happJ.mp hv).1, hJtot i⟩
  have hdomJM : H.dom J ∈ M := by
    rw [hdomJ]
    exact (H.mem_ords.mp hs.1).1
  obtain ⟨vs, hvs, hvsv⟩ := cx.hM.ords_bd H.isFun_mkFun hdomJM (fun i v hv => by
    obtain ⟨-, ⟨a, y, -, hvy, -⟩, -⟩ := happJ.mp hv
    exact (hF.2 v).mpr ⟨y, hvy⟩)
  obtain ⟨ys, hys⟩ := (hF.2 vs).mp hvs
  obtain ⟨yss, hyss⟩ := (hF.2 _).mp (H.ords_suc cx.hM hvs)
  have hyso := (H.mem_ords.mp (hval vs ys hys)).2
  have hpys : ∀ i a, H.App p i a → a ∈ ys := by
    intro i a hia
    obtain ⟨v, hv⟩ := hJtot i ((hs.2.1.1.2 i).mpr ⟨a, hia⟩)
    obtain ⟨-, ⟨a', y, hia', hvy, hay⟩, -⟩ := happJ.mp hv
    rw [← hs.2.1.1.1.2 i a a' hia hia'] at hay
    exact hyso.1 a y hay (hlink v vs y ys hvy hys (H.mem_lt v vs (hvsv i v hv))).1
  obtain ⟨a, ha, hab, heq⟩ := (hlink vs (H.suc vs) ys yss hys hyss
    (H.mem_lt _ _ (H.mem_suc.mpr (Or.inr rfl)))).2 ξ p ⟨hs.1, hs.2.1, hpys⟩ a₀ ha₀ hab₀
  exact ⟨a, H.mem_un.mpr ⟨yss, H.mem_ran.mpr ⟨_, hyss⟩, ha⟩, hab, heq⟩

include cx in
/-- **A pre-homogeneous sequence**: an increasing function `b` from the ordinals of `M` into an
ordinal `δ` of `M'` such that every value gives, with every set of `r` earlier values, the same
colour as `δ`. -/
theorem prehom_exists : ∃ b δ, δ ∈ H.ords M' ∧ H.FunOn b (H.ords M) ∧
    (∀ ξ a, H.App b ξ a → a ∈ δ) ∧ (∀ u v z y, H.App b u z → H.App b v y → u ∈ v → z ∈ y) ∧
    ∀ ξ a, H.App b ξ a → ∀ B, H.Card B r → (∀ z, z ∈ B → ∃ η, η ∈ ξ ∧ H.App b η z) →
      ∀ c, (H.App col (H.bun B (H.sg a)) c ↔ H.App col (H.bun B (H.sg δ)) c) := by
  have hc := H.def_card
  obtain ⟨δ, hδ, hcl⟩ := cx.closure_ord
  have hδo : H.On δ := (H.mem_ords.mp hδ).2
  have hLo : H.On (H.ords M) := H.on_ords cx.hM
  have huniq : ∀ h v y y', H.StepB col r δ h v y → H.StepB col r δ h v y' → y = y' := by
    rintro h v y y' (⟨hg, hmin⟩ | ⟨hn, e, -⟩) (⟨hg', hmin'⟩ | ⟨hn', e', -⟩)
    · rcases H.lt_tri y y' with k | k | k
      · exact (hmin' y k hg).elim
      · exact k
      · exact (hmin y' k hg').elim
    · exact (hn' ⟨y, hg⟩).elim
    · exact (hn ⟨y', hg'⟩).elim
    · rw [e, e']
  have hex : ∀ h v, ∃ y, H.StepB col r δ h v y := by
    intro h v
    by_cases hg : ∃ y', H.GoodB col r δ h y'
    · obtain ⟨y', hy'⟩ := hg
      obtain ⟨m, hm, hmin⟩ := H.least' (fun y => H.GoodB col r δ h y) (by hdef) hy'
      exact ⟨m, Or.inl ⟨hm, hmin⟩⟩
    · exact ⟨H.emp, Or.inr ⟨hg, rfl, rfl⟩⟩
  have hGd : Def3 H (fun h v y => H.StepB col r δ h v y) := by hdef
  obtain ⟨b, hb, hbs⟩ := Host.wo_rec (G := fun h v y => H.StepB col r δ h v y) huniq hGd hex
    (H.ords M)
  have hdomL : ∀ v y, H.App b v y → v ∈ H.ords M := fun v y h => (hb.2 v).mpr ⟨y, h⟩
  have key : ∀ v, v ∈ H.ords M → ∀ y h, H.App b v y → H.IsBelow b v h →
      H.GoodB col r δ h y := by
    refine H.lt_ind (fun v => v ∈ H.ords M → ∀ y h, H.App b v y → H.IsBelow b v h →
      H.GoodB col r δ h y) (by hdef) ?_
    intro v ih hv y h hvy hbel
    obtain ⟨h', hbel', hs⟩ := hbs v y hvy
    rw [Host.isBelow_unique hbel' hbel] at hs
    rcases hs with ⟨hg, -⟩ | ⟨hn, -, -⟩
    · exact hg
    · exfalso
      apply hn
      have hvo : H.On v := H.on_mem hLo hv
      have happh : ∀ {u z : H.W}, H.App h u z ↔ H.App b u z ∧ H.lt u v := Host.app_below hbel
      have hih : ∀ u z, H.App b u z → H.lt u v →
          z ∈ δ ∧ ∀ u' z', H.App b u' z' → H.lt u' u → z' ∈ z := by
        intro u z huz hlt
        obtain ⟨hu', hbu, -⟩ := hbs u z huz
        have hg := ih u hlt (hdomL u z huz) z hu' huz hbu
        exact ⟨hg.1, fun u' z' hu'z' hlt' =>
          hg.2.1 u' z' ((Host.app_below hbu).mpr ⟨hu'z', hlt'⟩)⟩
      have hinc : H.IncF h v := by
        refine ⟨⟨⟨fun q hq => hb.1.1 q ((hbel q).mp hq).1,
          fun a c c' k k' => hb.1.2 a c c' (happh.mp k).1 (happh.mp k').1⟩,
          fun u => ⟨fun hu => ?_, fun ⟨z, hz⟩ => ?_⟩⟩, fun u z huz => ?_,
          fun u u' z z' huz hu'z' huu' => ?_⟩
        · obtain ⟨z, hz⟩ := (hb.2 u).mp (hLo.1 u v hu hv)
          exact ⟨z, happh.mpr ⟨hz, H.mem_lt u v hu⟩⟩
        · obtain ⟨hz1, hz2⟩ := happh.mp hz
          exact (H.on_lt_iff (H.on_mem hLo (hdomL u z hz1)) hvo).mp hz2
        · obtain ⟨hz1, hz2⟩ := happh.mp huz
          exact H.on_mem hδo (hih u z hz1 hz2).1
        · obtain ⟨h1, h2⟩ := happh.mp huz
          obtain ⟨h1', h2'⟩ := happh.mp hu'z'
          exact (hih u' z' h1' h2').2 u z h1 (H.mem_lt u u' huu')
      have hsm : H.Small M δ v h :=
        ⟨hv, hinc, fun u z huz => (hih u z (happh.mp huz).1 (happh.mp huz).2).1⟩
      obtain ⟨a, ha, hab, heq⟩ := hcl v h hsm δ hδ (fun u z huz => hsm.2.2 u z huz)
      exact ⟨a, ha, hab, heq⟩
  have hgoodAll : ∀ v y, H.App b v y → ∃ h, H.IsBelow b v h ∧ H.GoodB col r δ h y := by
    intro v y hvy
    obtain ⟨h, hbel, -⟩ := hbs v y hvy
    exact ⟨h, hbel, key v (hdomL v y hvy) y h hvy hbel⟩
  refine ⟨b, δ, hδ, hb, fun ξ a h => ?_, fun u v z y huz hvy huv => ?_,
    fun ξ a hξa B hB hBsub c => ?_⟩
  · obtain ⟨h', -, hg⟩ := hgoodAll ξ a h
    exact hg.1
  · obtain ⟨h', hbel, hg⟩ := hgoodAll v y hvy
    exact hg.2.1 u z ((Host.app_below hbel).mpr ⟨huz, H.mem_lt u v huv⟩)
  · obtain ⟨h', hbel, hg⟩ := hgoodAll ξ a hξa
    exact hg.2.2 B hB (fun z hz => by
      obtain ⟨η, hη, hηz⟩ := hBsub z hz
      exact ⟨η, (Host.app_below hbel).mpr ⟨hηz, H.mem_lt η ξ hη⟩⟩) c

end ERCtx

/-! ## Part 3: the partition theorem -/

/-- `col` is a colouring of the sets of `r` members of `A`, with colours in `C`. -/
def ColOn (H : Host) (col r A C : H.W) : Prop :=
  H.IsFun col ∧ ∀ B, H.Card B r → (∀ z, z ∈ B → z ∈ A) → ∃ c, c ∈ C ∧ H.App col B c

/-- All sets of `r` members of `X` have the same colour. -/
def HomC (H : Host) (col r X : H.W) : Prop :=
  ∀ B B' c c', H.Card B r → H.Card B' r → (∀ z, z ∈ B → z ∈ X) → (∀ z, z ∈ B' → z ∈ X) →
    H.App col B c → H.App col B' c' → c = c'

/-- **The step of the partition theorem.** If every colouring of the sets of `r` ordinals of
`M` has a large homogeneous set, then every colouring of the sets of `r + 1` ordinals of `M'`
has one. -/
theorem ERCtx.succ {M M' C r col : H.W} (cx : H.ERCtx M M' C r col)
    (ih : ∀ col₁, H.ColOn col₁ r (H.ords M) C →
      ∃ X, (∀ x, x ∈ X → x ∈ H.ords M) ∧ H.Large X ∧ H.HomC col₁ r X) :
    ∃ X, (∀ x, x ∈ X → x ∈ H.ords M') ∧ H.Large X ∧ H.HomC col (H.suc r) X := by
  obtain ⟨b, δ, hδ, hb, hbδ, hbinc, hpre⟩ := cx.prehom_exists
  have hδo : H.On δ := (H.mem_ords.mp hδ).2
  have hLo : H.On (H.ords M) := H.on_ords cx.hM
  have hLord : ∀ u, u ∈ H.ords M → H.On u := fun u hu => (H.mem_ords.mp hu).2
  have hbtot : ∀ u, u ∈ H.ords M → ∃ u', H.App b u u' := fun u hu => (hb.2 u).mp hu
  have hbinc' : ∀ u v u' v', u ∈ H.ords M → v ∈ H.ords M → H.App b u u' → H.App b v v' →
      u ∈ v → u' ∈ v' := fun u v u' v' _ _ h h' huv => hbinc u v u' v' h h' huv
  have hbon : ∀ u u', u ∈ H.ords M → H.App b u u' → H.On u' :=
    fun u u' _ h => H.on_mem hδo (hbδ u u' h)
  have hbrefl : ∀ u v u' v', u ∈ H.ords M → v ∈ H.ords M → H.App b u u' → H.App b v v' →
      u' ∈ v' → u ∈ v := by
    intro u v u' v' hu hv h h' hlt
    rcases H.on_tri u (hLord u hu) v (hLord v hv) with e | e | e
    · exact e
    · rw [e] at h
      rw [hb.1.2 v u' v' h h'] at hlt
      exact (H.mem_irrefl _ hlt).elim
    · exact (H.mem_asymm hlt (hbinc v u v' u' h' h e)).elim
  have hbinj : ∀ u v w, u ∈ H.ords M → v ∈ H.ords M → H.App b u w → H.App b v w → u = v := by
    intro u v w hu hv h h'
    rcases H.on_tri u (hLord u hu) v (hLord v hv) with e | e | e
    · exact (H.mem_irrefl _ (hbinc u v w w h h' e)).elim
    · exact e
    · exact (H.mem_irrefl _ (hbinc v u w w h' h e)).elim
  obtain ⟨P, -, hPB⟩ := cx.hM'.cards_mem (cx.hM'.ords_mem cx.hMM') hLord r cx.hr
  -- the induced colouring
  have hdefd : ∀ B, B ∈ P → ∃ c, c ∈ C ∧ H.App col (H.bun (H.imgO b B) (H.sg δ)) c := by
    intro B hB
    obtain ⟨hcard, hsub⟩ := (hPB B).mp hB
    have hci : H.Card (H.imgO b B) r := H.card_img hb.1 hbinc' hbon hbtot hsub hcard
    refine cx.ctot _ (H.card_snoc hci hδo (fun y hy => ?_)) (fun z hz => ?_)
    · obtain ⟨x, -, hxy⟩ := H.mem_imgO.mp hy
      exact hbδ x y hxy
    · rcases H.mem_bun.mp hz with h | h
      · obtain ⟨x, -, hxz⟩ := H.mem_imgO.mp h
        exact cx.ords_sub hδ (hbδ x z hxz)
      · rw [H.mem_sg.mp h]
        exact hδ
  let col₁ := H.mkFun P (fun B c => H.App col (H.bun (H.imgO b B) (H.sg δ)) c) (by hdef)
    (fun u _ v v' h h' => cx.hcol.2 _ v v' h h')
  have happ : ∀ {B c : H.W}, H.App col₁ B c ↔
      B ∈ P ∧ H.App col (H.bun (H.imgO b B) (H.sg δ)) c := H.app_mkFun
  have hcol₁ : H.ColOn col₁ r (H.ords M) C := ⟨H.isFun_mkFun, fun B hB hsub => by
    have hBP : B ∈ P := (hPB B).mpr ⟨hB, hsub⟩
    obtain ⟨c, hc, hcc⟩ := hdefd B hBP
    exact ⟨c, hc, happ.mpr ⟨hBP, hcc⟩⟩⟩
  obtain ⟨X, hXsub, hXL, hXhom⟩ := ih col₁ hcol₁
  -- every set of `r + 1` members of the image has the colour of a set of `r` members of `X`
  have hkey : ∀ B' c, H.Card B' (H.suc r) → (∀ z, z ∈ B' → z ∈ H.imgO b X) → H.App col B' c →
      ∃ B₀, H.Card B₀ r ∧ (∀ z, z ∈ B₀ → z ∈ X) ∧ H.App col₁ B₀ c := by
    intro B' c hcard hsub hc
    obtain ⟨B₁, x', hB₁, -, hbel, hx'B, hB₁B, e⟩ := H.card_suc_inv hcard
    obtain ⟨ξ, hξX, hξx'⟩ := H.mem_imgO.mp (hsub x' hx'B)
    have hB₁X : ∀ z, z ∈ B₁ → ∃ η, η ∈ X ∧ H.App b η z :=
      fun z hz => H.mem_imgO.mp (hsub z (hB₁B z hz))
    have hB₁ξ : ∀ z, z ∈ B₁ → ∃ η, η ∈ ξ ∧ H.App b η z := by
      intro z hz
      obtain ⟨η, hηX, hηz⟩ := hB₁X z hz
      exact ⟨η, hbrefl η ξ z x' (hXsub η hηX) (hXsub ξ hξX) hηz hξx' (hbel z hz), hηz⟩
    rw [e] at hc
    have hc' := (hpre ξ x' hξx' B₁ hB₁ hB₁ξ c).mp hc
    obtain ⟨B₀, hB₀c, hB₀⟩ := H.card_pre hb.1 hLord hbinc'
      (fun y hy => by
        obtain ⟨η, hηX, hηy⟩ := hB₁X y hy
        exact ⟨η, hXsub η hηX, hηy⟩) hB₁
    have hB₀X : ∀ z, z ∈ B₀ → z ∈ X := by
      intro z hz
      obtain ⟨hzL, y, hy, hzy⟩ := (hB₀ z).mp hz
      obtain ⟨η, hηX, hηy⟩ := hB₁X y hy
      rw [hbinj z η y hzL (hXsub η hηX) hzy hηy]
      exact hηX
    have eimg : H.imgO b B₀ = B₁ := H.ext' fun y => by
      rw [H.mem_imgO]
      constructor
      · rintro ⟨x, hx, hxy⟩
        obtain ⟨-, y', hy', hxy'⟩ := (hB₀ x).mp hx
        rw [hb.1.2 x y y' hxy hxy']
        exact hy'
      · intro hy
        obtain ⟨η, hηX, hηy⟩ := hB₁X y hy
        exact ⟨η, (hB₀ η).mpr ⟨hXsub η hηX, y, hy, hηy⟩, hηy⟩
    refine ⟨B₀, hB₀c, hB₀X, happ.mpr ⟨(hPB B₀).mpr ⟨hB₀c, fun z hz => hXsub z (hB₀X z hz)⟩, ?_⟩⟩
    rw [eimg]
    exact hc'
  refine ⟨H.imgO b X, fun y hy => ?_, ⟨?_, fun y hy => ?_⟩, fun B B' c c' hB hB' hs hs' hc hc' => ?_⟩
  · obtain ⟨x, -, hxy⟩ := H.mem_imgO.mp hy
    exact cx.ords_sub hδ (hbδ x y hxy)
  · obtain ⟨x, hx⟩ := hXL.1
    obtain ⟨y, hy⟩ := hbtot x (hXsub x hx)
    exact ⟨y, H.mem_imgO.mpr ⟨x, hx, hy⟩⟩
  · obtain ⟨x, hx, hxy⟩ := H.mem_imgO.mp hy
    obtain ⟨x₂, hx₂, hxx₂⟩ := hXL.2 x hx
    obtain ⟨y₂, hy₂⟩ := hbtot x₂ (hXsub x₂ hx₂)
    exact ⟨y₂, H.mem_imgO.mpr ⟨x₂, hx₂, hy₂⟩, hbinc x x₂ y y₂ hxy hy₂ hxx₂⟩
  · obtain ⟨B₀, hB₀, hB₀X, hc₀⟩ := hkey B c hB hs hc
    obtain ⟨B₀', hB₀', hB₀X', hc₀'⟩ := hkey B' c' hB' hs' hc'
    exact hXhom B₀ B₀' c c' hB₀ hB₀' hB₀X hB₀X' hc₀ hc₀'

/-- The numeral of a standard number. -/
noncomputable def nmr (H : Host) : ℕ → H.W
  | 0 => H.emp
  | n + 1 => H.suc (nmr H n)

theorem nmr_mem_om : ∀ n : ℕ, H.nmr n ∈ H.om
  | 0 => H.emp_mem_om
  | n + 1 => H.suc_mem_om (nmr_mem_om n)

/-- **A sequence of consecutive closed levels** `Ms 0 ∈ … ∈ Ms n`: every member of a level maps
one-to-one into the level before, by a function of the host. `C` is a member of `Ms 0`. -/
structure LevSeq (H : Host) (Ms : ℕ → H.W) (C : H.W) (n : ℕ) : Prop where
  closed : ∀ j, j ≤ n → H.Closed (Ms j)
  mem : ∀ j, j < n → Ms j ∈ Ms (j + 1)
  cons : ∀ j, j < n → ∀ x, x ∈ Ms (j + 1) → ∃ g, H.IsFun g ∧
    (∀ a, a ∈ x → ∃ c, c ∈ Ms j ∧ H.App g a c) ∧
    ∀ a a' c, a ∈ x → a' ∈ x → H.App g a c → H.App g a' c → a = a'
  hC : C ∈ Ms 0

theorem LevSeq.mono {Ms : ℕ → H.W} {C : H.W} {n m : ℕ} (h : H.LevSeq Ms C n) (hm : m ≤ n) :
    H.LevSeq Ms C m :=
  ⟨fun j hj => h.closed j (by omega), fun j hj => h.mem j (by omega),
    fun j hj => h.cons j (by omega), h.hC⟩

theorem LevSeq.C_mem {Ms : ℕ → H.W} {C : H.W} {n : ℕ} (h : H.LevSeq Ms C n) :
    ∀ j, j ≤ n → C ∈ Ms j
  | 0, _ => h.hC
  | j + 1, hj => (h.closed (j + 1) hj).trans C (Ms j) (LevSeq.C_mem h j (by omega))
      (h.mem j (by omega))

/-- **The partition theorem.** For a standard `n` and consecutive closed levels
`Ms 0 ∈ … ∈ Ms n`, every colouring of the sets of `n` ordinals of `Ms n` with colours in a
member of `Ms 0` has a homogeneous set of ordinals of `Ms n` with a member and without a
largest member. -/
theorem er {Ms : ℕ → H.W} {C : H.W} : ∀ (n : ℕ), H.LevSeq Ms C n → ∀ col,
    H.ColOn col (H.nmr n) (H.ords (Ms n)) C →
    ∃ X, (∀ x, x ∈ X → x ∈ H.ords (Ms n)) ∧ H.Large X ∧ H.HomC col (H.nmr n) X
  | 0, hl, col, hcol => by
    have hM := hl.closed 0 le_rfl
    refine ⟨H.ords (Ms 0), fun x hx => hx, ⟨⟨H.emp, H.mem_ords.mpr ⟨hM.emp_mem, H.on_emp⟩⟩,
      fun x hx => ⟨H.suc x, H.ords_suc hM hx, H.mem_suc.mpr (Or.inr rfl)⟩⟩,
      fun B B' c c' hB hB' _ _ hc hc' => ?_⟩
    rw [H.card_emp_iff.mp hB] at hc
    rw [H.card_emp_iff.mp hB'] at hc'
    exact hcol.1.2 _ c c' hc hc'
  | n + 1, hl, col, hcol => by
    have cx : H.ERCtx (Ms n) (Ms (n + 1)) C (H.nmr n) col :=
      { hM := hl.closed n (by omega)
        hM' := hl.closed (n + 1) le_rfl
        hMM' := hl.mem n (by omega)
        cons := hl.cons n (by omega)
        hC := hl.C_mem n (by omega)
        hr := H.nmr_mem_om n
        hcol := hcol.1
        ctot := hcol.2 }
    exact cx.succ (fun col₁ hcol₁ => er n (hl.mono (by omega)) col₁ hcol₁)

/-- A set of ordinals with a member and without a largest member has increasing sequences of
every length. -/
theorem large_seq {X : H.W} (hX : H.Large X) (hXo : ∀ x, x ∈ X → H.On x) :
    ∀ k, k ∈ H.om → ∃ s, H.IncSeq s k ∧ ∀ i a, H.App s i a → a ∈ X := by
  have hd := H.def_incSeq
  have key := H.om_ind (fun k => ∃ s y, H.IncSeq s k ∧ (∀ i a, H.App s i a → a ∈ X) ∧ y ∈ X ∧
    ∀ i a, H.App s i a → a ∈ y) (by hdef) (by
      obtain ⟨x, hx⟩ := hX.1
      exact ⟨H.emp, x, H.incSeq_emp, fun i a h => (H.not_mem_emp _ (H.app_iff.mp h)).elim, hx,
        fun i a h => (H.not_mem_emp _ (H.app_iff.mp h)).elim⟩) (by
      rintro k - ⟨s, y, hs, hsX, hy, hsy⟩
      obtain ⟨y₂, hy₂, hyy₂⟩ := hX.2 y hy
      refine ⟨H.ins s k y, y₂, hs.snoc (hXo y hy) hsy, fun i a h => ?_, hy₂, fun i a h => ?_⟩
      · rcases H.app_ins.mp h with h1 | ⟨-, h1⟩
        · exact hsX i a h1
        · rw [h1]
          exact hy
      · rcases H.app_ins.mp h with h1 | ⟨-, h1⟩
        · exact (hXo y₂ hy₂).1 a y (hsy i a h1) hyy₂
        · rw [h1]
          exact hyy₂)
  intro k hk
  obtain ⟨s, y, hs, hsX, -, -⟩ := key k hk
  exact ⟨s, hs, hsX⟩

/-- **The partition theorem, for sequences.** There is a homogeneous increasing sequence of
every length. -/
theorem er_seq {Ms : ℕ → H.W} {C : H.W} {n : ℕ} (hl : H.LevSeq Ms C n) {col : H.W}
    (hcol : H.ColOn col (H.nmr n) (H.ords (Ms n)) C) {k : H.W} (hk : k ∈ H.om) :
    ∃ s, H.IncSeq s k ∧ (∀ i a, H.App s i a → a ∈ H.ords (Ms n)) ∧
      ∀ B B' c c', H.Card B (H.nmr n) → H.Card B' (H.nmr n) → H.SubV B s → H.SubV B' s →
        H.App col B c → H.App col B' c' → c = c' := by
  obtain ⟨X, hXsub, hXL, hXhom⟩ := H.er n hl col hcol
  obtain ⟨s, hs, hsX⟩ := H.large_seq hXL (fun x hx => (H.mem_ords.mp (hXsub x hx)).2) k hk
  refine ⟨s, hs, fun i a h => hXsub a (hsX i a h), fun B B' c c' hB hB' hBs hBs' hc hc' => ?_⟩
  exact hXhom B B' c c' hB hB'
    (fun z hz => by
      obtain ⟨j, hj⟩ := hBs z hz
      exact hsX j z hj)
    (fun z hz => by
      obtain ⟨j, hj⟩ := hBs' z hz
      exact hsX j z hj) hc hc'

end Host
