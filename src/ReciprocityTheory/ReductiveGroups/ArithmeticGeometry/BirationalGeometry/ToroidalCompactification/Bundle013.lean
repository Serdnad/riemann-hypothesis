module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Chart

variable {R : Type} [CommRing R] {Gx : Over (Spec (CommRingCat.of R))} [GrpObj Gx] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ Gx} (hx : IsUnivChart Gx n x)

include hx in
theorem tvec_inj {c c' : Fin n → R} (h : tvec (x := x) c = tvec (x := x) c') : c = c' := by
  rw [← tcoord_tvec hx c, ← tcoord_tvec hx c']
  exact tcoord_congr hx h _ _

theorem list_prod_tan' : ∀ {M : ℕ} (u : Fin M → (sp (R₀ := R) (DualNumber R) ⟶ Gx)) (hu : ∀ i, IsTan (u i)),
    ∃ h : IsTan (List.ofFn u).prod, tcoord hx _ h = ∑ i, tcoord hx (u i) (hu i) := by
  intro M
  induction M with
  | zero =>
    intro u hu
    have e0 : (List.ofFn u).prod = 1 := by simp
    refine ⟨e0 ▸ isTan_one, ?_⟩
    rw [tcoord_congr hx e0 _ isTan_one, tcoord_one]
    simp
  | succ M ih =>
    intro u hu
    obtain ⟨h, e⟩ := ih (fun i => u i.succ) (fun i => hu i.succ)
    have e0 : (List.ofFn u).prod = u 0 * (List.ofFn fun i => u i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    refine ⟨e0 ▸ isTan_mul (hu 0) h, ?_⟩
    rw [tcoord_congr hx e0 _ (isTan_mul (hu 0) h), tcoord_mul hx (hu 0) h, e, Fin.sum_univ_succ]

theorem mem_eigLat_iff {O : Type} (act : O → (Gx ⟶ Gx)) [∀ a, IsMonHom (act a)] (χ : O → R) (c : Fin n → R) :
    c ∈ eigLat hx act χ ↔ ∀ a, tmap hx (act a) c = χ a • c := by
  simp only [eigLat, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem tvec_eig_iff (e : Gx ⟶ Gx) [IsMonHom e] (c : Fin n → R) (s : R) :
    tvec (x := x) c ≫ e = spMap (scaleD s) ≫ tvec (x := x) c ↔ tmap hx e c = s • c := by
  rw [← tvec_tmap hx, ← tvec_smul hx]
  exact ⟨fun h => tvec_inj hx h, fun h => by rw [h]⟩

end Chart

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)

include hc in
theorem rel_eq_iff {X : Over (Spec (CommRingCat.of k))} {w₁ w₂ : viaT tk X ⟶ G'} {v₁ v₂ : X ⟶ (Over.pullback g).obj G}
    (h₁ : Rel (F := F) tk g w₁ v₁) (h₂ : Rel (F := F) tk g w₂ v₂) : w₁ = w₂ ↔ v₁ = v₂ := by
  constructor
  · rintro rfl
    exact rel_uniq_v h₁ h₂
  · rintro rfl
    exact rel_uniq_w hc h₁ h₂

include hc hg in
theorem tan_iff {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk tk ⟶ G').left ↔ IsTan v := by
  have h1 := rel_pre (spMap (fstD k)) h
  have h2 := rel_one hc hg (X := sp (R₀ := k) k)
  have hid : (sp (R₀ := k) k).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e1 : (1 : viaT tk (sp (R₀ := k) k) ⟶ G').left = (1 : Over.mk tk ⟶ G').left := by
    rw [one_left', one_left']
    show ((sp (R₀ := k) k).hom ≫ tk) ≫ _ = tk ≫ _
    rw [hid, Category.id_comp]
  rw [IsTan, ← rel_eq_iff hc h1 h2]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    exact e.trans e1.symm
  · intro e
    exact (congrArg (fun q => q.left) e).trans e1

include hc in
theorem eig_iff (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) (s : k)
    {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    (w ≫ a).left = Geo.Tor.spMap (Geo.Tor.epsScale s) ≫ w.left ↔ v ≫ (Over.pullback g).map b = spMap (scaleD s) ≫ v := by
  rw [← rel_eq_iff hc (rel_act a b hab h) (rel_pre (spMap (scaleD s)) h)]
  constructor
  · intro e
    exact Over.OverMorphism.ext e
  · intro e
    exact congrArg (fun q => q.left) e

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)


include hc hg hab hact' in
theorem finrank_of_lieMult {N : ℕ} (hL : Geo.Tor.LieMult act tk τ N) :
    Module.finrank k (eigLat hx act' (fun a => τ a)) = N := by
  obtain ⟨vB, hvB, huq⟩ := hL
  have hT : ∀ (w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') v, Rel (F := F) tk g w v →
      (Geo.Tor.IsLieEigen act tk τ w ↔ IsTan v ∧ ∀ a, v ≫ act' a = spMap (scaleD (τ a)) ≫ v) := by
    intro w v h
    refine and_congr (tan_iff hc hg h) (forall_congr' fun a => ?_)
    rw [hact']
    exact eig_iff hc (act.act a) (b a) (hab a) (τ a) h
  choose v' hv' using fun i => rel_exists_v hc hg (X := sp (R₀ := k) (DualNumber k)) (vB i)
  have hv'e : ∀ i, IsTan (v' i) ∧ ∀ a, v' i ≫ act' a = spMap (scaleD (τ a)) ≫ v' i :=
    fun i => (hT _ _ (hv' i)).mp (hvB i)
  let bb : Fin N → Fin n → k := fun i => tcoord hx (v' i) (hv'e i).1
  have htv : ∀ i, tvec (x := x) (bb i) = v' i := fun i => (tcoord_spec hx _ _).symm
  have hmem : ∀ c, c ∈ eigLat hx act' (fun a => τ a) ↔ ∀ a, tvec (x := x) c ≫ act' a = spMap (scaleD (τ a)) ≫ tvec (x := x) c := by
    intro c
    rw [mem_eigLat_iff]
    exact forall_congr' fun a => (tvec_eig_iff hx (act' a) c (τ a)).symm
  have hbW : ∀ i, bb i ∈ eigLat hx act' (fun a => τ a) := fun i => (hmem _).mpr fun a => by
    rw [htv]
    exact (hv'e i).2 a
  let P : (Fin N → k) → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G) :=
    fun d => (List.ofFn fun i => spMap (scaleD (d i)) ≫ v' i).prod
  let Wd : (Fin N → k) → (viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') :=
    fun d => (List.ofFn fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i).prod
  have hPW : ∀ d, Rel (F := F) tk g (Wd d) (P d) := fun d => rel_prod hc hg _ _ fun i => rel_pre _ (hv' i)
  have hPeq : ∀ d, P d = tvec (x := x) (∑ i, d i • bb i) := by
    intro d
    obtain ⟨h, e⟩ := list_prod_tan' hx (fun i => spMap (scaleD (d i)) ≫ v' i) (fun i => isTan_scale (d i) (hv'e i).1)
    refine (tcoord_spec hx (P d) h).trans ?_
    show tvec (x := x) (tcoord hx (P d) h) = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun i _ => tcoord_scale hx (d i) (hv'e i).1
  have hsum : ∀ d : Fin N → k, (∑ i, d i • bb i) ∈ eigLat hx act' (fun a => τ a) := fun d =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbW i)
  have hWeig : ∀ d : Fin N → k, Geo.Tor.IsLieEigen act tk τ (Wd d) := fun d => (hT _ _ (hPW d)).mpr
    ⟨by rw [hPeq]; exact isTan_tvec hx _, by rw [hPeq]; exact (hmem _).mp (hsum d)⟩
  have hsat : ∀ d : Fin N → k, ∃ u : Fin N → (Geo.Tor.epsPt tk ⟶ G'),
      (∀ i, (u i).left = Geo.Tor.spMap (Geo.Tor.epsScale (d i)) ≫ (vB i).left) ∧ Wd d = (List.ofFn u).prod :=
    fun d => ⟨fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i, fun i => rfl, rfl⟩
  have hli : LinearIndependent k bb := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    have e1 : P d = P 0 := by
      rw [hPeq, hPeq, hd]
      simp
    have e2 : Wd d = Wd 0 := (rel_eq_iff hc (hPW d) (hPW 0)).mpr e1
    have := (huq (Wd 0) (hWeig 0)).unique (e2 ▸ hsat d) (hsat 0)
    exact fun i => congrFun this i
  have hspan : eigLat hx act' (fun a => τ a) = Submodule.span k (Set.range bb) := by
    apply le_antisymm
    · intro c hc'
      obtain ⟨w, hw⟩ := rel_exists_w hc hg (tvec (x := x) c)
      obtain ⟨d, ⟨u, hu, hwu⟩, -⟩ := huq w ((hT _ _ hw).mpr ⟨isTan_tvec hx c, (hmem c).mp hc'⟩)
      have hu' : u = fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i :=
        funext fun i => Over.OverMorphism.ext (hu i)
      have e1 : w = Wd d := by rw [hwu, hu']
      have e2 : tvec (x := x) c = P d := rel_uniq_v (e1 ▸ hw) (hPW d)
      rw [hPeq] at e2
      rw [tvec_inj hx e2]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hbW i
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end Count

section Assembly

theorem pushR_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
    (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) (e : G ⟶ G) :
    pushR G (y ≫ (Over.pullback (fB R R')).map e) = pushR G y ≫ e := by
  apply Over.OverMorphism.ext
  rw [pushR_left, Over.comp_left, Over.comp_left, pushR_left, Category.assoc, Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

end Assembly

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Hom

variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]

def preH {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) : (X ⟶ M) →* (Y ⟶ M) :=
  MonoidHom.mk' (f ≫ ·) fun a b => MonObj.comp_mul f a b

theorem pre_prod {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) {d : ℕ} (v : Fin d → (X ⟶ M)) :
    f ≫ (List.ofFn v).prod = (List.ofFn fun i => f ≫ v i).prod := by
  have h := map_list_prod (preH (M := M) f) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

theorem scale_prodPts {d : ℕ} (a : R) (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ M)) :
    spMap (scaleD a) ≫ prodPts c v = prodPts (a • c) v := by
  unfold prodPts
  rw [pre_prod]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  have hs : (scaleD a).comp (scaleD (c i)) = scaleD ((a • c) i) := by
    apply AlgHom.ext
    intro x
    refine TrivSqZeroExt.ext ?_ ?_
    all_goals (simp only [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, AlgHom.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Pi.smul_apply]; try ring)
  rw [← Category.assoc, spMap_comp, hs]

end Hom

section Push

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]

def pushforwardHom : (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) :=
  MonoidHom.mk' (pushR G) fun a b => by
    show iotaB ≫ Geo.Tor.pushPt _ (a * b) = (iotaB ≫ Geo.Tor.pushPt _ a) * (iotaB ≫ Geo.Tor.pushPt _ b)
    rw [← MonObj.comp_mul]
    congr 1
    exact map_mul (Geo.Tor.pushHom (Geo.Tor.isGrpPullback_pullback G (fB R R')) _) a b

theorem pushR_prod {d : ℕ} (v : Fin d → (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G)) :
    pushR G (List.ofFn v).prod = (List.ofFn fun i => pushR G (v i)).prod := by
  have h := map_list_prod (pushforwardHom (R := R) (R' := R') (P := P) G) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h

end Push

theorem isGrpPullback_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {F : G''.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G'' G (g ≫ f) F) :
    Geo.Tor.IsGrpPullback G'' ((Over.pullback f).obj G) g
      (pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc])) := by
  have hfst : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.fst G.hom f = F := pullback.lift_fst _ _ _
  have hsnd : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫
      pullback.snd G.hom f = G''.hom ≫ g := pullback.lift_snd _ _ _
  have hP := Geo.Tor.isGrpPullback_pullback G f
  refine ⟨?_, ?_⟩
  · refine IsPullback.of_right ?_ hsnd (IsPullback.of_hasPullback G.hom f)
    rw [hfst]
    exact h.1
  · intro T x y x₀ y₀ hx hy
    apply pullback.hom_ext
    · let x₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (x₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w x₀))
      let y₀' : Over.mk ((Over.mk (T.hom ≫ g)).hom ≫ f) ⟶ G :=
        Over.homMk (y₀.left ≫ pullback.fst G.hom f) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ f) (Over.w y₀))
      let x₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (x.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w x) =≫ (g ≫ f))
      let y₀'' : Over.mk (T.hom ≫ g ≫ f) ⟶ G :=
        Over.homMk (y.left ≫ F) (by
          rw [Category.assoc, h.1.w]
          simpa using (Over.w y) =≫ (g ≫ f))
      have e1 : (x₀' * y₀').left = (x₀ * y₀).left ≫ pullback.fst G.hom f :=
        hP.2 _ x₀ y₀ x₀' y₀' rfl rfl
      have e2 : (x₀'' * y₀'').left = (x * y).left ≫ F := h.2 T x y x₀'' y₀'' rfl rfl
      have e3 : (x₀' * y₀').left = (x₀'' * y₀'').left := by
        refine Geo.Tor.mul_left_congr (Category.assoc T.hom g f) x₀' y₀' x₀'' y₀'' ?_ ?_
        · show x₀.left ≫ pullback.fst G.hom f = x.left ≫ F
          rw [hx, Category.assoc, hfst]
        · show y₀.left ≫ pullback.fst G.hom f = y.left ≫ F
          rw [hy, Category.assoc, hfst]
      rw [Category.assoc, hfst, ← e1, e3, e2]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x * y)]
      exact Over.w (x₀ * y₀)

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section GV

variable {X Y Y' : Scheme.{0}} (M : LB X)

def GV (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → M.ι), (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb M φ ε)), u.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ Z r z J, Good M z J → val u r z J = v Z r z J

variable {M} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} {v v'}

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  first
    | (rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
    | (rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    | simp [← Functor.map_comp_apply]
    | simp


end GV

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (hG : GlobalFnsSt)
  (hA : IsAbelianScheme A)
include c hG hA

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem twist_of_val {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ} {M : LB A.left}
    (hM : M.IsLB) {α : LB.Gen (LB.LinComb M (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    {s : LB.Sec (LPow A M b T)} {s' : LB.Sec (LPow A M a T)} (h : ∀ z J, Good M z J →
      sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) z J =
      (val α (𝟙 _) z J).val * sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) z J) :
    IsTwistPull A M ψ m hm a b α s s' := fun j => fn_ext fun z hz => by
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hM (χ z)
  have hz' : (𝟙 (T ⊗ A).left : _ ⟶ _) z ∈ LB.wchart M ![(snd T A).left, m.left] j := hz
  have a₁ := (gs_res (𝟙 _) z (chart_le_zero A M m j) hz' (s'.f fun _ => j 0)).trans
    (sec_trans (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) z (chart_le_zero A M m j hz')
      (Good.mem hJ _ _))
  have a₂ := ((gs_res (𝟙 _) z (chart_le_pull A M ψ m hm j) hz' ((ψ.left.app _).hom (s.f fun _ => j 1))).trans
    (gs_pull (𝟙 _) ψ.left z (LB.wchart M (fun _ : Fin 1 => (snd T A).left) fun _ => j 1) (chart_le_pull A M ψ m hm j hz') _)).trans
    (sec_trans (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) z
      (chart_le_pull A M ψ m hm j hz') (Good.mem hJ _ _))
  have a₃ := (gs_unit (𝟙 _) z _ hz' (α.s j)).trans (congrArg Units.val (gen_trans hα (𝟙 _) z hz' (Good.mem hJ _ _)))
  refine a₁.trans (Eq.trans ?_ ((gs_mul (𝟙 _) z _ hz' _ _).trans (congrArg₂ (· * ·) a₃ a₂)).symm)
  refine (congrArg (_ * ·) (h z J hJ)).trans ?_
  have e : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, ← Over.comp_left, hm]
  have t : trF (L := M) (K := Fin 2) ![(snd T A).left, m.left] ![a, -b] (𝟙 _) z j
        (fun k => J (𝟙 _ ≫ (![(snd T A).left, m.left] : Fin 2 → _) k)) *
      trF (L := M) (fun _ : Fin 1 => (snd T A).left) (fun _ => b) (𝟙 _ ≫ ψ.left) z (fun _ => j 1)
        (fun _ => J ((𝟙 _ ≫ ψ.left) ≫ (snd T A).left)) =
      trF (L := M) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _) z (fun _ => j 0) (fun _ => J (𝟙 _ ≫ (snd T A).left)) := by
    rw [trF, trF, trF, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e]
    exact (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) ((congrArg (· * _) (zpow_neg _ _)).trans (inv_mul_cancel _))).trans
      (_root_.mul_one _))
  rw [← t, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]
  rfl

variable [IsCommMonObj A] {L : RigLB A}

theorem isMonHom_mulA (n : ℕ) : IsMonHom (mulA A n) := by
  constructor
  · rw [mulA, MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
  · have e := MonObj.mul_eq_mul A
    rw [mulA, MonObj.comp_pow, Category.comp_id]
    conv_lhs => rw [e, mul_pow]
    rw [e, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id]

omit [IsCommMonObj A] [GrpObj A] in
theorem prod_end (φ : A ⟶ A) {a b : ℕ} {a' b' : ℤ} (ha : a' = a) (hb : b' = b) {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U]
    (h : (T.left ⟶ A.left) → U) : ∏ i, h (y.left ≫ (![𝟙 A.left, φ.left] : Fin 2 → _) i) ^ (![a', -b'] : Fin 2 → ℤ) i =
      h y.left ^ a * (h (y ≫ φ).left ^ b)⁻¹ := by
  subst ha hb
  rw [Fin.prod_univ_two]
  simp [Over.comp_left, zpow_neg, zpow_natCast]


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
