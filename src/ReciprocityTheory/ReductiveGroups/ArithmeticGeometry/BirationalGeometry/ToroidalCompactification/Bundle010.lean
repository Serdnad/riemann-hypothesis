module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Aesop.BuiltinRules
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

section Chart

variable {X X' Y Y' : Scheme.{0}}

structure ChartPull (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) where
  idx : A'.ι → A.ι
  le : ∀ i, A'.U i ≤ h ⁻¹ᵁ A.U (idx i)
  g : ∀ (y : Y') i j, y ∈ A'.U i → y ∈ A'.U j →
    gm (𝟙 Y') y (A'.U i ⊓ A'.U j) (A'.g i j) = gm h y (A.U (idx i) ⊓ A.U (idx j)) (A.g (idx i) (idx j))

theorem gm_div {Z : Scheme.{0}} (A B : LB Y) (r : Z ⟶ Y) (z : Z) (p q : B.ι × A.ι)
    (hm : r z ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) :
    gm r z (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) ((LB.div B A).g p q) =
      gm r z _ (B.g p.1 q.1) * (gm r z _ (A.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hm _))))

theorem LBIso.chartPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (H : LBIso A B) : LBIso A' B' := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ p : B'.ι × A'.ι, B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) := fun p y hy =>
    ⟨b.le _ hy.1, a.le _ hy.2⟩
  refine ⟨⟨fun p => res (le p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩, fun p q => unit_ext fun y hy => ?_⟩
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ (res (le p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))) =
        gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) := fun p hp =>
    (gm_res (𝟙 Y') y (le p) hp _).trans ((gm_pull (𝟙 Y') h y _ (le p hp) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2))))
    (hw (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B h y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hm) (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val p hy.1)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div A' B' (𝟙 Y') y p q hy).trans ?_)
    ((gm_res (𝟙 Y') y _ hy _).trans (val q hy.2)))
  rw [a.g y _ _ hy.1.2 hy.2.2, b.g y _ _ hy.1.1 hy.2.1]

theorem gm_linComb {Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (j j' : K → L.ι) (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') =
      ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ (show r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' from ⟨hj, hj'⟩) _).trans
    (gm_pull r (φ k) z (L.U (j k) ⊓ L.U (j' k)) ⟨Set.mem_iInter.1 hj k, Set.mem_iInter.1 hj' k⟩ _)

theorem gm_pull_g {Z : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (r : Z ⟶ X') (z : Z) (J J' : PUnit → L.ι)
    (hj : r z ∈ (L.pull F).U J) (hj' : r z ∈ (L.pull F).U J') :
    gm r z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) :=
  (gm_linComb L (fun _ : PUnit => F) (fun _ => 1) r z J J' hj hj').trans (by rw [Fintype.prod_unique, zpow_one])

def chartPullPull (L : LB X) (F h : X' ⟶ X) (e : h = F) : ChartPull (L.pull F) L h where
  idx J := J PUnit.unit
  le J y hy := by subst e; exact mem_pull.1 hy
  g y J J' hj hj' := by subst e; exact (gm_pull_g L h (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp])

def chartPullLinComb (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) : ChartPull (LB.LinComb (L.pull F) φ' ε) (LB.LinComb L φ ε) h :=
  have le : ∀ j : K → PUnit → L.ι, LB.wchart (L.pull F) φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := mem_pull.1 (Set.mem_iInter.1 hy k)
      show φ k (h y) ∈ L.U (j k PUnit.unit)
      rw [pt_eq hc]; exact this
  { idx := fun j k => j k PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb (L.pull F) φ' ε (𝟙 Y') y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (gm_pull_g L F (𝟙 Y' ≫ φ' k) y (j k) (j' k) (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k)).trans ?_
      rw [Category.id_comp, hc] }

end Chart

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem psum_hom {T : Over S} {T' : Over S'} (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (I : Finset (Fin n)) : ρ (psum G' x I) = psum G (fun i => ρ (x i)) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact map_one ρ
  | cons k l ih => exact (map_mul ρ _ _).trans (congrArg (ρ (x k) * ·) ih)


omit [IsCommMonObj G] [IsCommMonObj G'] in
def pushHom (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (pushPt h.1.w) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm


omit [IsCommMonObj G] in
def preHom {T T' : Over S} (U : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (U ≫ ·) fun x y => MonObj.comp_mul U x y

theorem psum_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (I : Finset (Fin n)) : (psum G' x' I).left ≫ φ = U.left ≫ (psum G x I).left := by
  have e : pushPt h.1.w (psum G' x' I) = U ≫ psum G x I :=
    (psum_hom (pushHom h T') x' I).trans ((congrArg (fun z => psum G z I) (funext hx)).trans
      (psum_hom (preHom U) x I).symm)
  exact congrArg (fun z => z.left) e

def cubeMapOf (h : IsGrpPullback G' G f φ) : CubeMap G' G where
  F := φ
  F3 := (lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))).left
  e := f
  e_comm := by
    have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
    have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [e₁] at e
    refine e.trans ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  psum_comm I := psum_push h _ _ _ (fun i => by fin_cases i <;> simp [x3]) I

omit [IsCommMonObj G] in
theorem isGrpPullback_pullback (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left := fun a => pullback.lift_fst _ _ _
  refine ⟨IsPullback.of_hasPullback _ _, fun T x y x₀ y₀ hx hy => ?_⟩
  let z : T ⟶ (Over.pullback f).obj (G ⊗ G) := lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl

end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
      (m : SABMap ⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
        sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
  · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
    refine LBIso.chartPull (chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

private theorem exists_global_unit_of_compatible_of_iSup_eq {X : Scheme.{0}} {J : Type} (U : J → X.Opens) (hU : ⨆ i, U i = ⊤)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  have hc : (⊤ : X.Opens) ≤ iSup U := hU.ge
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hc
    (fun i => (r i).val) (fun i j => congrArg Units.val (hr i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hc
    (fun i => ((r i)⁻¹).val)
    (fun i j => congrArg Units.val (show res (inf_le_left : U i ⊓ U j ≤ U i) (r i)⁻¹ =
      res (inf_le_right : U i ⊓ U j ≤ U j) (r j)⁻¹ by rw [map_inv, map_inv, hr i j]))
  have hss : s * s' = 1 := by
    refine X.sheaf.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hc _ _ fun i => ?_
    have h1 := hs i
    have h2 := hs' i
    rw [map_mul, map_one, h1, h2]
    exact (r i).mul_inv
  exact ⟨Units.mkOfMulEqOne (s : Γ(X, ⊤)) s' hss, fun i => Units.ext (hs i)⟩

private theorem units_eq_of_res_eq_of_le_iSup {Y : Scheme.{0}} {J : Type} (V : J → Y.Opens) (W : Y.Opens) (hVW : ∀ i, V i ≤ W)
    (hW : W ≤ ⨆ i, V i) (s t : Γ(Y, W)ˣ) (h : ∀ i, res (hVW i) s = res (hVW i) t) : s = t :=
  Units.ext (Y.sheaf.eq_of_locally_eq' V W (fun i => homOfLE (hVW i)) hW _ _ fun i => congrArg Units.val (h i))

private theorem app_rs_eq_rs_app' {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} (U' : X.Opens) (hU : U' ≤ U) {V : Y.Opens}
    (h1 : V ≤ f ⁻¹ᵁ U') (h2 : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h2 (pullU f U x) = res h1 (pullU f U' (res hU x)) := by
  apply Units.ext
  change (f.app U ≫ Y.presheaf.map (homOfLE h2).op).hom x.val =
    (X.presheaf.map (homOfLE hU).op ≫ f.app U' ≫ Y.presheaf.map (homOfLE h1).op).hom x.val
  rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  rfl

private theorem apply_default_eq_of_prod_eq_of_unique {K G : Type*} [Fintype K] [Unique K] [CommMonoid G] (f g : K → G)
    (h : ∏ k, f k = ∏ k, g k) : f default = g default := by
  rwa [Fintype.prod_unique, Fintype.prod_unique] at h

theorem iso_unique_of_rig (hG : Out.GlobalFnsSt) {S X₀ : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    {M : LB A.left} {M₀ : LB X₀} (hM : M.IsLB) (hM₀ : M₀.IsLB) {φ : A.left ⟶ X₀}
    {w₁ w₂ : LB.Iso M (M₀.pull φ)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) {a : LB.Gen (M.pull (eSec A))}
    {b : LB.Gen ((M₀.pull φ).pull (eSec A))}
    (m₁ : LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) a b)
    (m₂ : LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) a b) : w₁ = w₂ := by
  have hcov : ⨆ q, (LB.div (M₀.pull φ) M).U q = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx₀ : φ.base x ∈ (⨆ i, M₀.U i) := by rw [hM₀.cover]; trivial
    have hx : x ∈ (⨆ j, M.U j) := by rw [hM.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₀
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => i, j), ?_⟩
    exact ⟨Set.mem_iInter.2 fun _ => hi, hj⟩
  obtain ⟨u, hu⟩ := exists_global_unit_of_compatible_of_iSup_eq (LB.div (M₀.pull φ) M).U hcov (fun q => w₁.s q / w₂.s q) fun q q' => by
    rw [map_div, map_div, g₁ q q', g₂ q q']
    exact mul_div_mul_left_eq_div _ _ _
  have hcovY : (eSec A) ⁻¹ᵁ (⊤ : A.left.Opens) ≤
      ⨆ p, (LB.div ((M₀.pull φ).pull (eSec A)) (M.pull (eSec A))).U p := by
    intro y _
    have hx : (eSec A).base y ∈ (⨆ q, (LB.div (M₀.pull φ) M).U q) := by rw [hcov]; trivial
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => q.1, fun _ => q.2), ?_⟩
    exact ⟨Set.mem_iInter.2 fun _ => hq.1, Set.mem_iInter.2 fun _ => hq.2⟩
  have hc : pullU (eSec A) ⊤ u = 1 := by
    refine units_eq_of_res_eq_of_le_iSup _ _ (fun _ _ _ => by trivial) hcovY _ _ fun p => ?_
    rw [map_one]
    have E := mul_right_cancel ((m₁ p).symm.trans (m₂ p))
    simp only [id_eq, LB.linCombIso, Fintype.prod_unique, zpow_one] at E
    refine (app_rs_eq_rs_app' (eSec A) ((LB.div (M₀.pull φ) M).U (p.1 default, p.2 default)) le_top ?_ _ u).trans ?_
    · exact le_inf (inf_le_left.trans (LB.wchart_le _ _ p.1 default))
        (inf_le_right.trans (LB.wchart_le _ _ p.2 default))
    · refine (congrArg (fun z => res _ (pullU (eSec A) _ z)) (hu (p.1 default, p.2 default))).trans ?_
      try dsimp only
      rw [map_div, map_div, div_eq_one]
      exact apply_default_eq_of_prod_eq_of_unique _ _ E
  have hc' : (eSec A).appTop.hom (u : Γ(A.left, ⊤)) = 1 := congrArg Units.val hc
  obtain ⟨v, hv⟩ := (hG S A hA).2 (u : Γ(A.left, ⊤))
  have hw : eSec A ≫ A.hom = (𝟙_ (Over S)).hom := by
    exact Over.w _
  have key : (eSec A).appTop.hom (A.hom.appTop.hom v) = v := by
    have h3 : (eSec A).appTop.hom (A.hom.appTop.hom v) = (eSec A ≫ A.hom).appTop.hom v := by
      rfl
    rw [h3, hw]
    rfl
  have hv1 : v = 1 := by rw [← key, hv]; exact hc'
  have hu1 : u = 1 := Units.ext (by rw [← hv, hv1, map_one, Units.val_one])
  have hq : ∀ q, w₁.s q = w₂.s q := fun q => by
    have h := hu q
    rw [hu1, map_one] at h
    exact div_eq_one.1 h.symm
  cases w₁
  cases w₂
  congr 1
  funext q
  exact hq q

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
