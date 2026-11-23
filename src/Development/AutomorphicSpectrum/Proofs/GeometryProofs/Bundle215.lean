module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle207
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle211
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle107
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpBuild
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSheetChartHolo
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem gm_comp_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp R') (z : Z) :
    gm (r ≫ spMap f) z ⊤ (unitOn u) = gm r z ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  refine (gm_pull r (spMap f) z ⊤ trivial (unitOn u)).symm.trans (congrArg (gm r z ⊤) ?_)
  apply Units.ext
  exact (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

def FG.scaled {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (a : FG M Y) (c : Γ(Y, ⊤)ˣ) : FG M Y :=
  ⟨a.K, a.φ, a.ε, scaleGen a.t c, scaleGen_isGen hM a.t a.ht c⟩

theorem FG.v_scaled {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (a : FG M Y) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) : (a.scaled hM c).v r z J = gm r z ⊤ c * a.v r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem a.φ r) _) rfl)

theorem exists_root_in_ext (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 1 ≤ n) (c : Kˣ) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (u : K'ˣ),
      u ^ n = Units.map (algebraMap K K').toMonoidHom c := by
  let P : Polynomial K := Polynomial.X ^ n - Polynomial.C (c : K)
  have hdeg : P.degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (by omega)]
    exact_mod_cast (by omega : n ≠ 0)
  have : FiniteDimensional ℚ P.SplittingField := Module.Finite.trans K _
  obtain ⟨ρ, hρ⟩ := (Polynomial.IsSplittingField.splits P.SplittingField P).exists_eval_eq_zero
    (by rwa [Polynomial.degree_map])
  have hρn : ρ ^ n = algebraMap K P.SplittingField (c : K) := by
    simpa [P, sub_eq_zero, Polynomial.eval_map] using hρ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hρn
    exact (map_ne_zero _).2 c.ne_zero hρn.symm
  refine ⟨P.SplittingField, inferInstance, NumberField.mk, inferInstance, Units.mk0 ρ hρ0, Units.ext ?_⟩
  simpa using hρn

theorem exists_gen_normalised {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Field K] [NumberField K] (n : ℕ)
    (hn : 1 ≤ n) (xl : Sp K ⟶ X) (A : FG M (Sp K))
    (hA : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), A.sum U h = (h xl ^ n)⁻¹) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (e : FG M (Sp K')),
      (∀ (U : Type) [CommGroup U] (h : (Sp K' ⟶ X) → U), e.sum U h = h (spMap (algebraMap K K') ≫ xl)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K') (z : Z) (J), Good M z J →
        e.v r z J ^ n * A.v (r ≫ spMap (algebraMap K K')) z J = 1 := by
  obtain ⟨z₀⟩ : Nonempty (Sp K) := inferInstance
  choose d hd using fun χ : Sp K ⟶ X => exists_chart hM (χ z₀)
  have hJ₀ : Good M z₀ d := hd
  obtain ⟨t₀, ht₀, -⟩ := GlobalTheory.ThetaInValues.exists_gen_of_value hM (fun _ : PUnit => xl) (fun _ => (1 : ℤ)) hJ₀ (1 : Kˣ)
  let e₀ : FG M (Sp K) := ⟨PUnit, _, _, t₀, ht₀⟩
  have hs₀ : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), e₀.sum U h = h xl := by
    intro U _ h
    show ∏ _k : PUnit, h xl ^ (1 : ℤ) = _
    simp
  have hg : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), ((e₀.pow n).mul A).sum U h = 1 := by
    intro U _ h
    rw [FG.sum_mul, FG.sum_pow, hs₀, hA]
    exact _root_.mul_inv_cancel _
  obtain ⟨c, hc⟩ := FG.exists_unit hM _ hg
  let c₀ : Kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c
  have hcc : unitOn c₀ = c := by
    apply Units.ext
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val
  obtain ⟨K', iF, iN, iA, u, hu⟩ := exists_root_in_ext K n hn c₀⁻¹
  refine ⟨K', iF, iN, iA, (e₀.pull (spMap (algebraMap K K'))).scaled hM (unitOn u), ?_, ?_⟩
  · intro U _ h
    exact hs₀ U fun q => h (spMap (algebraMap K K') ≫ q)
  · intro Z r z J hJ
    have key : unitOn u ^ n * unitOn (Units.map (algebraMap K K').toMonoidHom c₀) = 1 := by
      have e1 : unitOn u ^ n = unitOn (u ^ n) := (map_pow _ _ _).symm
      have e2 : ∀ a b : K'ˣ, unitOn a * unitOn b = unitOn (a * b) := fun a b => (map_mul _ _ _).symm
      rw [e1, e2, hu, ← map_mul, inv_mul_cancel, map_one]
      exact map_one _
    rw [FG.v_scaled hM _ _ r hJ, FG.v_pull hJ, _root_.mul_pow, _root_.mul_assoc, ← FG.v_pow hJ, ← FG.v_mul hJ,
      hc Z _ z J hJ, ← hcc, gm_comp_spMap_unitOn, ← map_pow, ← map_mul, key, map_one]

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CombVal

section General

variable {S S' : Scheme.{0}} {G : CategoryTheory.Over S} {G' : CategoryTheory.Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem push_mul (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b)
    (x y : CategoryTheory.Over.mk a ⟶ G') (x₀ y₀ : CategoryTheory.Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hab
  exact h.2 (CategoryTheory.Over.mk a) x y x₀ y₀ hx hy

theorem push_one (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b) :
    (1 : CategoryTheory.Over.mk b ⟶ G).left = (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ := by
  subst hab
  exact (congrArg (fun z => z.left) (map_one (pushHom h (CategoryTheory.Over.mk a)))).symm

theorem one_left_congr {A : Scheme.{0}} {a b : A ⟶ S} (h : a = b) :
    (1 : CategoryTheory.Over.mk a ⟶ G).left = (1 : CategoryTheory.Over.mk b ⟶ G).left := by
  subst h
  rfl

theorem push_mul₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) (x y : CategoryTheory.Over.mk a ⟶ G') (x' y' : CategoryTheory.Over.mk a₂ ⟶ G₂)
    (hx : x.left ≫ φ = x'.left ≫ φ₂) (hy : y.left ≫ φ = y'.left ≫ φ₂) :
    (x * y).left ≫ φ = (x' * y').left ≫ φ₂ := by
  have wx : (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w x]
    rfl
  have wy : (y.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w y]
    rfl
  let W : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (x.left ≫ φ) wx
  let W' : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (y.left ≫ φ) wy
  exact (push_mul h rfl x y W W' rfl rfl).symm.trans (push_mul h₂ hab.symm x' y' W W' hx hy)

theorem push_one₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) :
    (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ = (1 : CategoryTheory.Over.mk a₂ ⟶ G₂).left ≫ φ₂ :=
  (push_one h hab).symm.trans (push_one h₂ rfl)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {F : Type} [Field F] [Algebra c.F F]

abbrev qe (y : FrPt Xo c F) : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.XF c :=
  spMap (algebraMap F (DualNumber F)) ≫ Small.ptF y

theorem qe_fst (y : FrPt Xo c F) : qe y ≫ pullback.fst _ _ = spMap (algebraMap F (DualNumber F)) ≫ y.x := by
  rw [Category.assoc, Small.ptF_fst]

def liftP (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G :=
  CategoryTheory.Over.homMk (Y.m0.cart.1.lift p.left (qe y) ((CategoryTheory.Over.w p).trans (qe_fst y).symm)) (Y.m0.cart.1.lift_snd _ _ _)

theorem pointLift_fst (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) :
    (liftP Y y p).left ≫ Y.m0.toSABMap.φ = p.left :=
  Y.m0.cart.1.lift_fst _ _ _

theorem pointLift_eq (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) (P : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G)
    (h : P.left ≫ Y.m0.toSABMap.φ = p.left) : (liftP Y y p).left = P.left := by
  apply Y.m0.cart.1.hom_ext
  · exact (pointLift_fst Y y p).trans h.symm
  · exact (CategoryTheory.Over.w (liftP Y y p)).trans (CategoryTheory.Over.w P).symm

variable {Y : Model Xo c β} {X : Scheme.{0}} {tX : SAB H X} {f : X ⟶ Y.X} (m : SABMap tX Y.t f)
  {g : Spec (CommRingCat.of F) ⟶ X} {EC : Type} [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC)
  (y : FrPt Xo c F)

def Rd (p : tEps y.x ⟶ Xo.univ.t.G) (e : EC) : Prop :=
  (MC.pt e).left ≫ m.φ = (liftP Y y p).left ≫ Y.m.φ

variable {y}

theorem base_eq (hY : Small.ptY Y y = g ≫ f) :
    (spMap (algebraMap F (DualNumber F)) ≫ g) ≫ f = qe y ≫ Y.jQ ≫ pullback.fst _ _ := by
  rw [Category.assoc, Category.assoc, ← hY]
  rfl

theorem pt_zero : MC.pt 0 = 1 := by
  have h := MC.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem rd_one (hY : Small.ptY Y y = g ≫ f) : Rd m MC y 1 0 := by
  have h1 : (liftP Y y 1).left = (1 : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G).left := by
    refine pointLift_eq Y y 1 1 ?_
    exact ((push_one Y.m0.cart (qe_fst y)).symm).trans (one_left_congr rfl)
  unfold Rd
  rw [h1, pt_zero]
  exact push_one₂ m.cart Y.m.cart (base_eq hY)

theorem rd_mul (hY : Small.ptY Y y = g ≫ f) {p p' : tEps y.x ⟶ Xo.univ.t.G} {e e' : EC}
    (h : Rd m MC y p e) (h' : Rd m MC y p' e') : Rd m MC y (p * p') (e + e') := by
  have h1 : (liftP Y y (p * p')).left = (liftP Y y p * liftP Y y p').left := by
    refine pointLift_eq Y y _ _ ?_
    exact (push_mul Y.m0.cart (qe_fst y) (liftP Y y p) (liftP Y y p') p p'
      (pointLift_fst Y y p).symm (pointLift_fst Y y p').symm).symm
  unfold Rd
  rw [h1, MC.add]
  exact push_mul₂ m.cart Y.m.cart (base_eq hY) (MC.pt e) (MC.pt e') (liftP Y y p) (liftP Y y p') h h'

theorem scale_base (a : F) : spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap F (DualNumber F)) =
    spMap (algebraMap F (DualNumber F)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem rd_smul {p p₂ : tEps y.x ⟶ Xo.univ.t.G} {e : EC} (a : F)
    (hp : p₂.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ p.left) (h : Rd m MC y p e) :
    Rd m MC y p₂ (a • e) := by
  have h1 : (liftP Y y p₂).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (liftP Y y p).left := by
    apply Y.m0.cart.1.hom_ext
    · rw [pointLift_fst, Category.assoc, pointLift_fst, hp]
    · have e₁ := CategoryTheory.Over.w (liftP Y y p)
      have e₂ := CategoryTheory.Over.w (liftP Y y p₂)
      refine e₂.trans ?_
      rw [Category.assoc, e₁]
      show qe y = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ qe y
      rw [qe, ← Category.assoc, scale_base]
  unfold Rd at h ⊢
  rw [h1, MC.smul, Category.assoc, Category.assoc, h]
  rfl

theorem rd_prod (hY : Small.ptY Y y = g ≫ f) :
    ∀ (n : ℕ) (u : Fin n → (tEps y.x ⟶ Xo.univ.t.G)) (e : Fin n → EC), (∀ i, Rd m MC y (u i) (e i)) →
      Rd m MC y (List.ofFn u).prod (∑ i, e i)
  | 0, u, e, _ => by
    simpa using rd_one m MC hY
  | n + 1, u, e, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact rd_mul m MC hY (h 0) (rd_prod hY n _ _ fun i => h i.succ)

end CombVal

theorem comb_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, Formalism.L2.Pj.IsTanAt y.x (v j)) (e : Fin n → EC), (∀ j, (MC.pt (e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y (v j) (hv j).1) → ∀ (cf : Fin n → F) (w : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left), IsCombAt y.x v cf w → ∃ hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y.x, (MC.pt (∑ j, cf j • e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y w hw := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hY n v hv e he cf w hc
  obtain ⟨u, hu, rfl⟩ := hc
  refine ⟨CategoryTheory.Over.w ((List.ofFn u).prod), ?_⟩
  have h0 : ∀ j, CombVal.Rd m MC y (CategoryTheory.Over.homMk (v j) (hv j).1 : tEps y.x ⟶ Xo.univ.t.G) (e j) := he
  have h1 : ∀ j, CombVal.Rd m MC y (u j) (cf j • e j) := fun j => CombVal.rd_smul m MC (cf j) (hu j) (h0 j)
  exact CombVal.rd_prod m MC hY n u (fun j => cf j • e j) h1

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chartForm_regular_of_mem_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (u : Module.Dual Ω 𝔐.Li), u ∈ P.Dh.om → ∀ v : 𝔐.Li, (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → v ∈ 𝔐.M.lat q) → u v ∈ CR O y c' := by
  exact @PositivityTheory.Xgn.sequence_family_pairing

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.hodge_comp_descent_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover | exact GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.root_origin_frame_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∃ B : Finset RM.Ω, ∀ A : Subring RM.Ω, (↑B : Set RM.Ω) ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : RM.Ω))⁻¹ ∈ A) → FinRd.GoodRing Fr A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance : Inputs → AvoidStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → CmpSt := by
  intro hIn hAv hRes II hII K _ ι _ K₁ _ ι₁ _ K₂ _ ι₂ _ κ₁ v₁ κ₂ v₂ Ω _ _ y D σ _ S₁ S₂ Re₁ Re₂ β b
    hb₁ hb₂ hAr hβ hβy halg₁ halg₂ hsing w
  obtain ⟨K', _, ι', _, κ, v, y', S, Re, f, g, d, hbl, hyv, hfield, hdeg, ht₁, ht₂, hpull, hiso,
    hsm, hph, hrel⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cmp.BuildK.joint_system hIn hRes K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ Re₁ Re₂ β b
      hb₁ hb₂ hAr hβ hβy halg₁ halg₂ hsing
  have hlim := GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.cmp_one hIn hAv II hII K' ι' (mCoordIdeal y') D σ S Re f g d
    hiso hsm hph hrel w
  have hpos₁ : 0 < S₁.t₀ := (S₁.reg (w 0)).1
  have hpos₂ : 0 < S₂.t₀ := (S₂.reg (w 0)).1
  have hPF : HasPFCoord II := hII.2.2.1
  refine hlim.congr' ?_
  have hmem : Set.Ioc (0 : ℝ) (min S₁.t₀ S₂.t₀) ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (lt_min hpos₁ hpos₂)
  filter_upwards [hmem] with t ht
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.CoordK.side_eq II hPF Re₁ Re Sum.inl hb₁ hbl hyv hfield hdeg
      (fun a t => (hpull a t).1) w t ht.1 (le_trans ht.2 (min_le_left _ _)),
    GlobalTheory.CompanionTheory.Ar.Cmp.CoordK.side_eq II hPF Re₂ Re Sum.inr hb₂ hbl hyv hfield hdeg
      (fun a t => (hpull a t).2) w t ht.1 (le_trans ht.2 (min_le_right _ _))]
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.StokesCompare

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

end Clauses

section Mass

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem degMu_nonneg (X : ComponentSetting D O Lt) : 0 ≤ degMu X.H := by
  classical
  have hN := MuHomDensityNonneg.proof (MuSheetLeviNonneg.proof SheetChartHolo.proof RefAlongSheet.proof)
  have hdeg : degMu X.H = ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) (fun _ => 1) := rfl
  rw [hdeg]
  unfold ptsIntegral
  split_ifs with hΨ
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hN II Ψ K ι Ω E D O Lt X _ hΨ.choose_spec] with y hy
    exact finsum_nonneg fun w => finsum_nonneg fun _ => hy w
  · exact le_rfl

end Mass

end GlobalTheory.CompanionTheory.StokesCompare
end
end

section

namespace GlobalTheory.CompanionTheory.Ggeo

theorem blockProjection_genericPoints_good : GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement :=
  GlobalTheory.CompanionTheory.Ar.PB.BaseCount.generic_points_good_for_intersection

end GlobalTheory.CompanionTheory.Ggeo
end
