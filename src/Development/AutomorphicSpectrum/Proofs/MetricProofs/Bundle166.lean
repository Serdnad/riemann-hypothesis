module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle123
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle134
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle163
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle161
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle164
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.height_comparison_between_models : Top.Given → PtsIntegrableStatement →
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem)
      (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
      (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
      (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M M' : XModel D)
      (S : LogLogRegularisationSetting M D.Xo (muLine Hd))
      (S₁ : LogLogRegularisationSetting M' D.Xo (muLine Hd)) (B : ℕ),
      IsFullIntersectionSystem II → S.IsTied → S₁.IsTied →
      ArLimExists Hd S B ∧ arLim Hd S B = arLim Hd S₁ B := by
  intro hG _ K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M M' S S₁ B hII hS hS₁
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hNb : IsSmoothHerm (fsHerm J (muTwDeg Hd B)) := PB.StepW.fsHerm_isSmoothHerm K J _
  have h₁ := tendsto_arLimFun hIn.metricLocal S hS B hII _ hNb rfl
  have h₂ := tendsto_arLimFun hIn.metricLocal S₁ hS₁ B hII _ hNb rfl
  exact ⟨⟨_, h₁⟩, by rw [arLim, arLim, h₁.limUnder_eq, h₂.limUnder_eq]⟩
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isometric_toZ_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (t : X ⟶ Sp ℤ) (t' : Y ⟶ Sp ℤ) (π : Y ⟶ X) (hπ : π ≫ p = q) (hπ' : π ≫ t = t') (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (hL' : ∀ τ, (wZ (L.pull π hπ) t' τ).IsCInf), (toZ (L.pull π hπ) t' hL').Isometric ((toZ L t hL).pull π hπ') := by
  intro k _ X Y p q t t' π hπ hπ' L hL hL'
  refine HermLB.isometric_of_eqOn fun τ a y _ => ?_
  have key : ∀ (σ σ' : k →+* ℂ) (_ : σ = σ') (z : CxPts p σ) (z' : CxPts p σ'), z.1 = z'.1 →
      (L.φ σ).φ (a PUnit.unit) z = (L.φ σ').φ (a PUnit.unit) z' := by
    rintro σ _ rfl z z' h
    rw [Subtype.ext h]
  refine (Weight.pull_φ (wZ L t τ) π hπ' a y).trans (Eq.trans ?_ (Weight.pull_φ (L.φ (emb q y)) π hπ a (unsheet q y)).symm)
  refine key _ _ ?_ _ _ rfl
  have e : (PtsOver.map π hπ' _ y).1 ≫ p = y.1 ≫ q := by
    rw [← hπ]
    exact Category.assoc _ _ _
  show (Spec.preimage ((PtsOver.map π hπ' _ y).1 ≫ p)).hom = (Spec.preimage (y.1 ≫ q)).hom
  rw [e]

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem toZ_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (L M : HermLB p)
    (hL : ∀ τ, (wZ L t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf), L.Isometric M →
    (toZ L t hL).Isometric (toZ M t hM) := by
  intro k _ X p t L M hL hM ⟨w, hw, h⟩
  refine ⟨w, hw, fun τ a b y ha hb => ?_⟩
  exact h (emb p y) a b (unsheet p y) ha hb

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.chernDensity_sheet_eq : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart t τ D), (∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y) → ∀ y ∈ c.e.source, c'.chernDens ψ (sheet t τ y) = c.chernDens (φ σ) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet | exact GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.logNorm_sheet_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → ∀ (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (σ : k →+* ℂ) (y : CxPts p σ), y ∈ offSupp p σ (divOfRatSec ψ.isLB hr) → logNorm ψ r (sheet t τ y) = logNorm (φ σ) r y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet | exact GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.exists_regularization_setting : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ), LogHom D Hd.aMu w → ChartPsh D w → ChartCont D w → ChartBdd D w → ConjOff D w → ∃ S' : BoundedRegularisationSetting M D.Xo Hd.aMu w, S'.IsTied ∧ ConjU S' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_regularization_setting | exact GlobalTheory.CompanionTheory.Relay.exists_regularization_setting | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_regularization_setting <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.exists_regularization_of_hodge_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D), ChartPsh D (phMu Hd) → ∃ S : LogLogRegularisationSetting M D.Xo (muLine Hd), S.IsTied := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_regularization_of_hodge_metric | exact GlobalTheory.CompanionTheory.Relay.exists_regularization_of_hodge_metric | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_regularization_of_hodge_metric <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.partial_flag_bundle_metric_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) → ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (B : FinHolAtlas e R.X), (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) → IsPotential R.A (BM.L.pullback pr hp.1) → IsSection R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m (fun k => pr ⁻¹' BM.W k) → IsAdaptedAtlas R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → ∃ (ph : R.X → ℝ) (C₅ : ℝ), (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x → Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) ∧ (∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → ph x = ph x') ∧ IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ιk fun k => M.dy p (κ k))) ph C₅ ∧ IsGradBound B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) ph C₅ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists | exact GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.stepWeight_exists <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem eval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {w : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal w) : eval w (map (Int.castRingHom ℂ) f) = 0 := by
  have h : (mConeMap w : MRing ι →+* MvPolynomial K ℂ) f = 0 := RingHom.mem_ker.mp hf
  have key : ((MvPolynomial.eval (fun _ : K => (1 : ℂ))).comp (mConeMap w : MRing ι →+* MvPolynomial K ℂ) : MRing ι →+* ℂ)
      = (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMap]
    · intro p
      simp [mConeMap]
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at this
  rw [← this, h, map_zero]

theorem bvec_good : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt (BM.F l) (mCoordIdeal (FC.bvec BM l b)) ∧ (∀ k, FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1) ∧ SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift b b)) := BM.good l b hb
  have hne : ∀ k, BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k =>
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.chart_ne (hgood.1 k)
  have hbv : ∀ q, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b q
      = (BM.Rb.lift b b ⟨q.1, (BM.F l).c q.1⟩)⁻¹ * BM.Rb.lift b b q := fun q => by
    simp only [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec, div_eq_inv_mul]
  have horb : SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) (BM.Rb.lift b b) := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit
    exact ⟨fun k => (BM.Rb.lift b b ⟨k, (BM.F l).c k⟩)⁻¹, fun k => inv_ne_zero (hne k), funext hbv⟩
  have hideal : mCoordIdeal (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) = mCoordIdeal (BM.Rb.lift b b) :=
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit horb
  have hone : ∀ k, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbv]; exact inv_mul_cancel₀ (hne k)
  have hmem : BM.Rb.lift b b ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem b b (BM.Rb.mem_U b)
  have hpt : GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) := by
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ⟨(BM.F l).c k, by rw [hone k]; exact one_ne_zero⟩, fun f hf => ?_⟩
    apply eval_eq_zero_of_mem_mCoordIdeal
    rw [hideal]
    exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hmem hf
  refine ⟨hpt, ?_, hone, horb⟩
  rw [hideal]
  exact hgood

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem fibre_member_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ (p : Ψ × Fin N) (z : Fin (d + 1) → ℂ), Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p z hz
  have hV : IsOpen {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un} := by
    have hc : Continuous (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) :=
      continuous_pi fun i => continuous_apply _
    exact hUn.preimage hc
  obtain ⟨zex, hzan, hzex⟩ := GlobalTheory.T.two_point_fibre_chart_first K ι Φ y Ψ N j M n d BM FA τ a ca cb X q Un Gn ΦYn ΦWn l H bp hUn hF
  have hbij := GlobalTheory.T.realisation_bijective_degree_one K ι (d + 1) (Option (Ψ × Fin N)) FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty
  obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.local_holomorphic_lift_realisation K ι (d + 1) (Option (Ψ × Fin N)) FA.S (mCoordIdeal y) FA.Re (some p) (d + 1)
    {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un} ΦYn zex z FA.J_top FA.deg_one FA.br_empty hV hz hzan
    (fun u hu => (hzex u hu).1) (fun u hu x₀ hx => ((hzex u hu).2 x₀ hx).1)
  refine ⟨Hh, hHh, ?_⟩
  filter_upwards [hev, hV.mem_nhds hz] with z' h1 hz'
  obtain ⟨x₀, hx₀⟩ := hbij.2 (ΦYn z')
  obtain ⟨h2, h3, h4⟩ := (hzex z' hz').2 x₀ hx₀
  obtain ⟨hbO, hH⟩ := hF.2.2.2.1 _ hz'
  obtain ⟨hsb, hsd, -, -⟩ := GlobalTheory.T.elementary_factor_properties N j a b ca cb (z' 0) M.j_le hb hab hca hcb
  have hflag : IsBlockDiag j (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) ∧
      (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1).det ≠ 0 := by
    unfold flagAt
    split_ifs with hp
    · subst hp
      refine ⟨(hH p.1).1.mul hsb, ?_⟩
      rw [Matrix.det_mul, hsd, mul_one]
      exact (hH p.1).2
    · exact hH p.1
  have hline := GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ (zex z') (bp (Fin.tail z')) p
    (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) hbO h2 h3 (h4 p.1 p.2) hflag.1 hflag.2
  have hphi : ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') =
      (FA.S.th (some p)).φ (ΦYn z) (ΦYn z') + FA.S.ph (some p) (ΦYn z') := rfl
  rw [hphi, h1, FA.ref_some, ← hline, hx₀]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.two_point_fibre_twisted_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (k₀ : K), M.blk (τ, a) = some k₀ → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ f : RW.X → ℝ, IsNormFn M τ a k₀ ca cb RW f → ∀ (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → RW.X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → z 0 ≠ z 1 → f (ΦWn z) + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) = logSin (Gn (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.flag_adjacent_chart_sixth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∃ O' : Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen O' ∧ wO M Rb τ a k₀ ca cb F kb V r h = O' ∩ mcPts (wP M τ a k₀ ca cb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.main <;> assumption)
end
