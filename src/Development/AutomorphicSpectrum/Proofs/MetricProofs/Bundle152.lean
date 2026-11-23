module

import Development.WeilBound.CoreStatements.MultihomogeneousSquares.EmbImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.EvalFam
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.LeMCoordIdealOfTorus
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSet
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareSystemPolarVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle142
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle120
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle124
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TiedRegularizationAsymptotic
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle151
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev cj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun q => starRingEnd ℂ (z q)

theorem cj_cj (z : (Σ k, ι k) → ℂ) : cj (cj z) = z := by
  funext q; simp [cj]

theorem cj_nonzero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, cj z ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, by simpa [cj] using hi⟩

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit (cj z) (cj z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => starRingEnd ℂ (c k), fun k => by simpa using hc k, ?_⟩
  funext p
  simp [cj]

theorem cj_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : cj z ∈ mcPts P := by
  refine ⟨cj_nonzero hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  have key : eval (cj z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by

    rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq,
    map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [map_mul, map_prod, map_pow]
  rw [key, h, map_zero]

theorem log_sub_orbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  have hP : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  rw [A.smul c z' hc, B.smul c z' hc, ← hab,
    Real.log_mul hP.ne' (A.pos z' hz).ne', Real.log_mul hP.ne' (B.pos z' hz).ne']
  ring

def conjAvg (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := Real.sqrt |A.h z * A.h (cj z)|
  pos z hz := Real.sqrt_pos.2 (abs_pos.2 (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne')
  smul c z hc := by
    have hP : 0 ≤ ∏ k, ‖c k‖ ^ A.a k :=
      Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    have e1 : cj (fun p : Σ k, ι k => c p.1 * z p) =
        fun p => (starRingEnd ℂ (c p.1)) * cj z p := by
      funext p; simp [cj]
    have hc' : ∀ k, starRingEnd ℂ (c k) ≠ 0 := fun k => by simpa using hc k
    rw [e1, A.smul c z hc, A.smul _ (cj z) hc']
    simp only [RCLike.norm_conj]
    rw [show (∏ k, ‖c k‖ ^ A.a k) * A.h z * ((∏ k, ‖c k‖ ^ A.a k) * A.h (cj z)) =
      (∏ k, ‖c k‖ ^ A.a k) ^ 2 * (A.h z * A.h (cj z)) by ring, abs_mul, abs_of_nonneg (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hP]

theorem conjAvg_conj (A : HermLine ι) : IsConjInvariantH (conjAvg A) := fun z => by
  change Real.sqrt |A.h (cj z) * A.h (cj (cj z))| = Real.sqrt |A.h z * A.h (cj z)|
  rw [cj_cj, mul_comm]

theorem conjAvg_log (A : HermLine ι) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((conjAvg A).h z) = (Real.log (A.h z) + Real.log (A.h (cj z))) / 2 := by
  have h1 := A.pos z hz
  have h2 := A.pos _ (cj_nonzero hz)
  change Real.log (Real.sqrt |A.h z * A.h (cj z)|) = _
  rw [abs_of_pos (mul_pos h1 h2), Real.log_sqrt (mul_pos h1 h2).le, Real.log_mul h1.ne' h2.ne']

theorem conjAvg_smooth {A : HermLine ι} (hA : IsSmoothHerm A) : IsSmoothHerm (conjAvg A) := by
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hS
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) := by
    refine contDiff_pi.2 fun q => ?_
    exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) q)
  have hmap : Set.MapsTo (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) S S := fun z hz => cj_nonzero hz
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h (cj z)) S :=
    hA.comp hconj.contDiffOn hmap
  have hprod := hA.mul h2
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.sqrt (A.h z * A.h (cj z))) S :=
    hprod.sqrt fun z hz => (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne'
  refine hs.congr fun z hz => ?_
  change Real.sqrt |A.h z * A.h (cj z)| = _
  rw [abs_of_pos (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz)))]

theorem holoOn_comp {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {g : X → Y} (hg : HoloMap A B g) {V : Set Y}
    {G : Y → ℂ} (hG : B.HoloOn V G) : A.HoloOn (g ⁻¹' V) (G ∘ g) := by
  apply SquareStatements.emb_holoOn <;> assumption

def IsLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lift : X → X → (Σ k, ι k) → ℂ) : Prop :=
  (∀ x, IsOpen (U x)) ∧ (∀ x, x ∈ U x) ∧ (∀ x p, A.HoloOn (U x) fun y => lift x y p) ∧
  (∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P) ∧
  (∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)) ∧
  (∀ z ∈ mcPts P, ∃ x, SameOrbit (lift x x) z) ∧
  (∀ x x', SameOrbit (lift x x) (lift x' x') → x = x') ∧
  ∀ x, ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal x) ∩ mcPts bd) : Set (mcPts (mCoordIdeal x))) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → ∃ (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Rb.X), IsPotential Rb.A L ∧ IsSection Rb.A L s ∧ IsSNC Rb.A L s m W ∧ (∀ p, logNormSec L s p ≤ 0) ∧ (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) ∧ ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → rW L s p' = rW L s p := by
  intro K _ J _ Ω _ _ x n bd hsnc harith _ htor hconj
  obtain ⟨I, hIh, hIle, hIsnc, hIeq⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_homogIdeal x n bd hsnc harith htor
  obtain ⟨Rb, nb, W, hloc⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_res x n I harith hIh hIle hIsnc
  rw [hIeq] at hloc
  obtain ⟨L, s, h1, h2, h3, h4, h5, h6⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.assemble Rb (mcPts (mCoordIdeal x) ∩ mcPts bd)
      (fun z hz c hc => htor z hz c hc) (fun z hz => hconj z hz) nb W hloc
  refine ⟨Rb, L, s, nb, fun _ => 1, W, h1, h2, h3, h4, fun p => ?_, h6⟩
  rw [h5 p]
  exact ⟨fun hp => hp.2, fun hp => ⟨Rb.mem p p (Rb.mem_U p), hp⟩⟩
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.cusp_weight_integrable_on_fundamental_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)), F.IsArith Γ → F.IsFundSet Γ FF → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → IntegrableOn (ballDens F.q) FF ∧ 0 < ∫ t in FF, ballDens F.q t ∧ IntegrableOn (fun t => (F.R t).cuspW F.σ * ballDens F.q t) FF ∧ ∫ t in FF, (F.R t).cuspW F.σ * ballDens F.q t ≤ Fintype.card Ψ * j' * (6 + Real.log (2 * Fintype.card Ψ * hostRd E) + Real.log (2 * Fintype.card Ψ * j' * hostRd E)) * ∫ t in FF, ballDens F.q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW | exact GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem _root_.GlobalTheory.T.hodgeCpt_descent_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (A : HodgeCpt Y S x) (F₀ : Type) [Field F₀] (ξ₀ : Spec (CommRingCat.of F₀) ⟶ Y.X) (ι : F₀ →+* Ω), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f ι → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module F₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j₁ : Li₀ →+ A.Li) (V₀ : CMType H ⊕ CMType H → Submodule F₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (A.M.pt (j₁ e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left) ∧ IsExtOver ι j₁ ∧ (∀ s e, e ∈ V₀ s ↔ j₁ e ∈ A.Vgen s) ∧ ∀ s, LinearIndependent F₀ (b s) ∧ Submodule.span F₀ (Set.range (b s)) = V₀ s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.lie_generic_eigenspaces | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.lie_generic_eigenspaces | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.lie_generic_eigenspaces <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.exists_potential_charts_with_radii : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (ref : HermLine J) (r : Fin D.nCharts → (Fin D.n → ℂ) → ℝ), IsSmoothHerm ref → IsConjInvariantH ref → (∀ a t, 0 < r a t) → ∃ (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)) (κ : Equiv.Perm (Fin P.N)), ThRef M ref P.th ∧ Adapted M P S ∧ FromSnc M P ∧ SymmCharts M P κ ∧ ∀ j, ∃ (a : Fin D.nCharts) (t₀ : Fin D.n → ℂ) (ε : ℝ), ‖t₀‖ ≤ 1 / 2 ∧ 0 < ε ∧ 2 * ε ≤ r a t₀ ∧ ε ≤ 1 / 4 ∧ ((∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj ((D.chart a).γ (t₀ + (ε : ℂ) • t)) ∧ P.q j t = Real.log (ref.h ((D.chart a).γ (t₀ + (ε : ℂ) • t)))) ∨ ∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t))) ∧ P.q j t = Real.log (ref.h ((D.chart a).γ (t₀ + (ε : ℂ) • star t)))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_potential_charts_with_radii | exact GlobalTheory.CompanionTheory.Relay.exists_potential_charts_with_radii | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_potential_charts_with_radii <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.square_system_polar_vanishing : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (n : σ → ℤ), n a₀ = 0 → ∀ t, 0 < t → t ≤ Q.an.SW.t₀ → polar (d + 2) (Re.num II t) (fun _ a => (n a : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → polar (d + 2) (Re.num II t) (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) = -∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t)) (Q.an.wcoef (fun a => (n a : ℝ)) k i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale | exact GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.first_half_at_scale <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_same_base_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (x₀ : BM.Rb.X) (z z' : (Σ k, ι k) → ℂ), x₀ ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z' ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → basePart M.blk z = basePart M.blk z' → (∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = z' ⟨k, m⟩) → stepGap M BM p z = stepGap M BM p z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem holoOn_mul_prod_zpow {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X} {κ : Type}
    [Fintype κ] {f : X → ℂ} {c : κ → X → ℂ} (d : κ → ℤ) (hf : A.HoloOn U f) (hc : ∀ k, A.HoloOn U (c k))
    (h0 : ∀ k, ∀ y ∈ U, c k y ≠ 0) : A.HoloOn U fun y => f y * ∏ k, c k y ^ d k := by
  intro j z hz
  have h1 : AnalyticAt ℂ (fun v => ∏ k, ((c k ∘ (A.chart j).symm) v) ^ d k) z :=
    Finset.analyticAt_fun_prod _ fun k _ => (hc k j z hz).zpow (h0 k _ hz.2)
  exact (hf j z hz).mul h1

theorem holoOn_comp_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {g : (Fin e → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g ψ.target) {V : Set X} (hV : V ⊆ ψ.source) : A.HoloOn V fun w => g (ψ w) := by
  intro j z hz
  have hs : (A.chart j).symm z ∈ ψ.source := hV hz.2
  have h1 : AnalyticAt ℂ (g ∘ (ψ ∘ (A.chart j).symm)) z :=
    AnalyticAt.comp (g := g) (f := ψ ∘ (A.chart j).symm) (hg _ (ψ.map_source hs)) ((hψ j).1 z ⟨hz.1, hs⟩)
  exact h1

def mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p =>
  match p with
  | ⟨some k, m⟩ => z₀ ⟨k, m⟩
  | ⟨none, m⟩ => z₁ ⟨k₀, m⟩

theorem fstPt_mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : fstPt k₀ (mixPt k₀ z₀ z₁) = z₀ := by
  funext q
  obtain ⟨k, m⟩ := q
  rfl

theorem sndPt_mixPt {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h : ∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ q = z₀ q) :
    sndPt k₀ (mixPt k₀ z₀ z₁) = z₁ := by
  funext q
  obtain ⟨k, m⟩ := q
  by_cases e : k = k₀
  · subst e
    change mixPt k z₀ z₁ (v₁ k ⟨k, m⟩) = _
    rw [v₁_self]
    rfl
  · change mixPt k₀ z₀ z₁ (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    exact (h ⟨k, m⟩ e).symm

theorem mixPt_blocks {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h₀ : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0)
    (h₁ : ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) : ∀ o, ∃ i, mixPt k₀ z₀ z₁ ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact h₁ k₀
  | some k => exact h₀ k

theorem log_norm_sub {k₀ : K} (A : HermLine fun o : Option K => ι (o.getD k₀)) {c : Option K → ℂ}
    (hc : ∀ o, c o ≠ 0) {z zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z = fun p => c p.1 * zz p)
    (hzz : ∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) {f t : ℂ} (hf : f ≠ 0) (ht : t ≠ 0) :
    Real.log ‖f * (∏ o, c o ^ A.a o) * t‖ - Real.log (A.h z) = Real.log ‖t * f‖ - Real.log (A.h zz) := by
  have hC : (∏ o, ‖c o‖ ^ A.a o) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc o))
  have hP : ‖∏ o, c o ^ A.a o‖ = ∏ o, ‖c o‖ ^ A.a o := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun o _ => norm_zpow _ _
  have hN : ‖f * (∏ o, c o ^ A.a o) * t‖ = (∏ o, ‖c o‖ ^ A.a o) * ‖t * f‖ := by
    rw [norm_mul, norm_mul, norm_mul, hP]
    ring
  have hA : A.h z = (∏ o, ‖c o‖ ^ A.a o) * A.h zz := by
    rw [hz]
    exact A.smul c zz hc
  have hp : A.h zz ≠ 0 := (A.pos zz hzz).ne'
  have hn : ‖t * f‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero ht hf)
  rw [hN, hA, Real.log_mul hC hn, Real.log_mul hC hp]
  ring

theorem goodAt_of_orbit {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
    {F : FrameData ι Ψ N M.Ω M.blk} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z'))) : M.GoodAt F (mCoordIdeal (basePart M.blk z)) := by
  obtain ⟨c, hc0, hzc⟩ := h
  have e₀ : basePart M.blk z = fun q : Σ k, baseIdx ι M.blk k =>
      (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk z' q := by
    rw [hzc]; rfl
  rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
    (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk z')]
  exact hG

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ x, ∃ ψ kb σ i₀ V u, IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x
  obtain ⟨ψ, kb, σ, i₀, F, H, hx, hC⟩ := hW.2.2 x
  obtain ⟨V, z₀, z₁, c, hVo, hxV, hVs, hVU, hz₀h, hch, hc0, hL⟩ :=
    GlobalTheory.T.flag_adjacent_twisted_resolution_alt K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x ψ kb σ i₀ F H hx hC
  have hFr : M.IsFrame F := hC.2.1
  have hsrc := hC.2.2.2.2.2
  have hfacts : ∀ w ∈ V, basePart M.blk (z₀ w) ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, ∃ i, z₀ w ⟨k, i⟩ ≠ 0) ∧
      (∀ k, ∃ i, z₁ w ⟨k, i⟩ ≠ 0) ∧ basePart M.blk (z₁ w) = basePart M.blk (z₀ w) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (z₀ w))) := by
    intro w hw
    obtain ⟨ho₀, ho₁, -, hoff, -, -⟩ := hL w hw
    obtain ⟨h1, -, h3, h4⟩ := PtBase.main K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW w (z₀ w) (z₁ w) ho₀ ho₁
    refine ⟨h1, h3, h4, ?_, goodAt_of_orbit M ho₀ (hsrc w (hVs hw)).2.1⟩
    funext q
    exact hoff ⟨q.1.1, q.2⟩ fun e' => q.1.2 (τ, a) (hk.trans (congrArg some (Eq.symm e')))
  have hdata : ∀ w ∈ V, ψ w i₀ ≠ 0 → IsPtData M τ a k₀ ca cb RW w (z₀ w) (z₁ w) F (H τ (ψ w)) (ψ w i₀) := by
    intro w hw h0
    obtain ⟨ho₀, ho₁, hex, -⟩ := hL w hw
    have hH := (hsrc w (hVs hw)).1 τ
    exact ⟨hFr, (hfacts w hw).2.2.2.2, ho₀, ho₁, hH.1, hH.2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  obtain ⟨V', hV'o, hxV', hV'V, hfh, hf0⟩ := GlobalTheory.T.holomorphic_frame_metric_near_point K ι Φ y Ψ N j M e RW.X RW.A V x
    (fun w => basePart M.blk (z₀ w)) (fun w => H τ (ψ w)) F τ a hVo hxV (fun q => hz₀h ⟨q.1.1, q.2⟩)
    (fun w hw => (hfacts w hw).1) (fun w hw => (hfacts w hw).2.2.2.2)
    (fun r s => holoOn_comp_chart RW.A hC.1 (hC.2.2.2.2.1 τ r s) hVs) (fun w hw => (hsrc w (hVs hw)).1 τ)
  obtain ⟨f, hfh, hf0, hfd⟩ : ∃ f : RW.X → ℂ, RW.A.HoloOn V' f ∧ (∀ w ∈ V', f w ≠ 0) ∧ ∀ w, f w =
      ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk (z₀ w)) *
        (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (H τ (ψ w)) (wIdx N j) (wIdx N j) else 1)
          else minorIJ (H τ (ψ w)) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i) :=
    ⟨_, hfh, hf0, fun _ => rfl⟩
  refine ⟨ψ, kb, σ, i₀, V', fun w => f w * ∏ o, c o w ^ aDeg M τ a k₀ o, ⟨F, H, hC⟩, hV'o, hxV',
    hV'V.trans hVs, hV'V.trans hVU, ?_, ?_, ?_, ?_⟩
  · exact holoOn_mul_prod_zpow RW.A _ hfh (fun o j' => (hch o j').mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono hV'V))) fun o w hw => hc0 o w (hV'V hw)
  · intro w hw
    exact mul_ne_zero (hf0 w hw) (Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (hc0 o w (hV'V hw)))
  · intro w hw
    have hwV := hV'V hw
    constructor
    · intro h0
      obtain ⟨ho₀, ho₁, hex, hoff, -, -⟩ := hL w hwV
      have hbase := (hfacts w hwV).2.2.2.1
      have hz : z₁ w = z₀ w := by
        funext q
        obtain ⟨k, m⟩ := q
        by_cases e' : k = k₀
        · subst e'
          have h1 := (hex τ a).1.2 k hk m
          have h2 := (hex τ a).2.2 k hk m
          rw [if_pos rfl, h0, Matrix.single_zero, add_zero, mul_one, hbase] at h2
          exact h2.trans h1.symm
        · exact hoff ⟨k, m⟩ e'
      rw [hz] at ho₁
      exact orbit_trans (orbit_symm ho₀) ho₁
    · intro hs
      by_contra h0
      exact GlobalTheory.T.flag_adjacent_twisted_resolution K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW w _ _ _ _ _
        (hdata w hwV h0) hs
  · intro w hw h0 z₀' z₁' F' h' t' hD
    have hwV := hV'V hw
    obtain ⟨ho₀, ho₁, -, hoff, hl0, hl1⟩ := hL w hwV
    obtain ⟨hmc, hn₀, hn₁, hbase, hG⟩ := hfacts w hwV
    obtain ⟨hF', hG', hp₀, hp₁, hB', hd', ht', he₀', he₁'⟩ := hD
    have hd := hdata w hwV h0
    have hind := GlobalTheory.T.flag_adjacent_two_frames_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hj hk hca hcb F F' (z₀ w) (z₁ w) z₀' z₁'
      (H τ (ψ w)) h' (ψ w i₀) t' hmc hn₀ hn₁ hbase hFr hF' hG hG' (orbit_trans ho₀ (orbit_symm hp₀))
      (orbit_trans ho₁ (orbit_symm hp₁)) hd.2.2.2.2.1 hd.2.2.2.2.2.1 hB' hd' h0 ht' hd.2.2.2.2.2.2.2.1
      hd.2.2.2.2.2.2.2.2 he₀' he₁'
    rw [← hind]
    have hlift : RW.lift x w = fun p => c p.1 w * mixPt k₀ (z₀ w) (z₁ w) p := by
      funext p
      obtain ⟨o, m⟩ := p
      cases o with
      | none => exact hl1 m
      | some k => exact hl0 ⟨k, m⟩
    have hzz := mixPt_blocks (k₀ := k₀) hn₀ hn₁
    have hnorm := log_norm_sub (potA M τ a k₀) (c := fun o => c o w) (fun o => hc0 o w hwV) hlift hzz
      (hf0 w hw) h0
    have hcombo := GlobalTheory.T.twisted_metric_log_formula K ι Φ y Ψ N j M τ a k₀ hk _ hzz
    rw [fstPt_mixPt, sndPt_mixPt hoff] at hcombo
    have e₁ : Real.log ‖(f w * ∏ o, c o w ^ aDeg M τ a k₀ o) * ψ w i₀‖ -
        Real.log ((potA M τ a k₀).h (RW.lift x w)) = _ := hnorm
    refine e₁.trans ?_
    rw [hcombo, normRhs, ← hfd w]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.regularized_levi_lower_bound_eventually : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ δ > (0 : ℝ), ∀ᶠ t' in 𝓝[>] (0 : ℝ), ∀ a, ∀ t : Fin D.n → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, -(δ * ‖v‖ ^ 2) ≤ levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v := by
  first | exact @LevelTowerAlt.tied_regularization_asymptotic | exact LevelTowerAlt.tied_regularization_asymptotic
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.local_section_of_potential_on_model : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (Φ : LocPot M.Xc), IsPotential M.atlas Φ → (∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re) → IsPosPot M.atlas Φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section | exact GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.projection_of_chart_analytic : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (a : Fin D.nCharts) (k : Fin M.atlas.n), ∀ t ∈ Metric.ball (0 : Fin D.n → ℂ) 1, M.proj ((D.chart a).γ t) ∈ (M.atlas.chart k).source → AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t ∧ Function.Bijective (fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic | exact GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic | (intros; apply GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic <;> assumption)
end
