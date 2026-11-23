module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle092
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle100
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle101
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartBergmanBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralOfBergman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DoubleSumEqZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GraphEquiv
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.UpdateEraseSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem BranchChartInt.proof : GroundTheory.Heights₂.Heights.BranchChartInt.Statement :=
  GroundTheory.Heights₂.Heights.BranchChartInt.proof
    (GroundTheory.Heights₂.Heights.HolomorphicFibreSumInt.proof GroundTheory.Heights₂.Heights.WeightedAreaFormula.proof)
    (GroundTheory.Heights₂.Heights.BranchSheetAE.proof
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof
      GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof
      (GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof
          GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof)))
    GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof

end GroundTheory.Heights₂.Heights.Swarm
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

lemma bergman_lerp_self {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (t : ℝ) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) :
    bergman (W.lerp W t) dV V n x = bergman W dV V n x := by
  simp only [bergman, sectionL2NormSq, ptNormSq, lerp_self_φ]

lemma bergman_nonneg {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) : 0 ≤ bergman W dV V n x :=
  Real.iSup_nonneg fun _ => div_nonneg (ptNormSq_nonneg W n _ x) (sectionL2NormSq_nonneg W dV n _)

theorem BergmanL1Convergence.proof (hL1 : L1Convergence.Statement)
    (hLoc : LocalBergmanBound.Statement) (hUnif : UniformBergmanBound.Statement)
    (hInt : IntegralOfBergman.Statement) (hBI : BergmanIntegrable.Statement)
    (hDI : BergmanDensIntegrable.Statement) : BergmanL1Convergence.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV hdim
  have := dV.isProb
  obtain ⟨C, hC⟩ := hUnif A L W W dV hW hW
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ D := fun n => by positivity
  set g : ℕ → X → ℝ := fun n x =>
    (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x with hg
  have hbound : ∀ n x, 0 ≤ g n x ∧ g n x ≤ C := fun n x => by
    refine ⟨mul_nonneg (inv_nonneg.2 (hpos n).le) (bergman_nonneg _ _ _ _ _), ?_⟩
    have h := hC (n + 1) (by omega) 0 ⟨le_rfl, zero_le_one⟩ (V (n + 1)) (hV _) x
    rw [bergman_lerp_self] at h
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ C
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm C (((n + 1 : ℕ) : ℝ) ^ D)]
  have hlim : ∀ (x : X) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ bergmanDens W dV x + ε := by
    intro x ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hLoc A L W dV hW V hV x ε hε)
    filter_upwards [h] with n hn
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ _
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm (bergmanDens W dV x + ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hmass : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∫ x, bergmanDens W dV x ∂dV.μ - ε ≤ ∫ x, g n x ∂dV.μ := by
    intro ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hdim ε hε)
    filter_upwards [h] with n hn
    have hI : ∫ x, g n x ∂dV.μ =
        (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * Module.finrank ℂ (V (n + 1)) := by
      rw [hg, integral_const_mul, hInt A L W dV (n + 1) (V (n + 1)) (hV _)]
    rw [hI, le_inv_mul_iff₀ (hpos n)]
    linarith [mul_comm (∫ x, bergmanDens W dV x ∂dV.μ - ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hgi : ∀ n, Integrable (g n) dV.μ := fun n =>
    (hBI A L W dV (n + 1) (V (n + 1)) (hV _)).const_mul _
  have h := hL1 dV.μ g (bergmanDens W dV) C hgi (hDI A L W dV) hbound hlim hmass
  exact (tendsto_add_atTop_iff_nat 1).1 h

theorem BergmanL1Convergence.full : BergmanL1Convergence.Statement :=
  BergmanL1Convergence.proof L1Convergence.proof
    (LocalBergmanBound.proof (ChartBergmanBound.proof PolydiscSubmean.proof ComplexTaylorTwo.proof))
    (UniformBergmanBound.proof PolydiscSubmean.proof ChartTaylorCover.proof)
    IntegralOfBergman.proof BergmanIntegrable.proof BergmanDensIntegrable.proof

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormPullback

theorem proof_dehom (hG : PullFormsGeneric.Statement) (hC : FibreNormDehomCharpoly.Statement)
    (hI : FibreNormDehomIntegral.Statement) (hR : FibreNormDehomRoots.Statement) :
    FibreNormPullback.Statement := by
  intro K _ ι _ Ω _ y D e L q hV hBir he hL hL0
  classical
  have : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨j, hj⟩ : ∃ j, aeval y (L j) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 := hG K ι Ω y D e L hV hBir he hL hL0 1 (X 0) (isHomogeneous_X ℚ 0) (by rw [aeval_X]; exact h 0)
    exact X_ne_zero _ h0
  obtain ⟨hfin, hC'⟩ := hC K ι Ω y D e L q hV hBir he hL hL0
  obtain ⟨M₀, hM₀, hI'⟩ := hI K ι Ω y D e L q hV hBir he hL hL0
  have hR' := hR K ι Ω y D e L q hV hBir he hL hL0
  have hP : IsMultiHomogIdeal (mCoordIdeal y) := hV.2.1.2.1
  set n := Module.finrank (pullField y L) Ω
  have hn1 : 1 ≤ n := Module.finrank_pos
  refine ⟨n, M₀, hn1, by exact_mod_cast hM₀, fun τ s hs hs0 => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hC' τ s hs j hj
  obtain ⟨F, hF⟩ := hI' τ s hs j c hc
  have hRc := hR' τ s hs j c hc
  obtain ⟨-, _, hc0, hch, -⟩ := hc
  have hM₀q : ((M₀ : ℚ) ^ τ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show M₀ ≠ 0 by omega))
  refine ⟨F, ?_, ?_, fun ζ hζ S hS M hM hrep => ?_⟩
  · rintro rfl
    rw [map_zero, eq_comm, smul_eq_zero] at hF
    exact hF.elim hM₀q (hcn hs0)
  · apply isHomogeneous_of_map
    rw [hF, smul_eq_C_mul, show n * q * τ = 0 + n * (q * τ) by ring]
    exact (isHomogeneous_C _ _).mul (hch n le_rfl)

  have hmapF : eval ζ (map (Int.castRingHom ℂ) F) = (M₀ : ℂ) ^ τ * eval ζ (map (algebraMap ℚ ℂ) (c n)) := by
    have h1 : map (Int.castRingHom ℂ) F = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) F) := by
      rw [map_map]
      congr 1
    rw [h1, hF, smul_eq_C_mul, map_mul, map_C, eval_mul, eval_C]
    simp
  set B := M * ‖ζ‖ ^ (q * τ) with hBdef
  have hB0 : 0 ≤ B := mul_nonneg hM (pow_nonneg (norm_nonneg _) _)
  have hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (n - i) = 0 →
      ‖w‖ ≤ B := by
    intro w hw
    obtain ⟨z, hz, t, ht0, hLz, hval⟩ := hRc ζ hζ w hw
    obtain ⟨z', hz'S, r, hr0, rfl⟩ := hS z hz ⟨t, hLz⟩
    have hz'm : z' ∈ mcPts (mCoordIdeal y) := by
      have h1 := mcPts_smul hP (fun k => (r k)⁻¹) (fun k => inv_ne_zero (hr0 k)) hz
      convert h1 using 1
      funext p
      simp [hr0 p.1]
    obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz'0, hle⟩ := hrep z' hz'S hz'm
    have hgz := eval_smul_homog g dg hg r z'
    have hhz := eval_smul_homog h dh hh r z'
    have hhz0 : eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h) ≠ 0 := by
      rw [hhz]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hr0 k)) hz'0
    have hv := hval dg dh g h hg hh hd hgh hhz0
    have hRg : (∏ k, r k ^ dg k) = (∏ k, r k ^ dh k) * (∏ k, r k ^ e k) ^ (q * τ) := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hd k, ← pow_mul, ← pow_add]
      ring
    have hnormL : ‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ = ‖t‖ * ‖ζ‖ := by
      have h1 : (∏ k, r k ^ e k) • (fun j => eval z' (map (Int.castRingHom ℂ) (L j))) = t • ζ := by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← eval_smul_homog (L j) e (hL j) r z', hLz j]
      rw [← norm_smul, h1, norm_smul]
    have hpos : 0 < ‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖ :=
      mul_pos (pow_pos (norm_pos_iff.mpr ht0) _) (norm_pos_iff.mpr hhz0)
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖w‖ * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖)
        = ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) g)‖ := by
          rw [hv, norm_mul, norm_mul, norm_pow]; ring
      _ = ‖∏ k, r k ^ dg k‖ * ‖eval z' (map (Int.castRingHom ℂ) g)‖ := by rw [hgz, norm_mul]
      _ ≤ ‖∏ k, r k ^ dg k‖ * (M * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) *
            ‖eval z' (map (Int.castRingHom ℂ) h)‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = M * (‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖) ^ (q * τ) *
            (‖∏ k, r k ^ dh k‖ * ‖eval z' (map (Int.castRingHom ℂ) h)‖) := by
          rw [hRg, norm_mul, norm_pow]; ring
      _ = B * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖) := by
          rw [hnormL, hhz, norm_mul, hBdef]; ring
  have key := norm_last_le (fun i => eval ζ (map (algebraMap ℚ ℂ) (c i))) (by simp [hc0]) hB0 hroot
  rw [hmapF, norm_mul, norm_pow, Complex.norm_natCast]
  calc (M₀ : ℝ) ^ τ * ‖eval ζ (map (algebraMap ℚ ℂ) (c n))‖ ≤ (M₀ : ℝ) ^ τ * B ^ n :=
        mul_le_mul_of_nonneg_left key (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (M₀ : ℝ) ^ τ * ‖ζ‖ ^ (n * q * τ) * M ^ n := by
        rw [hBdef, mul_pow, ← pow_mul, show q * τ * n = n * q * τ by ring]
        ring

end FibreNormPullback

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefBigCountAlongMultiples.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsNefBigDatum P0 y D A →
    ∀ ε : ℝ, 0 < ε → ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) - ε) *
          (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem VeryAmpleZRows.proof_closed : VeryAmpleZRows.Statement.{u, v, w} :=
  VeryAmpleZRows.proof CechPartition.proof ZChartSmul.proof (ZChartLocal.proof ZChartSmul.proof)

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w v'

theorem SnapperQuotIso.proof : SnapperQuotIso.Statement.{u, v, w, v'} := by
  intro k _ Ω _ _ N x E _ _ _ _ E' _ _ _ _ F₁ F₂ G₁ G₂ e
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact (Cech.equivH e.equiv e.comm i).finrank_eq

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem DoubleCech.proof : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DoubleCech.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DoubleCech.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq.proof

end GroundTheory.Heights₂.Heights.Swarm
end
