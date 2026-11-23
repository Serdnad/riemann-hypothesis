module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre isOpen_blockNonzero)

def expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) : HermLine ι :=
  HermLine.ofWeight (fun z => -v z) fun c z hc => by rw [hv.2 c z hc]

theorem pot_cons_expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι) :
    pot (Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) = Fin.cons v (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [pot, expLine, HermLine.ofWeight]
  · simp [pot]

theorem isSmoothHerm_cons_expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) j) := by
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact Real.contDiff_exp.comp_contDiffOn hv.1.neg.neg
  · simpa using hL j

theorem SegreChart.proof (hDim : SegreChartDim.Statement) (hInt : SegreChartIntegral.Statement) :
    SegreChart.Statement := by
  classical
  intro K _ _ ι _ P n L u v i δ hP hL hu hv hδ hsupp
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let U := fun x => χ x * u (lam x)
  let V := fun x => v (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i

  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'

  have key : ∀ x ∈ segreChartSet P σ i, U =ᶠ[𝓝 x] u ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [U, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    · have hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)
      have hcont : Continuous fun y => segre (lam y) :=
        continuous_pi fun i' => continuous_finsetProd _ fun k _ =>
          (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous
      have hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖} :=
        isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)
      have hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖ := by
        rw [segre_chartLift σ i z hzi, hzi, norm_one]
        have h1 : 1 / δ < ‖segre z‖ := by linarith
        calc (1 : ℝ) = δ * (1 / δ) := by field_simp
          _ < δ * ‖segre z‖ := mul_lt_mul_of_pos_left h1 hδ
      filter_upwards [hO.mem_nhds hx] with y hy
      simp [U, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)
  refine ⟨Fintype.card ((k : K) → ι k), segreChartComponents P σ i, U, V, Φ,
    fun J hJs => ⟨(mem_segreChartComponents.1 hJs).1.1,
      hDim K ι P (n + 1) _ σ i hP J hJs,
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm u hu.1)⟩,
      ⟨Ω, hΩ, hJ J hJs, hsm v hv.1⟩, fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩⟩,
    χ.hasCompactSupport.mul_right, ?_, ?_⟩
  · rw [← pot_cons_expLine v hv L]
    refine hInt K ι P n _ σ i _ u δ U _ hP (isSmoothHerm_cons_expLine v hv L hL) hu hδ (Or.inl hsupp)
      fun x hx => ⟨key x hx, fun j => EventuallyEq.of_eq ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · funext y; simp [V, lam, pot, expLine, HermLine.ofWeight]
    · rfl
  · rw [← pot_cons_expLine u hu L]
    refine hInt K ι P n _ σ i _ v δ V _ hP (isSmoothHerm_cons_expLine u hu L hL) hv hδ
      (Or.inr fun z hz => by rw [pot_cons_expLine u hu L]; exact hsupp z hz)
      fun x hx => ⟨EventuallyEq.rfl, fun j => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · have h0 : pot (Fin.cons (expLine u hu) L : Fin (n + 1) → HermLine ι) 0 = u := by
        rw [pot_cons_expLine u hu L]; rfl
      simpa [h0] using key x hx
    · exact EventuallyEq.rfl

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre)

theorem StokesStatement.of_found (hBil : PtsBilinear.Statement) (hPart : SegrePartition.Statement)
    (hChart : SegreChart.Statement) (hSV : StokesOnVariety.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by
  classical
  intro K _ ι _ P n L B B' hP hL hB hB' hB0 hB'0
  have hw := isDegZeroSmooth_log hB hB0
  have hw' := isDegZeroSmooth_log hB' hB'0
  have hne : ∀ k, Nonempty (ι k) := fun k => by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    exact ⟨i⟩
  obtain ⟨δ, hδ, ρ, hρs, hρ1, hρ0⟩ := hPart K ι hne

  have hpiece : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρs i).mul hw

  have key : ∀ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
        (fun z => ρ i z * Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
        (fun z => Real.log (B'.h z)) := by
    intro i
    obtain ⟨m, Js, U, V, Φ, hJ, hU, h1, h2⟩ := hChart K ι P n L (fun z => ρ i z * Real.log (B.h z))
      (fun z => Real.log (B'.h z)) i δ hP hL (hpiece i) hw' hδ
      (fun z hz => by simp only [hρ0 i z hz, zero_mul])
    rw [h1, h2]
    refine Finset.sum_congr rfl fun J hJs => ?_
    obtain ⟨hJp, hJd, hUs, hVs, hΦs⟩ := hJ J hJs
    exact hSV m n J U V Φ hJp hJd hUs hVs hΦs (Or.inl hU)
  have hsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) := by
    funext z
    rw [← Finset.sum_mul, hρ1 z, one_mul]
  obtain ⟨hA, hC⟩ := hBil K ι P n L _ (fun i z => ρ i z * Real.log (B.h z))
    (fun z => Real.log (B'.h z)) hP hL hpiece hw'
  calc ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (fun z => Real.log (B.h z))
      = ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ∑ i, ρ i z * Real.log (B.h z)) := by rw [← hsum]
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ρ i z * Real.log (B.h z)) := hA
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := Finset.sum_congr rfl fun i _ => key i
    _ = ptsIntegral P (Fin.cons (fun z => ∑ i, ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := hC.symm
    _ = ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := by rw [← hsum]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem charZero_of_isArithVar_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    simp only [mConeMap, map_natCast]
    rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot).1 hmem

theorem AmpleCountAlongMultiples.proofAmple (hL : LiftModel.Statement) (hC : LiftCountAlongMultiples.Statement) :
    AmpleCountAlongMultiples.StatementAmple := by
  intro K _ _ ι _ _ Ω _ y D N P0 II hD hII har hb hP0 hs hcj hgen hc hfib ε hε
  have : CharZero Ω := charZero_of_isArithVar_mCoordIdeal har
  obtain ⟨a, ι', _, x', ha, hmem, hgo, hbir⟩ := hL K ι Ω y D N.a har hb hgen hc hfib
  refine ⟨a, ha, ?_⟩
  have hapos : (0 : ℝ) < (a : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast ha) _
  filter_upwards [hC K ι Ω y D N P0 II a ι' x' hD hII har hb hP0 hs hcj ha hmem hgo hbir
    (ε * (a : ℝ) ^ (D + 1)) (mul_pos hε hapos)] with k hk
  have key : (II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
        (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      ((a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε * (a : ℝ) ^ (D + 1)) *
        ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    push_cast
    ring
  rw [key]
  exact hk

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace ConeRingLaurent

theorem map_C_isPrime {D σ : Type*} [CommRing D] (𝔮 : Ideal D) [𝔮.IsPrime] :
    (𝔮.map (C : D →+* MvPolynomial σ D)).IsPrime := by
  rw [← Ideal.mk_ker (I := 𝔮), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

variable {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k)

def tProd : MvPolynomial K (DehomRing i) := ∏ k, X k

abbrev Laurent := Localization.Away (tProd i)

def laurentToConeRing : MvPolynomial K (DehomRing i) →+* ConeRing i :=
  eval₂Hom (ratioMap i) fun k => algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (X ⟨k, i k⟩)

theorem laurentToConeRing_tProd : laurentToConeRing i (tProd i) = algebraMap _ (ConeRing i) (coneUnit i) := by
  simp [laurentToConeRing, tProd, coneUnit, map_prod]

def toCone : Laurent i →+* ConeRing i :=
  IsLocalization.Away.lift (tProd i) (g := laurentToConeRing i) (by
    rw [laurentToConeRing_tProd]; exact IsLocalization.Away.algebraMap_isUnit (coneUnit i))

def coneToLaurentPolynomial : MvPolynomial (Σ k, ι k) ℂ →+* Laurent i :=
  eval₂Hom ((algebraMap (MvPolynomial K (DehomRing i)) (Laurent i)).comp (C.comp (algebraMap ℂ (DehomRing i))))
    fun p => algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (C (dehom i (X p)) * X p.1)

theorem coneToLaurent_X_self (k : K) :
    coneToLaurentPolynomial i (X ⟨k, i k⟩) = algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X k) := by
  simp [coneToLaurentPolynomial, dehom_X_self]

theorem coneToLaurent_coneUnit :
    coneToLaurentPolynomial i (coneUnit i) = algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (tProd i) := by
  rw [coneUnit, map_prod]
  exact (Finset.prod_congr rfl fun k _ => coneToLaurent_X_self i k).trans (map_prod _ _ _).symm

def fromCone : ConeRing i →+* Laurent i :=
  IsLocalization.Away.lift (coneUnit i) (g := coneToLaurentPolynomial i) (by
    rw [coneToLaurent_coneUnit]; exact IsLocalization.Away.algebraMap_isUnit (tProd i))

theorem ratioMap_algebraMap (c : ℂ) :
    ratioMap i (algebraMap ℂ (DehomRing i) c) = algebraMap (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i) (C c) := by
  rw [← AlgHom.commutes (dehom i) c, ratioMap_dehom, AlgHom.commutes,
    IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq]

theorem toCone_comp_fromCone : (toCone i).comp (fromCone i) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (coneUnit i))
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingHom.id_apply, fromCone, IsLocalization.Away.lift_eq, coneToLaurentPolynomial,
      eval₂Hom_C, toCone, laurentToConeRing]
    exact ratioMap_algebraMap i c
  · intro p
    simp only [RingHom.comp_apply, RingHom.id_apply, fromCone, IsLocalization.Away.lift_eq, coneToLaurentPolynomial,
      eval₂Hom_X', toCone, map_mul, laurentToConeRing, eval₂Hom_C]
    rw [ratioMap_dehom, coneRatio, aeval_X, mul_right_comm, (isUnit_coneX i p.1).val_inv_mul, one_mul]

theorem fromCone_algebraMap (f : MvPolynomial (Σ k, ι k) ℂ) :
    fromCone i (algebraMap _ (ConeRing i) f) = coneToLaurentPolynomial i f :=
  IsLocalization.Away.lift_eq _ _ _

theorem fromCone_comp_ratioMap :
    (fromCone i).comp (ratioMap i) =
      (algebraMap (MvPolynomial K (DehomRing i)) (Laurent i)).comp (C : DehomRing i →+* MvPolynomial K (DehomRing i)) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (C c) = dehom i (C c) from rfl, ratioMap_dehom, coneRatio, aeval_C,
      IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) (ConeRing i), MvPolynomial.algebraMap_eq,
      fromCone_algebraMap, coneToLaurentPolynomial, eval₂Hom_C]
    rfl
  · intro p
    simp only [RingHom.comp_apply]
    rw [show Ideal.Quotient.mk (dehomIdeal i) (X p) = dehom i (X p) from rfl, ratioMap_dehom, coneRatio, aeval_X,
      map_mul, fromCone_algebraMap, coneToLaurentPolynomial, eval₂Hom_X', map_mul, ← mul_assoc]
    have hu : fromCone i (((isUnit_coneX i p.1).unit : (ConeRing i)ˣ) : ConeRing i) =
        algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X p.1) := by
      rw [IsUnit.unit_spec, fromCone_algebraMap, coneToLaurent_X_self]
    have hinv : fromCone i (((isUnit_coneX i p.1).unit⁻¹ : (ConeRing i)ˣ) : ConeRing i) *
        algebraMap (MvPolynomial K (DehomRing i)) (Laurent i) (X p.1) = 1 := by
      rw [← hu, ← map_mul, Units.inv_mul, map_one]
    rw [mul_comm _ (algebraMap _ _ (C _)), mul_assoc, hinv, mul_one]

theorem fromCone_comp_toCone : (fromCone i).comp (toCone i) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tProd i))
  apply MvPolynomial.ringHom_ext
  · intro y
    have h := RingHom.congr_fun (fromCone_comp_ratioMap i) y
    simp only [RingHom.comp_apply, RingHom.id_apply, toCone, IsLocalization.Away.lift_eq, laurentToConeRing,
      eval₂Hom_C] at h ⊢
    exact h
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply, toCone, IsLocalization.Away.lift_eq, laurentToConeRing, eval₂Hom_X']
    rw [fromCone_algebraMap, coneToLaurent_X_self]

def laurentEquiv : Laurent i ≃+* ConeRing i :=
  RingEquiv.ofRingHom (toCone i) (fromCone i) (toCone_comp_fromCone i) (fromCone_comp_toCone i)

theorem toCone_comp_algebraMap : (toCone i).comp (algebraMap (DehomRing i) (Laurent i)) = ratioMap i := by
  refine RingHom.ext fun y => ?_
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (DehomRing i) (MvPolynomial K (DehomRing i)) (Laurent i),
    toCone, IsLocalization.Away.lift_eq, MvPolynomial.algebraMap_eq, laurentToConeRing, eval₂Hom_C]

theorem map_laurent_isPrime (𝔮 : Ideal (DehomRing i)) [𝔮.IsPrime] :
    (𝔮.map (algebraMap (DehomRing i) (Laurent i))).IsPrime := by
  rw [IsScalarTower.algebraMap_eq (DehomRing i) (MvPolynomial K (DehomRing i)) (Laurent i), ← Ideal.map_map,
    MvPolynomial.algebraMap_eq]
  apply IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (tProd i)) (Laurent i) _ (map_C_isPrime 𝔮)
  rw [Set.disjoint_left]
  intro x hx hmem
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hx
  have hle : 𝔮.map (C : DehomRing i →+* MvPolynomial K (DehomRing i)) ≤
      RingHom.ker (eval₂Hom (Ideal.Quotient.mk 𝔮) fun _ : K => (1 : DehomRing i ⧸ 𝔮)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hy]
  have h0 := hle hmem
  rw [RingHom.mem_ker] at h0
  simp [tProd] at h0
  rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq_zero_iff_mem] at h0
  exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h0)

end ConeRingLaurent

theorem ConeRingLaurent.proof : ConeRingLaurent.Statement := by
  intro K _ ι i
  have hcomp : ratioMap i = (ConeRingLaurent.laurentEquiv i : ConeRingLaurent.Laurent i →+* ConeRing i).comp
      (algebraMap (DehomRing i) (ConeRingLaurent.Laurent i)) :=
    (ConeRingLaurent.toCone_comp_algebraMap i).symm
  constructor
  · rw [hcomp]
    refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (ConeRingLaurent.laurentEquiv i).bijective)
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  · intro 𝔮 h𝔮
    rw [hcomp, ← Ideal.map_map]
    have := ConeRingLaurent.map_laurent_isPrime i 𝔮
    exact Ideal.map_isPrime_of_equiv (ConeRingLaurent.laurentEquiv i)

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace CurveVerticalPointInjective

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem coord_ne_zero (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]

theorem isMultiHomogIdeal_of_mem_divSupp (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ)
    (hA : IsArithVar (mCoordIdeal y) 1) (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d) {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp (mCoordIdeal y) s) : IsMultiHomogIdeal W := by
  classical
  have hP : NumbersDVR.IsMultiHomogIdeal (mCoordIdeal y) :=
    (Bridge.isMultiHomogIdeal_iff _).2 hA.2.1.2.1
  have hJ := NumbersDVR.SupSpanMultiHomog.full.{0} ℤ K ι (mCoordIdeal y) s d hP
    ((Bridge.isMultiHomog_iff s _).2 hs)
  exact (Bridge.isMultiHomogIdeal_iff _).1
    (NumbersDVR.MinimalPrimeMultiHomog.full.{0} ℤ K ι _ W hJ hW.1)

end CurveVerticalPointInjective


open CurveVerticalPointInjective in
theorem CurveVertPointInj.proof (hCh : CurveVertPointChart.Statement) : CurveVertPointInj.Statement := by
  intro K _ ι _ Ω _ y s d hA hs hsP W hW W' hW' hWW'
  choose c hc using hW.2
  choose c' hc' using hW'.2
  obtain ⟨hmax, hrat, hform⟩ := hCh K ι Ω y s d hA hs hsP W hW c hc
  obtain ⟨-, -, hform'⟩ := hCh K ι Ω y s d hA hs hsP W' hW' c' hc'
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k =>
    coord_ne_zero y _ fun h => hc k (le_sup_left.trans hW.1.1.2 h)
  choose a' b' hb' hab' using fun k => hrat ⟨k, c' k⟩
  have hab'' : ∀ k, (b' k : Ω) * y ⟨k, c' k⟩ = a' k * y ⟨k, c k⟩ := fun k => by
    rw [← hab' k]; field_simp [hyc k]
  have hle : W' ≤ W := by
    obtain ⟨S, hS, hSeq⟩ := isMultiHomogIdeal_of_mem_divSupp y s d hA hs hW'
    rw [hSeq, Ideal.span_le]
    intro g hg
    obtain ⟨e, he⟩ := hS g hg
    obtain ⟨a, b, ha, hb, habg⟩ := (hform' e g he).1 (hSeq ▸ Ideal.subset_span hg)
    rw [← hWW'] at ha hb
    refine (hform e g he).2 ⟨a * ∏ k, a' k ^ e k, (∏ k, b' k ^ e k) * b, Ideal.mul_mem_right _ _ ha, ?_, ?_⟩
    · intro h
      rcases hmax.isPrime.mem_or_mem h with h | h
      · obtain ⟨k, -, hk⟩ := (hmax.isPrime.prod_mem_iff (s := Finset.univ)).1 h
        exact hb' k (hmax.isPrime.mem_of_pow_mem _ hk)
      · exact hb h
    · push_cast
      calc (∏ k, (b' k : Ω) ^ e k) * b * aeval y g
          = a * ∏ k, ((b' k : Ω) * y ⟨k, c' k⟩) ^ e k := by
            rw [mul_assoc, habg, Finset.prod_congr rfl fun k _ => mul_pow (b' k : Ω) _ (e k),
              Finset.prod_mul_distrib]; ring
        _ = (a * ∏ k, (a' k : Ω) ^ e k) * ∏ k, y ⟨k, c k⟩ ^ e k := by
            simp_rw [hab'', mul_pow, Finset.prod_mul_distrib]; ring
  exact le_antisymm (hW.1.2 ⟨hW'.1.1.1, hW'.1.1.2⟩ hle) hle

end GroundTheory.Heights₂.Heights.Targets
end
