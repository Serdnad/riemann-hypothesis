module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle702
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle705
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle706
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundHolomorphicFrameChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle062
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

section Contact

variable {X : Type} [AddCommGroup X] {m : ℕ}

theorem sum_smul_toReal_apply' (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) (y z : X) :
    (∑ i, t i • toReal (u i)) y z = ∑ i, t i * (u i y z : ℝ) := by
  simp [LinearMap.sum_apply]

theorem toReal_sum_nsmul (n : Fin m → ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    toReal (∑ i, n i • u i) = ∑ i, (n i : ℝ) • toReal (u i) := by
  ext y z
  rw [sum_smul_toReal_apply']
  simp [LinearMap.sum_apply]

theorem sum_smul_toReal_comb {r : ℕ} (v : Fin r → Fin m → ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (c : Fin r → ℝ) :
    ∑ k, c k • toReal (∑ i, v k i • u i) = ∑ i, (∑ k, c k • fun i => (v k i : ℝ)) i • toReal (u i) := by
  ext y z
  rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    toReal_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

variable {O : Type} [CommRing O] [Module O X]

theorem sum_mem_realForms_iff (bar : O → O) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i y z, u i y z = u i z y)
    (t : Fin m → ℝ) : ∑ i, t i • toReal (u i) ∈ realForms bar X ↔
      ∀ b ∈ {b : Fin m → ℤ | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)},
        ∑ i, (b i : ℝ) * t i = 0 := by
  rw [mem_realForms]
  constructor
  · rintro ⟨-, h⟩ b ⟨a, y, z, rfl⟩
    have := h a y z
    rw [sum_smul_toReal_apply', sum_smul_toReal_apply'] at this
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using this
  · intro h
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
      exact Finset.sum_congr rfl fun i _ => by rw [hu i y z]
    · have := h _ ⟨a, y, z, rfl⟩
      rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
      simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at this
      simpa only [mul_comm] using this

end Contact

theorem exists_isCell_of_contact (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ)
    (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)) (hA : A.Finite) (hK : 0 < K)
    (hsym : ∀ i y z, u i y z = u i z y) (hnn : ∀ i y, 0 ≤ u i y y)
    (hint : ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z)
    (hle : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β))
    (hcon : ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧
      (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i))
    (hlin : ∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) →
      ∑ i, t i • toReal (u i) ∈ realForms bar X →
      (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) :
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := by
  obtain ⟨r, v, hiff, hZ⟩ := GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints m A
    {b | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)} hA
  have hbal := sum_mem_realForms_iff bar u hsym
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hvk : ∀ k, (∀ i, (0 : ℝ) ≤ (v k i : ℝ)) ∧ (∀ a ∈ A, ∑ i, (a i : ℝ) * (v k i : ℝ) ≤ 0) ∧
      (∀ b ∈ {b : Fin m → ℤ | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)},
        ∑ i, (b i : ℝ) * (v k i : ℝ) = 0) := by
    intro k
    refine (hiff _).2 ⟨Pi.single k 1, fun j => ?_, ?_⟩
    · by_cases h : j = k
      · subst h; simp
      · simp [h]
    · funext i
      rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp
  have hγR : ∀ k, toReal (∑ i, v k i • u i) = ∑ i, (v k i : ℝ) • toReal (u i) := fun k => toReal_sum_nsmul _ _
  have hγbal : ∀ k, (∑ i, v k i • u i) ∈ balForms bar X := by
    intro k
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hsym i y z]
    · have h := ((hbal _).2 (hvk k).2.2).2 a y z
      rw [← hγR] at h
      simp only [toReal_apply] at h
      exact_mod_cast h
  have hγval : ∀ k, ((linW Λ (∑ i, v k i • u i) : ℤ) : ℝ) = K * ψ.evalZ (∑ i, v k i • u i) := by
    intro k
    have h := hlin _ (hvk k).1 (hvk k).2.1 ((hbal _).2 (hvk k).2.2)
    rw [← hγR, evalR_toReal, evalW_toReal] at h
    exact h.symm
  have hcomb := sum_smul_toReal_comb v u
  refine ⟨r, fun k => ∑ i, v k i • u i, ⟨hγbal, fun k y => ?_, ?_, ?_⟩, ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_nonneg fun i _ => nsmul_nonneg (hnn i y) _
  · rw [linearOn_iff]
    intro c hc
    obtain ⟨hnt, hAt, hVt⟩ := (hiff _).2 ⟨c, hc, rfl⟩
    have h := hlin _ hnt hAt ((hbal _).2 hVt)
    rw [← hcomb, evalW_sum] at h
    have : (K : ℝ) * evalR ψ (∑ k, c k • toReal (∑ i, v k i • u i)) = K * ∑ k, c k * ψ.evalZ (∑ i, v k i • u i) := by
      rw [h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hγval]; ring
    exact mul_left_cancel₀ hKr.ne' this
  · refine ⟨K, linW Λ, hK, hγval, fun β hβ hp => ?_, fun β hβ hp heq => ?_⟩
    · rw [← evalW_toReal]; exact hle β hβ hp
    · have hpsd : toReal β ∈ psdCone (bar := bar) (X := X) := by
        have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
          (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
        simpa using this
      obtain ⟨t, ht0, htA, htB⟩ := hcon _ hpsd (by rw [evalR_toReal, evalW_toReal]; exact heq)
      have hVt := (hbal t).1 (htB ▸ toReal_mem hβ)
      choose z hz using hint β t htB
      have hz0 : ∀ i, 0 ≤ z i := fun i => by
        have := ht0 i; rw [hz i] at this; exact_mod_cast this
      have htn : ∀ i, (((z i).toNat : ℤ) : ℝ) = t i := fun i => by
        rw [Int.toNat_of_nonneg (hz0 i), hz i]
      obtain ⟨k, c, hk, hkc⟩ := hZ (fun i => (z i).toNat)
        (fun a ha => by
          have := htA a ha
          simp only [← htn] at this
          exact_mod_cast this)
        (fun b hb => by
          have := hVt b hb
          simp only [← htn] at this
          exact_mod_cast this)
      refine ⟨k, c, hk, LinearMap.ext₂ fun y w => ?_⟩
      have hβz : β y w = ∑ i, ((z i).toNat : ℤ) * u i y w := by
        have h1 : (β y w : ℝ) = ∑ i, t i * (u i y w : ℝ) := by
          rw [← toReal_apply, htB, sum_smul_toReal_apply']
        have h2 : (β y w : ℝ) = ((∑ i, ((z i).toNat : ℤ) * u i y w : ℤ) : ℝ) := by
          rw [h1]; push_cast
          exact Finset.sum_congr rfl fun i _ => by rw [← htn i]; push_cast; ring
        exact_mod_cast h2
      have hcoord : ∀ i, (k : ℤ) * ((z i).toNat : ℤ) = ∑ j, (c j : ℤ) * (v j i : ℤ) := fun i => by
        have := congrFun hkc i
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
        exact_mod_cast this
      calc (k • β) y w = (k : ℤ) * β y w := by simp
        _ = ∑ i, ((k : ℤ) * ((z i).toNat : ℤ)) * u i y w := by
          rw [hβz, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, ∑ j, (c j : ℤ) * ((v j i : ℤ) * u i y w) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoord, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (c j : ℤ) * ∑ i, (v j i : ℤ) * u i y w := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
        _ = (∑ j, c j • ∑ i, v j i • u i) y w := by
          simp [LinearMap.sum_apply, nsmul_eq_mul]
  · intro B hB hBe
    obtain ⟨t, ht0, htA, rfl⟩ := hcon B hB hBe
    obtain ⟨c, hc, rfl⟩ := (hiff _).1 ⟨ht0, htA, (hbal _).1 (mem_realForms_of_mem_psdCone hB)⟩
    exact ⟨c, hc, (hcomb c).symm⟩

end GlobalTheory.PolCell
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame


theorem _root_.GlobalTheory.T.chernPolyTopDensity_unit_and_above_rank : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (τ : ι) (Q : MvPolynomial (ι × ℕ) ℝ), chernTop ((MvPolynomial.X (τ, 0) - 1) * Q) G v = 0 ∧ ∀ k : ℕ, m τ < k → chernTop (MvPolynomial.X (τ, k) * Q) G v = 0 := by
  first | exact @GlobalTheory.GoodMetric.chernTop_unit | exact GlobalTheory.GoodMetric.chernTop_unit | (intros; apply GlobalTheory.GoodMetric.chernTop_unit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (G G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n), G =ᶠ[nhds v] G' → GlobalTheory.GoodMetric.GoodBound S c N G v → GlobalTheory.GoodMetric.GoodBound S c N G' v := by
  first | exact @GlobalTheory.GoodMetric.goodBound_congr_nhds | exact GlobalTheory.GoodMetric.goodBound_congr_nhds | (intros; apply GlobalTheory.GoodMetric.goodBound_congr_nhds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.chernFormPolyCoeff_reindex_frame : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  first | exact @GlobalTheory.ChernReindex.chernPoly_reindex | exact GlobalTheory.ChernReindex.chernPoly_reindex | (intros; apply GlobalTheory.ChernReindex.chernPoly_reindex <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.chernPoly_conj_linearSubst_curvature : ∀ {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n) (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ), IsUnit S.det → (∀ a b, curv F v (coordVec a) (coordVec b) = S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) → ∀ k, chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) (chernPoly F v' k) := by
  first | exact @GlobalTheory.ChernConj.chernPoly_conj_subst | exact GlobalTheory.ChernConj.chernPoly_conj_subst | (intros; apply GlobalTheory.ChernConj.chernPoly_conj_subst <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.topChernDensity_invariant_holomorphic_frameChange : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G K g : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (c : ι → ℝ) (v : ReciprocityTheory.L2DbarEstimates.V n), (∀ τ, 0 < c τ) → (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) v) → (∀ τ, IsUnit (g v τ).det) → (∀ τ, MContDiffAt 2 (fun w => K w τ) v) → (∀ τ, IsUnit (K v τ).det) → (∀ᶠ w in 𝓝 v, ∀ τ, G w τ = (c τ : ℂ) • (g w τ * K w τ * (g w τ)ᴴ)) → chernTop R G v = chernTop R K v := by
  first | exact @GlobalTheory.PointChern.chernTop_changeFrame | exact GlobalTheory.PointChern.chernTop_changeFrame | (intros; apply GlobalTheory.PointChern.chernTop_changeFrame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame


theorem _root_.GlobalTheory.T.chernPolyTopDensity_eq_zero_of_weightedDegree_ne_dim : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ), MvPolynomial.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) Q d → d ≠ n → chernTop Q G v = 0 := by
  first | exact @GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous | exact GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous | (intros; apply GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.holomorphicFrameChange_local_bounds : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (r : ℝ), 0 < r → (∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r)) → IsUnit (P 0).det → ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ B : ℝ, ∀ v : ReciprocityTheory.L2DbarEstimates.V n, ‖v‖ < r' → IsUnit (P v).det ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) ∧ (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) ∧ (∀ i k, ‖P v i k‖ ≤ B) ∧ (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) ∧ (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) ∧ (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) := by
  first | exact @GlobalTheory.HermFrame.holoFrame_local_bounds | exact GlobalTheory.HermFrame.holoFrame_local_bounds | (intros; apply GlobalTheory.HermFrame.holoFrame_local_bounds <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_blocks_of_blockDiagonal : ∀ (n : ℕ) (S : Finset (Fin n)) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (G : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, (∀ a ∈ S, ‖v a‖ < 1 / 2) → (Matrix.blockDiagonal' fun τ => G τ v).det ≠ 0 → (∀ p q, ContDiffAt ℝ 2 (fun u => (Matrix.blockDiagonal' fun τ => G τ u) p q) v) → GlobalTheory.GoodMetric.GoodBound S c N (fun u => Matrix.blockDiagonal' fun τ => G τ u) v → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (G τ) v := by
  first | exact @GlobalTheory.GoodMetric.goodBound_of_blockDiagonal' | exact GlobalTheory.GoodMetric.goodBound_of_blockDiagonal' | (intros; apply GlobalTheory.GoodMetric.goodBound_of_blockDiagonal' <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_holomorphic_frameChange : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (B : ℝ), ∃ c' : ℝ, ∀ (G₀ P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n), ‖v‖ < 1 → (G₀ v).det ≠ 0 → (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) → (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) → (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) → IsUnit (P v).det → (∀ i k, ‖P v i k‖ ≤ B) → (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) → (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) → (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) → GlobalTheory.GoodMetric.GoodBound S c N G₀ v → (P v * G₀ v * (P v)ᴴ).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => (P u * G₀ u * (P u)ᴴ) i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c' N (fun u => P u * G₀ u * (P u)ᴴ) v := by
  first | exact @GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame | exact GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame | (intros; apply GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.topDegreeFormCoeff_linearSubst_eq_absDet_sq_mul : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ), topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) P) = J.det * starRingEnd ℂ J.det * topCoeff P := by
  first | exact @GlobalTheory.GoodMetric.topCoeff_subst_conj | exact GlobalTheory.GoodMetric.topCoeff_subst_conj | (intros; apply GlobalTheory.GoodMetric.topCoeff_subst_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

theorem lie_coord_unitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x x₁ : (U.X k).dom), IsOrth (U.X k) x.1 → IsOrth (U.X k) x₁.1 → (U.un k x₁).x = (U.un k x).x → ∀ (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (T b' b : ℂ)) ((U.un k x₁).u τ b)) → Tᴴ * T = 1 := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x x₁ hx hx₁ e τ T hT
  obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r _ hU
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.HodgeSmooth.exists_diag_riem hσ hU W
  obtain ⟨Hm, -, -, hH⟩ := (W.period k x₁).2.2.2.2
  obtain ⟨hPx, hv⟩ := W.lie k x₁
  have h1 := hd k x₁ hx₁ (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH hPx.symm τ _ ((U.un k x₁).u τ) 1 (hv τ)
    (fun b => by
      convert GlobalTheory.isCombAt_single_of_isTanAt (U.un k x₁).x ((U.un k x₁).u τ) ((U.un k x₁).tan τ) b using 1
      show (fun b' => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) b' b) = Pi.single b 1
      funext b'
      rw [Matrix.one_apply, Pi.single_apply])
  have h2 := hd k x hx (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH (hPx.symm.trans e) τ _ ((U.un k x₁).u τ) T
    (hv τ) hT
  have h3 : d k τ • (Tᴴ * T) = d k τ • (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) := by
    rw [← h2, h1, conjTranspose_one, Matrix.mul_one]
  exact smul_right_injective _ (hd0 k τ) h3

end GlobalTheory.ShFam
end
end
