module

public import Formalism.HarderNarasimhan.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle138
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle157
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
import Formalism.FormalDegreeBessel.StatementWR
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.DualBound

theorem opNorm_sq_le_hs {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ^ 2 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by positivity
  have h : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hS, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) x) i‖ ≤
        ∑ j, ‖M i j‖ * ‖x j‖ := by
      have : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) x) i =
          ∑ j, M i j * x j := by
        simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
      rw [this]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  calc _ ≤ (Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS

theorem card_mul_geom_sq_le {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * ((∏ i, z i) ^ ((1 : ℝ) / (Fintype.card ι : ℝ))) ^ 2 ≤
      ∑ i, z i ^ 2 := by
  have hf : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (1 : ℝ) / (Fintype.card ι : ℝ)) (fun i => z i ^ 2)
    (fun _ _ => by positivity) (by simp [hf.ne']) (fun _ _ => by positivity)
  have hp : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), Finset.prod_pow, ← Finset.mul_sum] at h
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp, mul_comm (1 / _ : ℝ), Real.rpow_mul hp,
    Real.rpow_natCast]
  calc _ ≤ (Fintype.card ι : ℝ) * (1 / (Fintype.card ι : ℝ) * ∑ i, z i ^ 2) :=
        mul_le_mul_of_nonneg_left h hf.le
    _ = _ := by field_simp

theorem size_different_smul {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    {a : ℕ} (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (hX : ∀ w, IsUnit (X w).det)
    {N : Submodule (𝓞 K) (Fin a → K)} (hN : N.FG) (hN0 : N ≠ ⊥) :
    Formalism.HN.size (Pi.basisFun K (Fin a)) X (differentIdeal ℤ (𝓞 K) • N) =
      Formalism.HN.size (Pi.basisFun K (Fin a)) X N * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) := by
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hrk : rkK (differentIdeal ℤ (𝓞 K) • N) = rkK N := by
    unfold rkK; rw [Formalism.HN.DualPolygon.twist_span_smul N _ hd]
  have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
  have hj : (rkK N : ℝ) ≠ 0 := by exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
  have hf : (Formalism.HN.nPl K : ℝ) ≠ 0 := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  unfold Formalism.HN.size
  rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hN hd, hrk, hnorm,
    Real.mul_rpow (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hN).le (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  field_simp

theorem hs_lower_bound :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ) (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → 0 < lo → (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) → Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi → ∀ ψ : Matrix (Fin a) (Fin b) K, (∃ y ∈ B, ψ *ᵥ y ≠ 0) → (∀ δ ∈ differentIdeal ℤ (𝓞 K), ∀ y ∈ B, δ • (ψ *ᵥ y) ∈ A) → (Formalism.HN.nPl K : ℝ) * (lo / (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi)) ^ 2 ≤ ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ψ.map w.embedding * X' w) i j‖ ^ 2 := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' _ hB hlo hA hhi ψ ⟨y, hyB, hy⟩ hψ
  set φ : (Fin b → K) →ₗ[K] (Fin a → K) := Matrix.toLin' ψ with hφ
  set A' : Submodule (𝓞 K) (Fin a → K) := B.map (φ.restrictScalars (𝓞 K)) with hA'
  set rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) with hrd
  have hrdpos : 0 < rd :=
    Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)) _
  have hA'fg : A'.FG := hB.map _
  have hA'0 : A' ≠ ⊥ := by
    intro h
    have : ψ *ᵥ y ∈ A' := ⟨y, hyB, by simp [hφ]⟩
    rw [h] at this
    exact hy this
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact hA'0 (by rw [hA', Submodule.map_bot])
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hleast : lo / rd ≤ leastSize (Pi.basisFun K (Fin a)) X A' := by
    refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
    have h1 : differentIdeal ℤ (𝓞 K) • N ≤ A := by
      refine Submodule.smul_le.2 fun δ hδ v hv => ?_
      obtain ⟨z, hz, rfl⟩ := hN hv
      simpa [hφ] using hψ δ hδ z hz
    have h2 : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
      intro h
      have h3 := Formalism.HN.DualPolygon.twist_span_smul N _ hd
      rw [h] at h3
      apply hN0
      rw [eq_bot_iff]
      intro v hv
      have : v ∈ Submodule.span K (N : Set (Fin a → K)) := Submodule.subset_span hv
      rw [← h3] at this
      simpa using this
    have h3 := hA _ h1 h2
    rw [size_different_smul X hX hNfg hN0] at h3
    rw [div_le_iff₀ hrdpos]
    exact h3
  have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
    rw [(sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
    exact Real.exp_pos _
  have hM := sizeIneq K _ _ _ _ (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
    hB hA'fg le_rfl hA'0
  have hhipos : 0 < hi := hLpos.trans_le hhi
  have h4 : lo / (rd * hi) ≤
      (∏ v, opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ) ^
        ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
    refine le_trans ?_ hM
    rw [← div_div]
    exact div_le_div₀ ((div_pos hlo hrdpos).le.trans hleast) hleast hLpos hhi
  have h5 := card_mul_geom_sq_le
    (fun v => opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ)
    (fun v => norm_nonneg _)
  calc _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h4 2) (Nat.cast_nonneg _)
    _ ≤ _ := h5
    _ ≤ _ := by
      refine Finset.sum_le_sum fun w _ => ?_
      have h6 : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a)) φ = ψ := by
        ext i j
        simp [hφ]
      unfold opNormAt
      rw [h6]
      exact opNorm_sq_le_hs _

end GlobalTheory.DualBound
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ValueSpaceCoordinates

theorem rowAct_mem_delSq {n : ℕ} (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ delSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam := by
  have hanti : Antitone lam.natW := by
    intro i j hij
    have h := lam.anti hij
    simp only [DomWeight.natW]
    exact Int.toNat_le_toNat (by omega)
  have hw := Formalism.L2.Col.dualWeyl_eq_weyl ℂ (le_rfl : n ≤ n) lam.natW hanti
  change p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW at hp
  change Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW
  rw [← hw] at hp ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n lam.natW g p hp

theorem eval_rowAct {n : ℕ} (g x : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : Fin n × Fin n => x v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      MvPolynomial.eval (fun v : Fin n × Fin n => (g * x) v.1 v.2) p := by
  have key : (MvPolynomial.eval fun v : Fin n × Fin n => x v.1 v.2).comp
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).toRingHom =
      MvPolynomial.eval fun v : Fin n × Fin n => (g * x) v.1 v.2 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
  simpa using RingHom.congr_fun key p

theorem eval_ten {ι : Type} [Fintype ι] {n : ℕ} (x : ι → Matrix (Fin n) (Fin n) ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : ι × Fin n × Fin n => x v.1 v.2.1 v.2.2) (ten f) =
      ∏ τ, MvPolynomial.eval (fun v : Fin n × Fin n => x τ v.1 v.2) (f τ) := by
  unfold Formalism.L2.Forms.ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval_rename]
  rfl

theorem fnOf_mul_ten {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A B : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    fnOf G s (A * B) (ten f) =
      (∏ τ, (A τ).det ^ s τ) • fnOf G s B (ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ)) := by
  ext y
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [eval_ten (fun τ => (A * B) τ * y.1 τ) f,
    eval_ten (fun τ => B τ * y.1 τ) (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ))]
  simp only [eval_rowAct, Pi.mul_apply, Matrix.mul_assoc, Matrix.det_mul, mul_zpow,
    Finset.prod_mul_distrib]
  ring

theorem map_fnOf_mul_le {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (A B : ι → Matrix (Fin n) (Fin n) ℂ) :
    (CSpan lam).map (fnOf G s (A * B)) ≤ (CSpan lam).map (fnOf G s B) := by
  unfold CSpan
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨q, ⟨f, hf, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, fnOf_mul_ten]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span
    ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ), fun τ => rowAct_mem_delSq (lam τ) (A τ) (f τ) (hf τ), rfl⟩))

theorem map_fnOf_eq_ValC :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G M : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (M τ).det) → (CSpan lam).map (fnOf G (shiftOf lam) M) = ValC G lam := by
  intro ι _ n lam G M hM
  have hinv : (fun τ => (M τ)⁻¹) * M = 1 := by
    funext τ
    simp only [Pi.mul_apply, Pi.one_apply]
    exact Matrix.nonsing_inv_mul (M τ) (hM τ)
  unfold ValC
  apply le_antisymm
  · have h := map_fnOf_mul_le lam G (shiftOf lam) M 1
    rwa [mul_one] at h
  · have h := map_fnOf_mul_le lam G (shiftOf lam) (fun τ => (M τ)⁻¹) M
    rwa [hinv] at h

end GlobalTheory.ValueSpaceCoordinates
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IsoFrame

private theorem half_smul_sub_mul_mul_mul_self {n : ℕ} (A S : Matrix (Fin n) (Fin n) ℂ) (hAA : A * A = A + A)
    (hSAS : S * A * S = S) :
    ((1 / 2 : ℂ) • (A - A * S * A)) * ((1 / 2 : ℂ) • (A - A * S * A)) =
      (1 / 2 : ℂ) • (A - A * S * A) := by
  have h5 : A * S * A * S * A = A * S * A := by
    rw [show A * S * A * S * A = A * (S * A * S) * A by noncomm_ring, hSAS]
  have key : (A - A * S * A) * (A - A * S * A) = (A - A * S * A) + (A - A * S * A) := by
    calc (A - A * S * A) * (A - A * S * A)
        = A * A - (A * A) * S * A - A * S * (A * A) + A * S * (A * A) * S * A := by noncomm_ring
      _ = (A + A) - (A + A) * S * A - A * S * (A + A) + A * S * (A + A) * S * A := by rw [hAA]
      _ = (A + A) - (A * S * A + A * S * A) - (A * S * A + A * S * A)
            + (A * S * A * S * A + A * S * A * S * A) := by noncomm_ring
      _ = (A - A * S * A) + (A - A * S * A) := by rw [h5]; abel
  rw [Matrix.smul_mul, Matrix.mul_smul, key, ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

theorem exists_eigenframe {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (hJJ : J * J = 1) (hJh : Jᴴ = J) (p : ℕ)
    (hp : Matrix.trace (1 + J) = 2 * (p : ℂ)) {a : ℕ} (j : Fin a → ℕ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (h3 : ∀ i k, (T i)ᴴ * J * T k = 0) :
    ∃ P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ, (∀ i, (T i)ᴴ * P = 0) ∧ Pᴴ * P = 1 ∧ J * P = P ∧
      P * Pᴴ = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by

  have hA : ∀ i k, (T i)ᴴ * (1 + J) * T k = (T i)ᴴ * T k := by
    intro i k
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h3, add_zero]
  have hTS : ∀ i, (T i)ᴴ * (1 + J) * (∑ k, T k * (T k)ᴴ) = (T i)ᴴ := by
    intro i
    rw [Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, hA, h1, Matrix.one_mul]
    · intro k _ hk
      rw [← Matrix.mul_assoc, hA, h2 i k (Ne.symm hk), Matrix.zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hSAS : (∑ k, T k * (T k)ᴴ) * (1 + J) * (∑ k, T k * (T k)ᴴ) = ∑ k, T k * (T k)ᴴ := by
    rw [Matrix.mul_assoc, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (T k)ᴴ, hTS]
  have hAA : (1 + J) * (1 + J) = (1 + J) + (1 + J) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hJJ]; abel
  have hJA : J * (1 + J) = 1 + J := by
    rw [Matrix.mul_add, Matrix.mul_one, hJJ, add_comm]

  have hRR := half_smul_sub_mul_mul_mul_self (1 + J) (∑ k, T k * (T k)ᴴ) hAA hSAS
  have hAh : (1 + J)ᴴ = 1 + J := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hJh]
  have hSh : (∑ k, T k * (T k)ᴴ)ᴴ = ∑ k, T k * (T k)ᴴ := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hRh : ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))ᴴ
      = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hAh, hSh, ← Matrix.mul_assoc]
    congr 1
    simp

  have htrS : Matrix.trace ((1 + J) * (∑ k, T k * (T k)ᴴ)) = ∑ k, (j k : ℂ) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, h1, Matrix.trace_one,
      Fintype.card_fin]
  have htrR : Matrix.trace ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))
      = (p : ℂ) - ∑ i, (j i : ℂ) := by
    rw [Matrix.trace_smul, Matrix.trace_sub, hp, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hAA,
      Matrix.add_mul, Matrix.trace_add, htrS]
    simp only [smul_eq_mul]; ring
  obtain ⟨r, P, hPP, hPR⟩ := GlobalTheory.hermitian_idempotent_eq_isometry_mul_conjTranspose n _ hRh hRR
  have hr : (r : ℂ) = (p : ℂ) - ∑ i, (j i : ℂ) := by
    rw [← htrR, ← hPR, Matrix.trace_mul_comm, hPP, Matrix.trace_one, Fintype.card_fin]
  have hr' : r = p - ∑ i, j i := by
    have hc : ((r + ∑ i, j i : ℕ) : ℂ) = (p : ℂ) := by push_cast; rw [hr]; ring
    have h' : r + ∑ i, j i = p := by exact_mod_cast hc
    omega
  subst hr'
  have hRP : (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) * P = P := by
    rw [← hPR, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hTR : ∀ i, (T i)ᴴ * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))) = 0 := by
    intro i
    rw [Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hTS, sub_self, smul_zero]
  have hJR : J * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))
      = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by
    rw [Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hJA]
  refine ⟨P, fun i => ?_, hPP, ?_, hPR⟩
  · rw [← hRP, ← Matrix.mul_assoc, hTR i, Matrix.zero_mul]
  · rw [← hRP, ← Matrix.mul_assoc, hJR]

theorem complete_isotropic_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) → (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) → (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) → ∃ (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 := by
  intro n ε p q hp hq a j T h1 h2 h3

  have hJdef : Formalism.REAL.Jm ε = Matrix.diagonal (fun b => if ε b = true then (1 : ℂ) else -1) := by
    unfold Formalism.REAL.Jm
    try rfl
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [hJdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext b; split_ifs <;> norm_num
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [hJdef, Matrix.diagonal_conjTranspose]
    congr 1; funext b; simp only [Pi.star_apply]; split_ifs <;> simp
  have htp : Matrix.trace (1 + Formalism.REAL.Jm ε) = 2 * (p : ℂ) := by
    rw [hJdef, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.trace_diagonal]
    refine (Finset.sum_congr rfl (g := fun b => if ε b = true then (2 : ℂ) else 0) fun b _ => ?_).trans ?_
    · try dsimp only
      cases ε b <;> norm_num
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hp]; ring
  have htq : Matrix.trace (1 + -Formalism.REAL.Jm ε) = 2 * (q : ℂ) := by
    rw [hJdef, ← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.diagonal_add, Matrix.trace_diagonal]
    refine (Finset.sum_congr rfl (g := fun b => if ε b = false then (2 : ℂ) else 0) fun b _ => ?_).trans ?_
    · try dsimp only
      cases ε b <;> norm_num
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hq]; ring

  obtain ⟨P, hP0, hPP, hJP, hPR⟩ := exists_eigenframe _ hJJ hJh p htp j T h1 h2 h3
  have h3' : ∀ i k, (T i)ᴴ * (-Formalism.REAL.Jm ε) * T k = 0 := by
    intro i k; rw [Matrix.mul_neg, Matrix.neg_mul, h3, neg_zero]
  obtain ⟨Q, hQ0, hQQ, hJQ, hQR⟩ := exists_eigenframe (-Formalism.REAL.Jm ε)
    (by rw [neg_mul_neg, hJJ]) (by rw [Matrix.conjTranspose_neg, hJh]) q htq j T h1 h2 h3'
  refine ⟨P, Q, hP0, hQ0, hPP, hQQ, hJP, ?_, ?_⟩
  · rw [Matrix.neg_mul, neg_eq_iff_eq_neg] at hJQ; exact hJQ
  · have hsum : (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε))
        = (∑ i, T i * (T i)ᴴ) + Formalism.REAL.Jm ε * (∑ i, T i * (T i)ᴴ) * Formalism.REAL.Jm ε := by
      rw [Finset.sum_add_distrib, Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    rw [hsum, hPR, hQR]
    generalize (∑ i, T i * (T i)ᴴ) = S
    generalize Formalism.REAL.Jm ε = J

    have hX : ((1 + J) - (1 + J) * S * (1 + J)) + ((1 + -J) - (1 + -J) * S * (1 + -J))
        = (1 - S - J * S * J) + (1 - S - J * S * J) := by noncomm_ring
    rw [add_assoc (S + J * S * J), ← smul_add, hX, ← two_smul ℂ, smul_smul,
      show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
    abel

end GlobalTheory.IsoFrame
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.volume_image_of_sqrt_two_isometric_linearEquiv : ∀ (A B F : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (r : ℕ) (L : ((A × A) × ((Fin r → ℂ) × B)) ≃L[ℝ] F), (∀ v, ‖L v‖ ^ 2 = ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2) → ∀ s : Set ((A × A) × ((Fin r → ℂ) × B)), MeasurableSet s → volume (L '' s) = 2 ^ r * volume s := by
  first | exact @GlobalTheory.CellDens.ScaledVol.volume_image_eq | exact GlobalTheory.CellDens.ScaledVol.volume_image_eq | (intros; apply GlobalTheory.CellDens.ScaledVol.volume_image_eq <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.thinUnitaryTube_volume_limit_arith : ∀ (k : ℕ) (c c₀ : ℝ) (F F' M V : ℝ → ℝ≥0∞), 0 < c → 0 < c₀ → (∀ t s : ℝ, 0 < t → t < s → F t ≤ F' t ∧ F' t ≤ F s) → (∀ ρ : ℝ, 0 < ρ → 0 < V ρ ∧ V ρ < ⊤) → Tendsto (fun ρ : ℝ => M ρ / V ρ) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c₀)) → Tendsto (fun ρ : ℝ => M ρ * (F (ρ ^ 2 / 2) * ENNReal.ofReal (ρ / Real.pi)) / (V ρ * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c)) → Tendsto (fun t : ℝ => F' t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  first | exact @GlobalTheory.Tube.thin_tube_limit_arith | exact GlobalTheory.Tube.thin_tube_limit_arith | (intros; apply GlobalTheory.Tube.thin_tube_limit_arith <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.rotationInvariant_measure_unitCircle_arc : ∀ (τ : Measure ℂ) (ρ : ℝ), τ Set.univ < ⊤ → τ {z | ‖z‖ ≠ 1} = 0 → (∀ u : ℂ, ‖u‖ = 1 → τ.map (fun z => u * z) = τ) → 0 < ρ → ρ ≤ Real.pi → τ ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) = τ Set.univ * ENNReal.ofReal (ρ / Real.pi) := by
  first | exact @GlobalTheory.CircleArc.measure_arc | exact GlobalTheory.CircleArc.measure_arc | (intros; apply GlobalTheory.CircleArc.measure_arc <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_massOne_cutoff_doubleCoset_integral : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (K : Subgroup G) (K' : Subgroup H) (x : G) (S : Set G), IsOpen (K : Set G) → IsOpen (K' : Set H) → IsCompact (K' : Set H) → (∀ h, h ∈ K' ↔ x⁻¹ * j h * x ∈ K) → (∀ g, g ∈ S ↔ ∃ h, ∃ k ∈ K, g = j h * x * k) → ∃ b : G → ENNReal, Measurable b ∧ (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) ∧ ∫⁻ g, S.indicator 1 g * b g ∂μ = μ K / ν K' := by
  first | exact @GlobalTheory.StabUnfold.exists_cutoff_doubleCoset | exact GlobalTheory.StabUnfold.exists_cutoff_doubleCoset | (intros; apply GlobalTheory.StabUnfold.exists_cutoff_doubleCoset <;> assumption)
end
