module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle283
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle274
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle275
public import Formalism.CyclotomicNorms.StatementT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle276
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem exists_map_eq_of_mem_sq_sup_pow {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (l N : ℕ) (π : A) (z u : B) (hπ : φ π = z) (hu : (l : B) = z * u) (a : A)
    (ha : a ∈ Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) :
    ∃ x y : B, φ a = (l : B) ^ 2 * x + z ^ N * y := by
  have hsub : Ideal.span {(l : B), z} ≤ Ideal.span {z} := by
    rw [Ideal.span_le]
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · rw [SetLike.mem_coe, hu]
      exact Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mem_span_singleton_self z
  have hmap : Ideal.map φ (Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) ≤
      Ideal.span {(l : B) ^ 2, z ^ N} := by
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_pair]
    simp only [map_pow, map_natCast, hπ]
    refine sup_le (Ideal.span_mono (by simp)) ?_
    calc Ideal.span {(l : B), z} ^ N ≤ Ideal.span {z} ^ N := Ideal.pow_right_mono hsub N
      _ = Ideal.span {z ^ N} := Ideal.span_singleton_pow z N
      _ ≤ _ := Ideal.span_mono (by simp)
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp (hmap (Ideal.mem_map_of_mem φ ha))
  exact ⟨x, y, by rw [← hxy]; ring⟩

theorem norm_kap_lt_rho1_of_mem_sq_sup_pow :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (j n f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (ζ : OC l), 1 ≤ j → IsPrimitiveRoot (ζ : PadicComplex l) (l ^ j) → φ letπ = (ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ∀ a ∈ Ideal.span {((l : ℕ) : LetA ↥(OL LL) n) ^ 2} ⊔ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) n), letπ}) ^ (l ^ j), ∀ k, ‖kap o (φ a) k‖ < rho1 l := by
  intro l _ LL j n f o φ ζ hj hζ hφ a ha k
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hζn : ‖(ζ : PadicComplex l) - 1‖ =
      (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) :=
    norm_primitiveRoot_sub_one l j hj _ hζ
  have hlnorm : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := norm_natCast_prime_padicComplex l
  have hz0 : (ζ : PadicComplex l) - 1 ≠ 0 := by
    rw [← norm_pos_iff, hζn]
    positivity
  have hle : ‖(l : PadicComplex l)‖ ≤ ‖(ζ : PadicComplex l) - 1‖ := by
    rw [hlnorm, hζn, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le hl.le
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) := one_le_pow₀ hl.le
    have h2 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by nlinarith
    rw [neg_div, neg_le_neg_iff, div_le_one (by linarith)]
    exact h2
  let u : OC l := ⟨(l : PadicComplex l) / ((ζ : PadicComplex l) - 1), by
    rw [mem_OC, norm_div]
    exact div_le_one_of_le₀ hle (norm_nonneg _)⟩
  have hu : ((l : ℕ) : OC l) = (ζ - 1) * u := by
    apply Subtype.ext
    push_cast
    change (l : PadicComplex l) =
      ((ζ : PadicComplex l) - 1) * ((l : PadicComplex l) / ((ζ : PadicComplex l) - 1))
    field_simp
  have huO : ((l : ℕ) : OCO LL) =
      ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * (u ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hu,
      ← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]
  obtain ⟨x, y, hxy⟩ := exists_map_eq_of_mem_sq_sup_pow φ l (l ^ j) letπ _ _ hφ huO a ha
  have e1 : ((l : ℕ) : OCO LL) ^ 2 = (((l : ℕ) : OC l) ^ 2) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_pow, map_natCast]
  have e2 : ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) ^ (l ^ j) =
      ((ζ - 1) ^ (l ^ j)) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [hxy, kap_add, e1, e2, kap_tmul_one_mul, kap_tmul_one_mul]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hlnorm]
    calc ((l : ℝ)⁻¹) ^ 2 * ‖kap o x k‖ ≤ ((l : ℝ)⁻¹) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o x k) (by positivity)
      _ = (l : ℝ) ^ (-(2 : ℝ)) := by
          rw [mul_one, inv_pow, Real.rpow_neg (by positivity)]
          norm_cast
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl]
          have h3 : -1 ≤ -(1 : ℝ) / ((l : ℝ) - 1) := by
            rw [neg_div, neg_le_neg_iff, div_le_one hq]
            linarith
          linarith
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hζn]
    calc ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * ‖kap o y k‖
        ≤ ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o y k) (by positivity)
      _ = (l : ℝ) ^ (-(l : ℝ) / ((l : ℝ) - 1)) := by
          rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1
          have hp : (0 : ℝ) < (l : ℝ) ^ (j - 1) := by positivity
          have hpow : ((l ^ j : ℕ) : ℝ) = (l : ℝ) * (l : ℝ) ^ (j - 1) := by
            rw [Nat.cast_pow, ← pow_succ']
            congr 1
            omega
          rw [hpow]
          field_simp
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl, div_lt_div_iff_of_pos_right hq]
          linarith

end GlobalTheory.Cyc.Decomp
end

section

open Matrix Polynomial

namespace GlobalTheory.UnitDiscAlg

section Residue
variable (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]

def unitBallMaxIdeal : Ideal (unitBallSubring E) := GlobalTheory.ClosedBallValuationSubring.openBallIdeal E

theorem mem_unitBallMaxIdeal {t : unitBallSubring E} :
    t ∈ unitBallMaxIdeal E ↔ ‖(t : E)‖ < 1 := Iff.rfl

theorem unitBallMaxIdeal_isMaximal : (unitBallMaxIdeal E).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    have h' : ‖((1 : E))‖ < 1 := h
    simp at h'
  · intro J x _ hx hxJ
    have hx1 : ¬ ‖(x : E)‖ < 1 := hx
    have hx2 : ‖(x : E)‖ ≤ 1 := x.2
    have hn : ‖(x : E)‖ = 1 := le_antisymm hx2 (not_lt.mp hx1)
    have hx0 : (x : E) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    have hinv : ‖(x : E)⁻¹‖ ≤ 1 := by rw [norm_inv, hn, inv_one]
    have hmem := J.mul_mem_left ⟨(x : E)⁻¹, hinv⟩ hxJ
    convert hmem using 1
    apply Subtype.ext
    exact (inv_mul_cancel₀ hx0).symm

end Residue

theorem norm_lt_one_of_pow_of_commute (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hb : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (w : Matrix (Fin n) (Fin n) E) (hwN : w * N = N * w) (hw : ∀ i j, ‖w i j‖ ≤ 1)
    (M : ℕ) (hM : ∀ i j, ‖(w ^ M) i j‖ < 1) : ∀ i j, ‖w i j‖ < 1 := by
  intro i j
  have hM0 : M ≠ 0 := by
    rintro rfl
    have := hM i i
    simp at this
  obtain ⟨u, v, hu, hv, huv⟩ := hb
  haveI := unitBallMaxIdeal_isMaximal E
  letI : Field (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.field _
  let O := unitBallSubring E
  let π : O →+* (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.mk _
  let N' : Matrix (Fin n) (Fin n) O := fun a b => ⟨N a b, hN a b⟩
  let w' : Matrix (Fin n) (Fin n) O := fun a b => ⟨w a b, hw a b⟩
  have hNm : O.subtype.mapMatrix N' = N := by ext; rfl
  have hwm : O.subtype.mapMatrix w' = w := by ext; rfl
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _) := by
    intro a b h
    ext x y
    exact congrFun (congrFun h x) y
  have hwN' : w' * N' = N' * w' := hinj (by rw [map_mul, map_mul, hNm, hwm, hwN])
  have hu' : (u.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hu m
  have hv' : (v.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hv m
  have hNmap : N'.map O.subtype = N := by ext; rfl
  have hbO : u.toSubring O hu' * N'.charpoly + v.toSubring O hv' * derivative N'.charpoly = 1 := by
    apply Polynomial.map_injective O.subtype Subtype.val_injective
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      Polynomial.map_toSubring, Polynomial.map_toSubring, ← Matrix.charpoly_map, hNmap,
      Polynomial.map_one]
    exact huv
  set N'' := N'.map π with hN''
  set w'' := w'.map π with hw''
  have hbk : (u.toSubring O hu').map π * N''.charpoly
      + (v.toSubring O hv').map π * derivative N''.charpoly = 1 := by
    have := congrArg (Polynomial.map π) hbO
    simpa [hN'', Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.derivative_map,
      Matrix.charpoly_map] using this
  have hwk : w'' * N'' = N'' * w'' := by
    rw [hN'', hw'', ← Matrix.map_mul, ← Matrix.map_mul, hwN']
  have hs : N''.charpoly.Separable := ⟨_, _, hbk⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RegSS.cyclicField (unitBallSubring E ⧸ unitBallMaxIdeal E) (Fin n) N'' hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra _ (Fin n) N'' x hx).2.2
  have hmem : w'' ∈ Algebra.adjoin (unitBallSubring E ⧸ unitBallMaxIdeal E) {N''} :=
    GlobalTheory.RegSS.mem_genAlg_of_commute hbij hwk
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨f, hf⟩ := hmem
  have hpowm : O.subtype.mapMatrix (w' ^ M) = w ^ M := by rw [map_pow, hwm]
  have hpow : w'' ^ M = 0 := by
    rw [hw'', ← Matrix.map_pow]
    ext a b
    rw [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem, mem_unitBallMaxIdeal]
    have := congrFun (congrFun hpowm a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    show ‖(((w' ^ M) a b : O) : E)‖ < 1
    rw [show (((w' ^ M) a b : O) : E) = (w ^ M) a b from this]
    exact hM a b
  have hfM : aeval N'' (f ^ M) = 0 := by
    rw [map_pow]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [hf, hpow]
  have hdvd := minpoly.dvd _ N'' hfM
  have hsq : Squarefree (minpoly (unitBallSubring E ⧸ unitBallMaxIdeal E) N'') :=
    hs.squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly N'')
  have hdvd' := (Squarefree.dvd_pow_iff_dvd hsq hM0).mp hdvd
  have hf0 : aeval N'' f = 0 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd' (minpoly.aeval _ _)
  have hw0 : w'' = 0 := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [← hf, hf0]
  have hij := congrFun (congrFun hw0 i) j
  rw [hw'', Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_unitBallMaxIdeal] at hij
  exact hij

end GlobalTheory.UnitDiscAlg
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem actWCbHom_teichmuller_eq {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (g : GQ l) (c : Cb l) :
    AI.actWCbHom g (WittVector.teichmuller l c) =
      WittVector.teichmuller l (autCb l (AI.actT g) c) :=
  WittVector.map_teichmuller l (autCb l (AI.actT g)).toRingHom c

theorem exists_fix_lift_of_fix_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (H : Set (GQ l)) (x : RW LL)
    (h : ∀ g ∈ H, ∃ r, AI.gRW LL g x - x = (l : RW LL) * r) :
    ∃ y ∈ fixSub AI LL H, ∃ r, y - x = (l : RW LL) * r := by
  obtain ⟨y, hy⟩ : ∃ y : RW LL, ∀ i, crd (basisO LL) i y =
      WittVector.teichmuller l ((crd (basisO LL) i x).coeff 0) :=
    ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ((crd (basisO LL) j x).coeff 0),
      fun i => crd_sum (basisO LL) _ i⟩
  refine ⟨y, mem_fixSub.2 fun g hg => ext_crd (basisO LL) fun i => ?_,
    (dvd_iff_crd LL _).2 fun i => ?_⟩
  · have h1 := (dvd_iff_crd LL _).1 (h g hg) i
    rw [LinearMap.map_sub, sub_coeff_zero, crd_gRW, coeff_actWCbHom] at h1
    rw [crd_gRW, hy, actWCbHom_teichmuller_eq, sub_eq_zero.1 h1]
  · rw [LinearMap.map_sub, sub_coeff_zero, hy, WittVector.teichmuller_coeff_zero, sub_self]

end GlobalTheory.Decompl
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem ioE_fixed_of_resΓ_eq_one (hO : Function.Injective (algebraMap O LL)) (g : G)
    (hg : W.resΓ g = 1) (e : W.EE) : gR g (E.ioE e) = E.ioE e := by
  rw [← GlobalTheory.TorsionBoundCompare.ioE_γ E hO g e, hg, map_one]
  rfl

theorem ioE_letπ : E.ioE (algebraMap (LetA O n) W.EE letπ) = inclR πA := by
  rw [E.ioE_ext, E.io_π]

theorem ioE_bounded_pole {p : ℕ} (hp : PD.p = p) (e : W.EE) :
    ∃ c : ℕ, Near (inclR : RA →+* RW) p (inclR πA) 0 (inclR πA ^ c * E.ioE e) := by
  obtain ⟨a, m, h⟩ := W.EE_dense e 1
  rw [pow_one, Ideal.mem_span_singleton, hp] at h
  obtain ⟨r, hr⟩ := h
  have h1 := congrArg E.ioE hr
  rw [map_sub, map_mul, map_mul, map_natCast, map_pow, map_pow, ioE_letπ, E.ioE_ext] at h1
  refine ⟨m, E.io a, E.ioE r, ?_⟩
  rw [pow_zero, one_mul, ← h1]
  change _ = inclR (E.io a) + _
  ring

end Generic

theorem ioE_compat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ e, E.tie.ioE (W.φE e) = φRW LL (E.tie.ioE e)) ∧ (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ e, AI.gRW LL (g : GQ l) (E.tie.ioE e) = E.tie.ioE e) ∧ E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ) = piR AI LL s ∧ (∀ e, ∃ c : ℕ, NearPi AI LL s 0 (piR AI LL s ^ c * E.tie.ioE e)) := by
  intro l _ P AI K s LL h W E
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  exact ⟨fun e => GlobalTheory.TorsionBoundCompare.ioE_φ E.tie hO e,
    fun g hg e => ioE_fixed_of_resΓ_eq_one E.tie hO g hg e, ioE_letπ E.tie,
    fun e => ioE_bounded_pole E.tie (P.PD_p K) e⟩

end GlobalTheory.Decompl
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), (∀ c : ↥(K0 K), ‖((frK P K c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖) ∧ ∀ j : ℕ, 1 ≤ j → ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → ∃ d : ↥(K0 K), ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ j * frK P K d = c := by
  first | exact @GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective | exact GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective | (intros; apply GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem exists_exponent_small {l s : ℕ} (hl : l.Prime) (hs : Lev l s) (M n k : ℕ) (hM : 1 ≤ M)
    (hk : 2 * (M + n) ≤ k) : ∃ N : ℕ, k + 1 ≤ (l - 1) * N ∧ N + M - 1 + n ≤ s * k := by
  obtain ⟨h1, h2⟩ := hs
  by_cases h : l = 2
  · refine ⟨k + 1, by subst h; omega, ?_⟩
    have := Nat.mul_le_mul_right k (h2 h)
    omega
  · have h3 : 2 ≤ l - 1 := by have := hl.two_le; omega
    refine ⟨k / 2 + 1, ?_, ?_⟩
    · have := Nat.mul_le_mul_right (k / 2 + 1) h3
      omega
    · have := Nat.mul_le_mul_right k h1
      omega

theorem pow_mul_inv_pow_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ)
    (hs : Lev l s) (u : P.R.BdR) (hu : u ∈ FilB P 0) (hx : io AI AI.π₁ * u = 1) (M n : ℕ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ a : Ainf l,
      (l : P.R.BdR) ^ (s * k) * io AI a * u ^ (k + 1) ∈ Lat AI M n := by
  refine ⟨2 * (M + n), fun k hk a => ?_⟩
  have hu' : u ^ (k + 1) ∈ FilB P 0 := by simpa using FilB_pow hu (k + 1)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · apply FilB_le_Lat
    have := FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ (s * k) * a)) hu'
    simpa only [map_mul, map_pow, map_natCast, Nat.cast_zero] using this
  obtain ⟨N, hN1, hN2⟩ := exists_exponent_small (Fact.out : l.Prime) hs M n k hM hk
  obtain ⟨a', b', hab⟩ := Ideal.mem_span_pair.mp (GlobalTheory.T.ainf_invPi_mod_xi_pow_bounded_denominator l P AI (k + 1) N M hM hN1)
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hN2
  have hio := congrArg (io AI) hab
  simp only [map_mul, map_pow, map_natCast, map_add (f := _)] at hio
  have hxk : io AI AI.π₁ ^ (k + 1) * u ^ (k + 1) = 1 := by rw [← mul_pow, hx, one_pow]
  have hξ : io AI AI.ξ ^ M ∈ FilB P (M : ℤ) := by simpa using FilB_pow (io_ξ_mem AI) M
  refine ⟨((l : ℕ) : Ainf l) ^ e * a * a', ?_⟩
  have := FilB_zero_mul
    (FilB_zero_mul (io_mem AI (((l : ℕ) : Ainf l) ^ n * ((l : ℕ) : Ainf l) ^ e * a * b')) hu') hξ
  convert this using 1
  rw [he, pow_add, pow_add _ (N + M - 1), ← hio]
  simp only [map_mul, map_pow, map_natCast]
  linear_combination ((l : P.R.BdR) ^ n * (l : P.R.BdR) ^ e * io AI a * io AI a') * hxk

end GlobalTheory.ExpImage
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.quotientAverage_add_of_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  first | exact @GlobalTheory.CuspGeneric.avg_add_of_per | exact GlobalTheory.CuspGeneric.avg_add_of_per | (intros; apply GlobalTheory.CuspGeneric.avg_add_of_per <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.continuous_quotientAverage_periodic_family : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ (X : Type) [TopologicalSpace X] (F : X × G → ℂ), Continuous F → (∀ x, ∀ γ ∈ Γ, ∀ y, F (x, γ + y) = F (x, y)) → Continuous fun x => avg Γ (fun y => F (x, y)) := by
  first | exact @GlobalTheory.CuspGeneric.continuous_avg_of_periodic | exact GlobalTheory.CuspGeneric.continuous_avg_of_periodic | (intros; apply GlobalTheory.CuspGeneric.continuous_avg_of_periodic <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ → (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero | exact GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero | (intros; apply GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.quotientAverage_prod_fubini : ∀ (G₁ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] (G₂ : Type) [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] (Γ₁ : AddSubgroup G₁) (Γ₂ : AddSubgroup G₂), IsCoLat Γ₁ → IsCoLat Γ₂ → ∀ Φ : G₁ × G₂ → ℂ, Per (Γ₁.prod Γ₂) Φ → avg (Γ₁.prod Γ₂) Φ = avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_prod | exact GlobalTheory.CuspGeneric.avg_prod | (intros; apply GlobalTheory.CuspGeneric.avg_prod <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.quotientAverage_translate_invariant : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ Φ : G → ℂ, Per Γ Φ → ∀ y : G, avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  first | exact @GlobalTheory.CuspGeneric.avg_add_right | exact GlobalTheory.CuspGeneric.avg_add_right | (intros; apply GlobalTheory.CuspGeneric.avg_add_right <;> assumption)
end

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_order_preserving_power_hom_algClosure_primeField : ∀ (g : ℕ) [Fact g.Prime] (M n : ℕ), 0 < M → n.Coprime M → ∃ θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g, Function.Injective θ ∧ (∀ x, orderOf (θ x) = orderOf x) ∧ ∀ x, x ^ M = 1 → θ x = x ^ n := by
  first | exact @GlobalTheory.PowAut.exists_powHom_fbar | exact GlobalTheory.PowAut.exists_powHom_fbar | (intros; apply GlobalTheory.PowAut.exists_powHom_fbar <;> assumption)
end
