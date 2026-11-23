module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset Module

noncomputable section

namespace FrameJacobianSumAlt

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem real_inner_eq_re (x y : EuclideanSpace ℂ ι) : inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.re_sum, Complex.inner]

theorem adjoint_restrictScalars (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.adjoint (S.restrictScalars ℝ) = (LinearMap.adjoint S).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, real_inner_eq_re,
    real_inner_eq_re, LinearMap.adjoint_inner_left]

theorem areaJacobian_restrictScalars (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    areaJacobian (S.restrictScalars ℝ) = ‖LinearMap.det (LinearMap.adjoint S ∘ₗ S)‖ := by
  rw [areaJacobian, adjoint_restrictScalars, ← LinearMap.restrictScalars_comp,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.norm_def]

theorem det_adjoint_comp (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.det (LinearMap.adjoint S ∘ₗ S) =
      (Matrix.of fun i j : Fin d => inner ℂ (S (EuclideanSpace.basisFun (Fin d) ℂ i))
        (S (EuclideanSpace.basisFun (Fin d) ℂ j))).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℂ).toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    LinearMap.adjoint_inner_right, Matrix.of_apply]

end FrameJacobianSumAlt


open FrameJacobianSumAlt in
theorem FrameJacobianSum.proof : FrameJacobianSum.Statement := by
  intro d n T b
  classical
  set e := EuclideanSpace.basisFun (Fin d) ℂ
  set N : Matrix (Fin n) (Fin d) ℂ := Matrix.of fun k j => inner ℂ (b k) (T (e j)) with hN
  have hI : ∀ (I : Finset (Fin n)) (h : I.card = d),
      areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ) = ‖(rowsOf N ⟨I, h⟩).det‖ ^ 2 := by
    intro I h
    rw [areaJacobian_restrictScalars, det_adjoint_comp]
    have hG : (Matrix.of fun i j : Fin d => inner ℂ ((frameProjLin b I ∘ₗ T) (e i))
        ((frameProjLin b I ∘ₗ T) (e j))) = (rowsOf N ⟨I, h⟩)ᴴ * rowsOf N ⟨I, h⟩ := by
      ext i j
      rw [Matrix.of_apply, PiLp.inner_apply, Matrix.mul_apply, ← (I.orderIsoOfFin h).toEquiv.sum_comp]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp [rowsOf, hN, frameProjLin, conjTranspose_apply, e, RCLike.inner_apply, mul_comm]
    rw [hG, det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul', norm_pow,
      Complex.norm_real, norm_norm]
  have hT : LinearMap.det (LinearMap.adjoint T ∘ₗ T) =
      ∑ I : {I : Finset (Fin n) // I.card = d}, ((‖(rowsOf N I).det‖ ^ 2 : ℝ) : ℂ) := by
    rw [det_adjoint_comp]
    have hG : (Matrix.of fun i j : Fin d => inner ℂ (T (e i)) (T (e j))) = Nᴴ * N := by
      ext i j
      rw [Matrix.of_apply, ← b.sum_inner_mul_inner, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hN, conjTranspose_apply]
    rw [hG, CauchyBinet.proof]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hc : colsOf Nᴴ I = (rowsOf N I)ᴴ := by
      ext i j
      simp [colsOf, rowsOf, conjTranspose_apply]
    rw [hc, det_conjTranspose, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [areaJacobian_restrictScalars, hT, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity),
    Finset.sum_subtype (univ.powersetCard d) (p := fun I : Finset (Fin n) => I.card = d)
      (fun I => by simp [mem_powersetCard])]
  exact Finset.sum_congr rfl fun I _ => (hI I.1 I.2).symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteModuloEliminate.proof (hG : FiniteModuloGeneralEquation.Statement)
    (hW : WeierstrassDivisionAtPoint.Statement) : FiniteModuloEliminate.Statement := by
  intro σ τ _ _ _ x k f L c hf hfin hpow
  obtain ⟨d, F, hF, hFan, hhF, hFev, hord⟩ := hG σ τ x k f L c hf hfin hpow
  obtain ⟨n, e, he, hgen⟩ := hfin

  set t : (σ → ℂ) → ℂ := fun z => L z c - L x c with ht_def
  have ht : AnalyticAt ℂ t x :=
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c).comp L).analyticAt x).sub analyticAt_const
  let ix : Fin (n * d) → Fin n × Fin d := fun p => finProdFinEquiv.symm p
  refine ⟨n * d, fun p z => t z ^ ((ix p).2 : ℕ) * e (ix p).1 z, fun p => (ht.pow _).mul (he _), ?_⟩
  intro g hg
  obtain ⟨b, h, hb, hh, hev⟩ := hgen g hg
  choose q a hq ha hdiv using fun m => hW τ (L x) c d F (b m) hFan (hb m) hord
  have hLt : Tendsto L (𝓝 x) (𝓝 (L x)) := L.continuous.tendsto x
  refine ⟨fun p y => a (ix p).1 (ix p).2 y, fun i z => h i z + ∑ m, q m (L z) * e m z * hF i z,
    fun p => by simpa using ha (ix p).1 (ix p).2, fun i => ?_, ?_⟩
  · refine (hh i).add (Finset.univ.analyticAt_fun_sum fun m _ => ?_)
    have hqL : AnalyticAt ℂ (fun z => q m (L z)) x := (hq m).comp (L.analyticAt x)
    exact (hqL.mul (he m)).mul (hhF i)
  · have hdivL : ∀ᶠ z in 𝓝 x, ∀ m, b m (L z) = q m (L z) * F (L z) +
        ∑ j : Fin d, a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) :=
      eventually_all.2 fun m => hLt.eventually (hdiv m)
    filter_upwards [hev, hdivL, hFev] with z hz hzd hzF
    rw [hz]
    simp only [hzd, hzF, ContinuousLinearMap.comp_apply]
    have hre : ∀ φ : Fin n × Fin d → ℂ, ∑ p : Fin (n * d), φ (ix p) = ∑ m, ∑ j, φ (m, j) := fun φ => by
      rw [← Fintype.sum_prod_type']
      exact finProdFinEquiv.symm.sum_comp φ
    rw [hre (fun mj => a mj.1 mj.2 (zeroCoordinate c (L z)) * (t z ^ (mj.2 : ℕ) * e mj.1 z))]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ht_def]
    have h1 : ∑ m, (q m (L z) * ∑ i, hF i z * f i z) * e m z =
        ∑ i, ∑ m, q m (L z) * e m z * hF i z * f i z := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
    have h2 : ∀ m (j : Fin d), a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) * e m z =
        a m j (zeroCoordinate c (L z)) * ((L z c - L x c) ^ (j : ℕ) * e m z) := fun m j => by ring
    simp only [h2]
    rw [h1]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Matrix

theorem FiniteModuloGeneralEquation.proof : FiniteModuloGeneralEquation.Statement := by
  intro σ τ _ _ _ x k f L c hf ⟨n, e, he, hfin⟩ ⟨r, h, h', hh, hh', hpow⟩
  classical
  have hproj : ∀ c', AnalyticAt ℂ (fun y : τ → ℂ => y c') (L x) := fun c' =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c').analyticAt _

  let fs : Fin k → analyticAtSubring x := fun i => ⟨f i, hf i⟩
  let es : Fin n → analyticAtSubring x := fun m => ⟨e m, he m⟩
  let hs : Fin k → analyticAtSubring x := fun i => ⟨h i, hh i⟩
  let hs' : τ → analyticAtSubring x := fun c' => ⟨h' c', hh' c'⟩
  let T : analyticAtSubring (L x) := ⟨fun y => (y c - L x c) ^ r, mem_analyticAtSubring.2 (((hproj c).sub analyticAt_const).pow r)⟩
  let D : τ → analyticAtSubring (L x) := fun c' =>
    ⟨fun y => zeroCoordinate c y c' - zeroCoordinate c (L x) c', mem_analyticAtSubring.2 (by
      simp only [zeroCoordinate_apply]
      split_ifs
      · exact analyticAt_const
      · exact (hproj c').sub analyticAt_const)⟩

  choose b kk hb hkk hbk using fun (i : Fin n) (c' : τ) => hfin _ ((hh' c').mul (he i))
  obtain ⟨b1, k1, hb1, hk1, h1eq⟩ := hfin (fun _ => 1) analyticAt_const
  let bs : Fin n → τ → Fin n → analyticAtSubring (L x) := fun i c' j => ⟨b i c' j, hb i c' j⟩
  let b1s : Fin n → analyticAtSubring (L x) := fun m => ⟨b1 m, hb1 m⟩
  let M : Matrix (Fin n) (Fin n) (analyticAtSubring (L x)) :=
    Matrix.of fun i j => (if i = j then T else 0) - ∑ c', bs i c' j * D c'
  refine ⟨r * n, ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ), ?_⟩

  let J : Ideal (holGerms x) := Ideal.span (Set.range fun i => analyticAtGerm x (fs i))
  let ψ : analyticAtSubring x →+* holGerms x ⧸ J := (Ideal.Quotient.mk J).comp (analyticAtGerm x)
  let ψ' : analyticAtSubring (L x) →+* holGerms x ⧸ J := ψ.comp (analyticAtComp x L)
  have hψf : ∀ i, ψ (fs i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  have hψeq : ∀ a b : analyticAtSubring x, (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 x] b → ψ a = ψ b := fun a b hab => by
    simp only [ψ, RingHom.comp_apply, (analyticAtGerm_eq_iff a b).2 hab]
  have R1 : ψ' T = ∑ c', ψ (hs' c') * ψ' (D c') := by
    have := hψeq (analyticAtComp x L T) (∑ i, hs i * fs i + ∑ c', hs' c' * analyticAtComp x L (D c')) (by
      filter_upwards [hpow] with z hz
      simpa [analyticAtComp, T, D, hs, hs', fs] using hz)

    simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this
  have R2 : ∀ i c', ψ (hs' c') * ψ (es i) = ∑ j, ψ' (bs i c' j) * ψ (es j) := fun i c' => by
    have := hψeq (hs' c' * es i) (∑ j, analyticAtComp x L (bs i c' j) * es j +
      ∑ a, (⟨kk i c' a, hkk i c' a⟩ : analyticAtSubring x) * fs a) (by
      filter_upwards [hbk i c'] with z hz
      simpa [analyticAtComp, bs, es, hs', fs] using hz)

    simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this
  have R3 : ∑ m, ψ' (b1s m) * ψ (es m) = 1 := by
    have := hψeq 1 (∑ m, analyticAtComp x L (b1s m) * es m +
      ∑ a, (⟨k1 a, hk1 a⟩ : analyticAtSubring x) * fs a) (by
      filter_upwards [h1eq] with z hz
      simpa [analyticAtComp, b1s, es, fs] using hz)

    simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this.symm

  have hMe : (ψ'.mapMatrix M) *ᵥ (fun j => ψ (es j)) = 0 := by
    funext i
    have hdiag : ∑ j, ψ' (if i = j then T else 0) * ψ (es j) = ψ' T * ψ (es i) := by
      simp [apply_ite ψ']
    have key : ∀ c', ψ (hs' c') * ψ' (D c') * ψ (es i) = ∑ j, ψ' (bs i c' j) * ψ' (D c') * ψ (es j) := by
      intro c'
      rw [mul_right_comm, R2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring

    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sub,
    map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply, hdiag, R1, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun c' _ => key c', Finset.sum_comm, sub_eq_zero]
  have hdet : ψ' M.det = 0 := by
    rw [RingHom.map_det]
    exact det_eq_zero_of_mulVec_eq_zero _ _ (fun m => ψ' (b1s m)) hMe R3

  have hmem : analyticAtGerm x (analyticAtComp x L M.det) ∈ J := Ideal.Quotient.eq_zero_iff_mem.1 hdet
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  choose q hq using fun i => analyticAtGerm_surjective x (a i)
  refine ⟨fun i => q i, (M.det).2, fun i => (q i).2, ?_, ?_⟩
  · have hgerm : analyticAtGerm x (∑ i, q i * fs i) = analyticAtGerm x (analyticAtComp x L M.det) := by
      rw [← ha]

      simp [map_sum, map_mul, hq]
    filter_upwards [(analyticAtGerm_eq_iff _ _).1 hgerm] with z hz
    simpa [analyticAtComp, fs] using hz.symm

  · have hev : ∀ s : ℂ, ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s) = s ^ (r * n) := by
      intro s
      rw [← analyticAtEval_apply, RingHom.map_det]
      have hdg : (analyticAtEval (L x) (L x + Pi.single c s)).mapMatrix M = Matrix.diagonal fun _ => s ^ r := by
        ext i j

        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sub, map_sum, map_mul,
        apply_ite (analyticAtEval (L x) (L x + Pi.single c s)), map_zero, analyticAtEval_apply, Matrix.diagonal_apply]
        have hD : ∀ c', ((D c' : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s) = 0 := by
          intro c'
          simp only [D, zeroCoordinate_apply]
          split_ifs with hc
          · simp
          · simp [hc]
        simp [hD, T]
      rw [hdg, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [show (fun s : ℂ => ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s)) =
      fun s : ℂ => s ^ (r * n) from funext hev]
    exact ((analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).pow _).analyticOrderAt_eq_natCast.2
      ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun s => by simp⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem exists_shift_coeff (N : ℕ) (a : ℂ) :
    ∃ K : Fin N → Fin N → ℂ, ∀ (c : Fin N → ℂ) (t : ℂ),
      ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        ∑ i : Fin N, (∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by
  refine ⟨fun i j => a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ), fun c t => ?_⟩
  have hj : ∀ j : Fin N, (t + a) ^ (j : ℕ) =
      ∑ i : Fin N, t ^ (i : ℕ) * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ)) := by
    intro j
    have hr := Fin.sum_univ_eq_sum_range (fun i => t ^ i * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ))) N
    rw [hr, add_pow]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (show (j : ℕ) + 1 ≤ N by omega))]
    · exact Finset.sum_congr rfl fun i _ => by ring
    · intro i _ hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  simp_rw [hj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_monic_shift_coeff (N : ℕ) (a : ℂ) :
    ∃ (K₀ : Fin N → ℂ) (K : Fin N → Fin N → ℂ), ∀ (c : Fin N → ℂ) (t : ℂ),
      (t + a) ^ N + ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        t ^ N + ∑ i : Fin N, (K₀ i + ∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by
  obtain ⟨K, hK⟩ := exists_shift_coeff N a
  refine ⟨fun i => a ^ (N - (i : ℕ)) * (N.choose i : ℂ), K, fun c t => ?_⟩
  have hr := Fin.sum_univ_eq_sum_range (fun i => a ^ (N - i) * (N.choose i : ℂ) * t ^ i) N
  rw [hK, add_pow, Finset.sum_range_succ]
  simp only [add_mul, Finset.sum_add_distrib, hr, Nat.sub_self, pow_zero, Nat.choose_self,
    Nat.cast_one, mul_one]
  have : ∑ x ∈ Finset.range N, t ^ x * a ^ (N - x) * (N.choose x : ℂ) =
      ∑ x ∈ Finset.range N, a ^ (N - x) * (N.choose x : ℂ) * t ^ x :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

theorem coeff_eq_zero_of_forall_eval_eq_zero {N : ℕ} (e : Fin N → ℂ)
    (he : ∀ t : ℂ, ∑ i : Fin N, e i * t ^ (i : ℕ) = 0) (i : Fin N) : e i = 0 := by
  classical
  have hp : (∑ j : Fin N, Polynomial.C (e j) * Polynomial.X ^ (j : ℕ)) = 0 :=
    Polynomial.funext fun t => by simpa [Polynomial.eval_finsetSum] using he t
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj] using this

theorem analyticAt_coord {ι : Type} [Fintype ι] (i : ι) (z : ι → ℂ) :
    AnalyticAt ℂ (fun w : ι → ℂ => w i) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt z

theorem weierstrassDivision_in_coordinate (h : WeierstrassPolynomialDivision.Statement)
    {σ : Type} [Fintype σ] [DecidableEq σ] (k : σ) (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (N : ℕ)
    (b : Fin N → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ)
    (hb : ∀ j, AnalyticAt ℂ (b j) y₀)
    (hG : ∀ T : ℂ, T ^ N + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u₀ k) ^ N)
    (hf : AnalyticAt ℂ f (y₀, u₀)) :
    ∃ (q : (Fin d → ℂ) × (σ → ℂ) → ℂ) (e : Fin N → (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → ℂ),
      AnalyticAt ℂ q (y₀, u₀) ∧ (∀ i, AnalyticAt ℂ (e i) (y₀, fun m => u₀ m)) ∧
      ∀ᶠ x in 𝓝 (y₀, u₀), f x = q x * (x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ)) +
        ∑ i, e i (x.1, fun m => x.2 m) * x.2 k ^ (i : ℕ) := by
  obtain ⟨K₀, K, hK⟩ := exists_monic_shift_coeff N (u₀ k)
  obtain ⟨K', hK'⟩ := exists_shift_coeff N (-u₀ k)

  let ι : σ → Option (Fin d ⊕ {m // m ≠ k}) := fun m =>
    if hm : m = k then none else some (Sum.inr ⟨m, hm⟩)

  let φ : (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) → (Fin d → ℂ) × (σ → ℂ) := fun z =>
    (fun i => y₀ i + z (some (Sum.inl i)), fun m => u₀ m + z (ι m))

  let ψ' : (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → (Fin d ⊕ {m // m ≠ k} → ℂ) := fun x' l =>
    Sum.elim (fun i => x'.1 i - y₀ i) (fun m => x'.2 m - u₀ m) l
  let ψ : (Fin d → ℂ) × (σ → ℂ) → (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) := fun x o =>
    Option.elim o (x.2 k - u₀ k) (ψ' (x.1, fun m => x.2 m))

  let c : Fin N → (Fin d ⊕ {m // m ≠ k} → ℂ) → ℂ := fun i w =>
    K₀ i + ∑ j, b j (fun l => y₀ l + w (Sum.inl l)) * K i j
  have hc_an : ∀ i, AnalyticAt ℂ (c i) 0 := by
    intro i
    have hy : AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => fun l => y₀ l + w (Sum.inl l)) 0 :=
      AnalyticAt.pi (f := fun l (w : Fin d ⊕ {m // m ≠ k} → ℂ) => y₀ l + w (Sum.inl l)) fun l =>
        analyticAt_const.add (analyticAt_coord (Sum.inl l) 0)
    have hb' : ∀ j, AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => b j (fun l => y₀ l + w (Sum.inl l))) 0 := by
      intro j
      refine (hb j).comp_of_eq hy ?_
      funext l; simp
    exact analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => (hb' j).fun_mul analyticAt_const)
  have hc0 : ∀ i, c i 0 = 0 := by
    refine coeff_eq_zero_of_forall_eval_eq_zero (fun i => c i 0) fun t => ?_
    have h1 := hK (fun j => b j y₀) t
    have h2 := hG (t + u₀ k)
    have hy : (fun l => y₀ l + (0 : Fin d ⊕ {m // m ≠ k} → ℂ) (Sum.inl l)) = y₀ := by funext l; simp
    simp only [c, hy]
    rw [add_sub_cancel_right] at h2
    linear_combination h1.symm.trans h2
  have hφ : AnalyticAt ℂ φ 0 :=
    (AnalyticAt.pi (f := fun i (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => y₀ i + z (some (Sum.inl i))) fun i =>
      analyticAt_const.add (analyticAt_coord _ 0)).prod
    (AnalyticAt.pi (f := fun m (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => u₀ m + z (ι m)) fun m => analyticAt_const.add (analyticAt_coord _ 0))
  have hφ0 : φ 0 = (y₀, u₀) := by
    simp [φ]
  have hφψ : ∀ x, φ (ψ x) = x := by
    intro x
    refine Prod.ext (funext fun i => ?_) (funext fun m => ?_)
    · simp [φ, ψ, ψ']
    · by_cases hm : m = k
      · subst hm; simp [φ, ψ, ι]
      · simp [φ, ψ, ψ', ι, hm]
  have hψ' : AnalyticAt ℂ ψ' (y₀, fun m => u₀ m) := by
    rw [analyticAt_pi_iff]
    intro l
    cases l with
    | inl i => exact ((analyticAt_coord i _).comp analyticAt_fst).sub analyticAt_const
    | inr m => exact ((analyticAt_coord m _).comp analyticAt_snd).sub analyticAt_const
  have hψ'0 : ψ' (y₀, fun m => u₀ m) = 0 := by
    funext l; cases l <;> simp [ψ']
  have hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀) :=
    analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m) fun m =>
      (analyticAt_coord _ _).comp analyticAt_snd)
  have hψ : AnalyticAt ℂ ψ (y₀, u₀) := by
    rw [analyticAt_pi_iff]
    intro o
    cases o with
    | none => exact ((analyticAt_coord k _).comp analyticAt_snd).sub analyticAt_const
    | some l => exact (analyticAt_coord l _).comp (hψ'.comp_of_eq hπ rfl)
  have hψ0 : ψ (y₀, u₀) = 0 := by
    funext o; cases o with
    | none => simp [ψ]
    | some l => simp only [ψ, Option.elim_some]; exact congrFun hψ'0 l
  have hg : AnalyticAt ℂ (f ∘ φ) 0 := hf.comp_of_eq hφ hφ0
  obtain ⟨q, a, hq, ha, hev⟩ := h _ N c (f ∘ φ) hc_an hc0 hg
  refine ⟨q ∘ ψ, fun i x' => ∑ j, a j (ψ' x') * K' i j, hq.comp_of_eq hψ hψ0, fun i => ?_, ?_⟩
  · exact Finset.analyticAt_fun_sum _ fun j _ => ((ha j).comp_of_eq hψ' hψ'0).fun_mul analyticAt_const
  · have ht : Tendsto ψ (𝓝 (y₀, u₀)) (𝓝 0) := hψ0 ▸ hψ.continuousAt.tendsto
    filter_upwards [ht.eventually hev] with x hx
    rw [Function.comp_apply, hφψ] at hx
    rw [hx]
    have hy : (fun l => y₀ l + ψ x (some (Sum.inl l))) = x.1 := by funext l; simp [ψ, ψ']
    have hc' : ∀ i, c i (fun l => ψ x (some l)) = K₀ i + ∑ j, b j x.1 * K i j := by
      intro i; simp only [c]; rw [hy]
    have h1 := hK (fun j => b j x.1) (x.2 k - u₀ k)
    rw [sub_add_cancel] at h1
    have hn : ψ x none = x.2 k - u₀ k := rfl
    have hw : weierstrassPolynomial c (ψ x) = x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ) := by
      unfold weierstrassPolynomial
      simp only [hc', hn]
      exact h1.symm
    have hr := hK' (fun j => a j (ψ' (x.1, fun m => x.2 m))) (x.2 k)
    rw [← sub_eq_add_neg] at hr
    rw [hw, Function.comp_apply, ← hr]
    rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
