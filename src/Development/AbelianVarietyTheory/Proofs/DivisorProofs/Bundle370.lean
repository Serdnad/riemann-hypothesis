module

public import Formalism.RealPlaceAnalysis.Bundle003
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
public import GroundTheory.ProfiniteCohomology.Bundle005
public import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Mathlib.Analysis.Convolution
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

namespace GlobalTheory.CapelliNext

open Finset

variable {A : Type} [Ring A] [Algebra ℂ A]

def shiftCoeff (d : ℕ) (p q : A) (c : ℕ → A) : ℕ → A :=
  fun i => (Nat.casesOn i 0 (fun j => p * c j) : A) + (if i < d + 1 then q * c i else 0)

theorem affine_mul_eq (d : ℕ) (p q : A) (c : ℕ → A) (u : ℂ) :
    (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • shiftCoeff d p q c i := by
  unfold shiftCoeff
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

theorem prod_affine_two_top (t : ℕ) (p : Fin (t + 1) → ℂ) (q : Fin (t + 1) → A) :
    ∃ c : ℕ → A, c (t + 1) = (∏ k, p k) • (1 : A) ∧
      c t = ∑ k, (∏ j, (if j = k then (1 : ℂ) else p j)) • q k ∧
      ∀ u : ℂ, (List.ofFn fun k => (u * p k) • (1 : A) + q k).prod
        = ∑ i ∈ range (t + 1 + 1), u ^ i • c i := by
  induction t with
  | zero =>
    let c : ℕ → A := fun i => if i = 0 then q 0 else if i = 1 then (p 0) • (1 : A) else 0
    refine ⟨c, ?_, ?_, fun u => ?_⟩
    · simp [c]
    · simp [c]
    · simp [c, sum_range_succ, add_comm]
      rw [mul_smul]
  | succ t ih =>
    obtain ⟨c, hc1, hc0, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    refine ⟨shiftCoeff (t + 1) (p 0 • (1 : A)) (q 0) c, ?_, ?_, fun u => ?_⟩
    · simp only [shiftCoeff, lt_irrefl, if_false, add_zero]
      rw [hc1, smul_one_mul, smul_smul, ← Fin.prod_univ_succ]
    · simp only [shiftCoeff, lt_add_iff_pos_right, Nat.lt_add_one, if_true]
      rw [hc0, hc1, smul_one_mul, mul_smul_comm, mul_one, smul_sum, add_comm]
      conv_rhs => rw [Fin.sum_univ_succ]
      congr 1
      · simp [Fin.prod_univ_succ, smul_mul_assoc]
      · refine sum_congr rfl fun k _ => ?_
        simp [Fin.prod_univ_succ, Fin.succ_ne_zero, smul_smul, (Fin.succ_ne_zero _).symm]
    · rw [List.ofFn_succ, List.prod_cons, hc u]
      have : (u * p 0) • (1 : A) + q 0 = u • (p 0 • (1 : A)) + q 0 := by rw [smul_smul]
      rw [this, affine_mul_eq]

end GlobalTheory.CapelliNext

namespace GlobalTheory.CapelliNext
open Finset

theorem qdet_shift_next_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  intro A _ _ m E s
  have h : ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ c : ℕ → A,
      c (m + 1) = (∏ k, (if σ k = k then (1 : ℂ) else 0)) • (1 : A) ∧
      c m = ∑ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) •
        ((if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k) ∧
      ∀ u : ℂ, (List.ofFn fun k : Fin (m + 1) => Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (m + 1 + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hc1, hc0, hc⟩ := prod_affine_two_top m (fun k => if σ k = k then (1 : ℂ) else 0)
      (fun k => (if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k)
    refine ⟨c, hc1, hc0, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Formalism.REAL.Tm
    simp only [id]
    split_ifs with hk
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← add_assoc, ← add_smul]
      congr 2
      ring
    · simp
  choose c hc1 hc0 hc using h
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i,
    ∑ k : Fin (m + 1), (-s - ((k : ℕ) : ℂ)), ?_, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc1 1]
      simp
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc1 σ, Finset.prod_eq_zero (mem_univ k) (if_neg hk), zero_smul, mul_zero]
    · intro h1
      exact absurd (mem_univ _) h1
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc0 1]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
        id_eq, if_true, ite_self, prod_const_one, one_smul]
      rw [sum_add_distrib, add_comm]
      congr 1
      simp only [Algebra.algebraMap_eq_smul_one, ← sum_smul]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc0 σ]
      have hz : ∀ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) = 0 := by
        intro k
        by_cases hk : σ k = k
        · refine Finset.prod_eq_zero (mem_univ k₀) ?_
          have : k₀ ≠ k := fun e => hk₀ (e ▸ hk)
          simp [this, hk₀]
        · refine Finset.prod_eq_zero (mem_univ (σ k)) ?_
          have h2 : σ (σ k) ≠ σ k := fun e => hk (σ.injective e)
          simp [hk, h2]
      simp [hz]
    · intro h1
      exact absurd (mem_univ _) h1
  · unfold Formalism.REAL.qdet Formalism.REAL.qminor
    rw [Finset.sum_congr rfl fun σ _ => by rw [hc σ u]]
    simp_rw [mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    simp_rw [← smul_sum]

end GlobalTheory.CapelliNext
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CapelliIntertw

theorem qdet_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) :
    f (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => f (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm

  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext k
  simp only [Function.comp_apply, map_add]
  split_ifs <;> simp

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M')

def intertw : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') where
  carrier := {z | ∀ v, T (z.1 v) = z.2 (T v)}
  mul_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_mul, Prod.snd_mul, Module.End.mul_apply]
    rw [ha, hb]
  add_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add (f := _)]
    rw [ha, hb]
  algebraMap_mem' := by
    intro c v
    simp [Module.algebraMap_end_apply]

end GlobalTheory.CapelliIntertw

theorem GlobalTheory.capelli_intertw : ∀ (M M' : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M') (n : ℕ) (X : Fin n → Fin n → Module.End ℂ M) (Y : Fin n → Fin n → Module.End ℂ M'), (∀ i j v, T (X i j v) = Y i j (T v)) → ∀ (u : ℂ) (p : Polynomial ℂ) (v : M), T (Polynomial.aeval (Formalism.REAL.qdet X u) p v) = Polynomial.aeval (Formalism.REAL.qdet Y u) p (T v) := by
  intro M M' _ _ _ _ T n X Y hXY u p v
  let S := GlobalTheory.CapelliIntertw.intertw T
  let Z : Fin n → Fin n → S := fun a b => ⟨(X a b, Y a b), fun w => hXY a b w⟩
  let q : S := Polynomial.aeval (Formalism.REAL.qdet Z u) p
  have h1 : ((q : Module.End ℂ M × Module.End ℂ M').1) = Polynomial.aeval (Formalism.REAL.qdet X u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.fst ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  have h2 : ((q : Module.End ℂ M × Module.End ℂ M').2) = Polynomial.aeval (Formalism.REAL.qdet Y u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.snd ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  rw [← h1, ← h2]
  exact q.2 v
end

section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.NarrowGauss

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def gauss (c : ℝ) (hc : 0 < c) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv)
    (GroundTheory.Global.gaussianSchwartz E)

theorem gauss_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gauss c hc x = Complex.exp (-(c : ℂ) * ‖x‖ ^ 2) := by
  rw [gauss, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply]
  have h : -Real.pi * ‖(LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv x‖ ^ 2
      = -c * ‖x‖ ^ 2 := by
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (div_pos hc Real.pi_pos).le]
    field_simp
  rw [h, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem fourier_gauss (c : ℝ) (hc : 0 < c) (w : E) :
    (𝓕 (gauss (E := E) c hc) : SchwartzMap E ℂ) w = (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
      Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / c) := by
  rw [SchwartzMap.fourier_coe]
  have : (⇑(gauss c hc) : E → ℂ) = fun v ↦ Complex.exp (-(c : ℂ) * ‖v‖ ^ 2) :=
    funext (gauss_apply c hc)
  rw [this, fourier_gaussian_innerProductSpace (by simpa using hc)]

theorem fourierInv_gauss_mul_eq (f u : SchwartzMap E ℂ) (b : ℝ) (hb : 0 < b)
    (hu : ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * (𝓕 f : SchwartzMap E ℂ) y) :
    ∃ (c : ℝ) (s : ℂ), 0 < c ∧ ∀ y, (𝓕⁻ u : SchwartzMap E ℂ) y =
      s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
  set c : ℝ := Real.pi ^ 2 / b with hc_def
  have hc : 0 < c := by positivity
  set K : ℂ := (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    exact Complex.cpow_ne_zero_iff.2 (Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast hc.ne')))
  set g : SchwartzMap E ℂ := gauss c hc
  set v : SchwartzMap E ℂ := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g
  have huv : u = K⁻¹ • (𝓕 v : SchwartzMap E ℂ) := by
    ext ξ
    rw [SchwartzMap.smul_apply, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
      ContinuousLinearMap.mul_apply', fourier_gauss, ← hK, hu, smul_eq_mul]
    have e : Complex.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) = Complex.exp (-((b * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
      congr 1
      rw [hc_def]
      push_cast
      field_simp
    rw [e]
    field_simp
  refine ⟨c, K⁻¹, hc, fun y ↦ ?_⟩
  rw [huv, FourierTransform.fourierInv_smul, FourierTransform.fourierInv_fourier_eq,
    SchwartzMap.smul_apply, smul_eq_mul, SchwartzMap.convolution_apply, convolution_def]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  simp only [ContinuousLinearMap.mul_apply', g, gauss_apply]
  push_cast
  ring_nf

end GlobalTheory.NarrowGauss

open GlobalTheory.NarrowGauss in
theorem GlobalTheory.narrowGauss_convolution_dense :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  intro E _ _ _ _ _ f
  have h1 := GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E (𝓕 f : SchwartzMap E ℂ)
  have h2 := map_mem_closure (f := fun w : SchwartzMap E ℂ ↦ (𝓕⁻ w : SchwartzMap E ℂ))
    (t := {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))})
    FourierTransform.continuous_fourierInv h1 (fun u hu ↦ by
      obtain ⟨b, hb, hu⟩ := hu
      exact fourierInv_gauss_mul_eq f u b hb hu)
  simpa [FourierTransform.fourierInv_fourier_eq] using h2
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.HomogCochains

open GroundTheory.ProfCoh groupCohomology

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Rep.{0} k G} [IsDiscreteRep M] {C : CosimplicialObject AddCommGrpCat.{1}}
  {e : ∀ m : ℕ, C.obj ⦋m⦌ →+ ((Fin (m + 1) → G) → M)}

theorem neg_one_pow_smul_eq (m : ℕ) (x : M) : ((-1 : k) ^ m) • x = ((-1 : ℤ) ^ m) • x := by
  rw [← Int.cast_smul_eq_zsmul k]
  simp

section
variable (he : ∀ m, Function.Injective (e m))
  (hr : ∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔
    IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i => τ * σ i) = M.ρ τ (φ σ))
  (hd : ∀ m (i : Fin (m + 2)) (c : C.obj ⦋m⦌) (σ : Fin (m + 2) → G),
    e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove))

include hr in
theorem isLocallyConstant_e (m : ℕ) (c : C.obj ⦋m⦌) : IsLocallyConstant (e m c) :=
  ((hr m (e m c)).1 ⟨c, rfl⟩).1

include hr in
theorem e_mul (m : ℕ) (c : C.obj ⦋m⦌) (τ : G) (σ : Fin (m + 1) → G) :
    e m c (fun i => τ * σ i) = M.ρ τ (e m c σ) :=
  ((hr m (e m c)).1 ⟨c, rfl⟩).2 τ σ

def toInh (m : ℕ) : C.obj ⦋m⦌ →+ locallyConstantCochains M m where
  toFun c := ⟨fun g => e m c (Fin.partialProd g),
    (isLocallyConstant_e hr m c).comp_continuous (continuous_partialProd m)⟩
  map_zero' := by ext g; simp
  map_add' a b := by ext g; simp

theorem toInh_apply (m : ℕ) (c : C.obj ⦋m⦌) (g : Fin m → G) :
    ((toInh hr m c : locallyConstantCochains M m) : (Fin m → G) → M) g = e m c (Fin.partialProd g) :=
  rfl

include he in
theorem toInh_bijective (m : ℕ) : Function.Bijective (toInh hr m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    apply he m
    rw [map_zero]
    funext σ
    have h0 : ∀ g, e m c (Fin.partialProd g) = 0 := fun g => by
      have := congrArg (fun f : locallyConstantCochains M m => (f : (Fin m → G) → M) g) hc
      simpa [toInh_apply] using this
    have hσ : σ = fun i => σ 0 * Fin.partialProd (fun j => (σ (Fin.castSucc j))⁻¹ * σ j.succ) i := by
      have := Fin.partialProd_left_inv σ
      funext i
      conv_lhs => rw [← this]
      rfl
    rw [hσ, e_mul hr, h0, map_zero]
    rfl
  · intro φ
    let F : (Fin (m + 1) → G) → M := fun x => M.ρ (x 0) (φ.1 fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)
    have hF : IsLocallyConstant F :=
      isLocallyConstant_ρ_apply M (continuous_apply 0)
        (φ.2.comp_continuous (continuous_pi fun _ =>
          ((continuous_apply _).inv).mul (continuous_apply _)))
    have hFm : ∀ (τ : G) (σ : Fin (m + 1) → G), F (fun i => τ * σ i) = M.ρ τ (F σ) := by
      intro τ σ
      simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
      rfl
    obtain ⟨c, hc⟩ := (hr m F).2 ⟨hF, hFm⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    funext g
    rw [toInh_apply, hc]
    simp only [F, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
    rfl

theorem sum_hom_apply {X Y : AddCommGrpCat.{1}} {ι : Type} (s : Finset ι) (f : ι → (X ⟶ Y)) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

theorem zsmul_hom_apply {X Y : AddCommGrpCat.{1}} (n : ℤ) (f : X ⟶ Y) (x : X) :
    (n • f) x = n • f x := by
  change (n • f).hom x = _
  rw [AddCommGrpCat.hom_zsmul]
  rfl

include hd hr in
theorem toInh_d (n : ℕ) (c : C.obj ⦋n⦌) :
    toInh hr (n + 1) ((AlgebraicTopology.AlternatingCofaceMapComplex.objD C n) c) =
      (dLocallyConstant M n).hom (toInh hr n c) := by
  apply Subtype.ext
  funext g
  rw [toInh_apply, dLocallyConstant_hom_apply, inhomogeneousCochains.d_hom_apply]

  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, sum_hom_apply, zsmul_hom_apply,
  map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply, hd]
  rw [Fin.sum_univ_succ]
  congr 1
  · have : (Fin.partialProd g ∘ (0 : Fin (n + 2)).succAbove) =
        fun j => g 0 * Fin.partialProd (Fin.tail g) j := by
      funext j
      simp only [Function.comp_apply, Fin.succAbove_zero]
      exact Fin.partialProd_succ' g j
    rw [this, e_mul hr, Fin.val_zero, pow_zero, one_smul, toInh_apply]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [toInh_apply, Fin.partialProd_contractNth, Fin.val_succ, neg_one_pow_smul_eq]

abbrev upF (k : Type) [CommRing k] : ModuleCat.{0} k ⥤ AddCommGrpCat.{1} :=
  forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0} ⋙ AddCommGrpCat.uliftFunctor.{1, 0}

theorem alt_d (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD C n := by
  simp [AlgebraicTopology.alternatingCofaceMapComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj]


include he hr hd in
noncomputable def complexIso :
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C ≅
      ((upF k).mapHomologicalComplex _).obj (cochainsComplex M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (((AddEquiv.ofBijective (toInh hr n) (toInh_bijective he hr n)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso :
        (C.obj ⦋n⦌ : AddCommGrpCat.{1}) ≅ (upF k).obj (ModuleCat.of k (locallyConstantCochains M n))))
    (by
      rintro i j (rfl : i + 1 = j)
      rw [alt_d, Functor.mapHomologicalComplex_obj_d, cochainsComplex_d]
      ext c
      apply ULift.ext
      exact (toInh_d hr hd i c).symm)

end

end GlobalTheory.HomogCochains

open GlobalTheory.HomogCochains in
theorem GlobalTheory.homogeneousCochains_homology_addEquiv : ∀ (k : Type) [CommRing k] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{0} k G) [GroundTheory.ProfCoh.IsDiscreteRep M] (C : CosimplicialObject AddCommGrpCat.{1}) (e : ∀ m : ℕ, C.obj ⦋m⦌ →+ ((Fin (m + 1) → G) → M)), (∀ m, Function.Injective (e m)) → (∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔ IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i => τ * σ i) = M.ρ τ (φ σ)) → (∀ m (i : Fin (m + 2)) (c : C.obj ⦋m⦌) (σ : Fin (m + 2) → G), e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove)) → ∀ n : ℕ, Nonempty (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).homology n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  intro k _ G _ _ _ M _ C e he hr hd n
  let i1 := (HomologicalComplex.homologyFunctor AddCommGrpCat.{1} _ n).mapIso (complexIso he hr hd)
  let i2 : (((upF k).mapHomologicalComplex _).obj (GroundTheory.ProfCoh.cochainsComplex M)).homology n ≅
      (upF k).obj ((GroundTheory.ProfCoh.cochainsComplex M).homology n) :=
    ((GroundTheory.ProfCoh.cochainsComplex M).sc n).mapHomologyIso (upF k)
  exact ⟨(i1 ≪≫ i2).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift⟩
end
