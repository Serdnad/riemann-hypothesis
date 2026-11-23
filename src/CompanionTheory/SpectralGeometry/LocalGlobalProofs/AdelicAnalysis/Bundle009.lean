module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle002
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle004
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle003
public import Mathlib.MeasureTheory.Measure.WithDensity
public import CompanionTheory.AutomorphicTheory.ThetaDilations.Nuabs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Fourier.FourierTransform
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.RingDiag

open HeckeCharacterZeroLocus.SiegelWeilU

variable {A : Type} [CommRing A] {m : ℕ}

def bd (a : A) (M : Matrix (Fin m) (Fin m) A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  fun i j => Fin.cases (Fin.cases a (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => M i' j') j) i

@[simp] lemma bd_succ_zero (a : A) (M : Matrix (Fin m) (Fin m) A) (i : Fin m) :
    bd a M i.succ 0 = 0 := rfl
@[simp] lemma bd_succ_succ (a : A) (M : Matrix (Fin m) (Fin m) A) (i j : Fin m) :
    bd a M i.succ j.succ = M i j := rfl

lemma bd_mul (a b : A) (M N : Matrix (Fin m) (Fin m) A) :
    bd a M * bd b N = bd (a * b) (M * N) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [bd, Matrix.mul_apply, Fin.sum_univ_succ]

lemma det_bd (a : A) (M : Matrix (Fin m) (Fin m) A) : (bd a M).det = a * M.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have : (bd a M).submatrix Fin.succ Fin.succ = M := by
    ext i j; simp
  simp [bd, this]

lemma cT_bd (σ : A →+* A) (a : A) (M : Matrix (Fin m) (Fin m) A) :
    cT σ (bd a M) = bd (σ a) (cT σ M) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [bd, cT]

lemma bd_diagonal (a : A) (d : Fin m → A) :
    bd a (Matrix.diagonal d) = Matrix.diagonal (Fin.cons a d : Fin (m + 1) → A) := by
  have h0 : ∀ j' : Fin m, (0 : Fin (m + 1)) ≠ j'.succ := fun j' => (Fin.succ_ne_zero j').symm
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [bd, Matrix.diagonal_apply, h0]

def uni (r : Fin m → A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  fun i j => Fin.cases (Fin.cases 1 r j)
    (fun i' => Fin.cases 0 (fun j' => (1 : Matrix (Fin m) (Fin m) A) i' j') j) i

lemma det_uni (r : Fin m → A) : (uni r).det = 1 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have : (uni r).submatrix Fin.succ Fin.succ = 1 := by
    ext i j; simp [uni, Matrix.one_apply]
  simp [uni, this]

def schur (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (b : A) : Matrix (Fin m) (Fin m) A :=
  fun i j => K i.succ j.succ - K i.succ 0 * b * K 0 j.succ

lemma mul_uni (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (r : Fin m → A) (i : Fin (m + 1)) :
    (K * uni r) i 0 = K i 0 ∧ ∀ j : Fin m, (K * uni r) i j.succ = K i j.succ + K i 0 * r j := by
  constructor
  · simp [uni, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  · intro j
    simp [uni, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, add_comm]

lemma cT_uni_mul (σ : A →+* A) (P : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (r : Fin m → A)
    (j : Fin (m + 1)) :
    (cT σ (uni r) * P) 0 j = P 0 j ∧
      ∀ i : Fin m, (cT σ (uni r) * P) i.succ j = P i.succ j + σ (r i) * P 0 j := by
  constructor
  · simp [uni, cT, Matrix.mul_apply, Fin.sum_univ_succ]
  · intro i
    simp [uni, cT, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, add_comm,
      apply_ite σ]

lemma schur_step (σ : A →+* A) (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hK : ∀ i j, σ (K j i) = K i j) (b : A) (hb : b * K 0 0 = 1) (hσb : σ b = b) :
    cT σ (uni fun j => -(b * K 0 j.succ)) * K * (uni fun j => -(b * K 0 j.succ)) =
      bd (K 0 0) (schur K b) := by
  set r : Fin m → A := fun j => -(b * K 0 j.succ) with hr
  have hσr : ∀ i, σ (r i) = -(b * K i.succ 0) := by
    intro i; simp [hr, hσb, hK]
  have hzero : ∀ j : Fin m, K 0 j.succ + K 0 0 * r j = 0 := by
    intro j
    have : K 0 0 * r j = -((b * K 0 0) * K 0 j.succ) := by simp only [hr]; ring
    rw [this, hb]; ring
  rw [Matrix.mul_assoc]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rw [(cT_uni_mul σ _ r 0).1, (mul_uni K r 0).1]
    change K 0 0 = K 0 0
    rfl
  · rw [(cT_uni_mul σ _ r _).1, (mul_uni K r 0).2, hzero]
    change 0 = 0
    rfl
  · rw [(cT_uni_mul σ _ r 0).2, (mul_uni K r _).1, (mul_uni K r 0).1, hσr]
    simp only [bd_succ_zero]
    have : b * K i'.succ 0 * K 0 0 = (b * K 0 0) * K i'.succ 0 := by ring
    rw [neg_mul, this, hb]; ring
  · rw [(cT_uni_mul σ _ r _).2, (mul_uni K r _).2, (mul_uni K r 0).2, hzero, hσr]
    simp only [bd_succ_succ, schur, hr]; ring

lemma det_cT (σ : A →+* A) (g : Matrix (Fin m) (Fin m) A) : (cT σ g).det = σ g.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl

lemma cT_cT (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) {p q : Type}
    (M : Matrix p q A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

lemma cT_congr_herm (σ : A →+* A) {n : ℕ} (hσ : ∀ y, σ (σ y) = y)
    (J g : Matrix (Fin n) (Fin n) A) (hJ : ∀ i j, σ (J j i) = J i j) :
    ∀ i j, σ ((cT σ g * J * g) j i) = (cT σ g * J * g) i j := by
  have hJ' : cT σ J = J := by ext i j; exact hJ i j
  have : cT σ (cT σ g * J * g) = cT σ g * J * g := by
    rw [cT_mul, cT_mul, cT_cT σ hσ, hJ', Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun this i) j

lemma corner (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (x : Fin (n + 1) → A) (hg : ∀ i, g i 0 = x i) :
    (cT σ g * J * g) 0 0 = hform σ J x x := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, hg, hform,
    Finset.sum_mul]
  exact Finset.sum_comm

lemma unimodular (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (x : Fin n → A) (b : A)
    (hb : b * hform σ J x x = 1) : ∃ c : Fin n → A, ∑ i, c i * x i = 1 := by
  refine ⟨fun j => b * ∑ i, σ (x i) * J i j, ?_⟩
  rw [← hb, hform, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (b * ∑ i : Fin n, σ (x i) * J i j) * x j = b * ∑ i : Fin n, σ (x i) * J i j * x j
  rw [mul_assoc, Finset.sum_mul]

theorem diagonalise : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → (∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x)) → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ (g : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit g.det ∧ (∀ i, IsUnit (d i) ∧ σ (d i) = d i) ∧ HeckeCharacterZeroLocus.SiegelWeilU.cT σ g * J * g = Matrix.diagonal d := by
  intro A _ _ σ hσ H m
  induction m with
  | zero =>
    intro J _ _
    exact ⟨1, Fin.elim0, by simp, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ m ih =>
    intro J hJ hdet
    obtain ⟨x, hx⟩ := H m J hJ hdet
    obtain ⟨b, hb⟩ := hx.exists_left_inv
    obtain ⟨g₀, hg₀, hcol⟩ := GlobalTheory.CompanionTheory.SW.SemilocalColumn.exists_invertible_first_column A m x (unimodular σ J x b hb)
    set K := cT σ g₀ * J * g₀ with hKdef
    have hK : ∀ i j, σ (K j i) = K i j := cT_congr_herm σ hσ J g₀ hJ
    have hcorner : K 0 0 = hform σ J x x := corner σ J g₀ x hcol
    have hbK : b * K 0 0 = 1 := by rw [hcorner]; exact hb
    have hβ : IsUnit (K 0 0) := by rw [hcorner]; exact hx
    have hσβ : σ (K 0 0) = K 0 0 := hK 0 0
    have hσb : σ b = b := by
      have h1 : σ b * K 0 0 = 1 := by
        have := congrArg σ hbK
        rwa [map_mul, hσβ, map_one] at this
      calc σ b = σ b * (K 0 0 * b) := by rw [mul_comm (K 0 0), hbK, mul_one]
        _ = (σ b * K 0 0) * b := by ring
        _ = b := by rw [h1, one_mul]
    set r : Fin m → A := fun j => -(b * K 0 j.succ) with hr
    have hstep := schur_step σ K hK b hbK hσb
    have hKdet : IsUnit K.det := by
      rw [hKdef, Matrix.det_mul, Matrix.det_mul, det_cT]
      exact ((hg₀.map σ).mul hdet).mul hg₀
    have hJ₁det : IsUnit (schur K b).det := by
      have h2 : (K 0 0) * (schur K b).det = K.det := by
        rw [← det_bd, ← hstep, Matrix.det_mul, Matrix.det_mul, det_cT, det_uni]; simp
      rw [← h2] at hKdet
      exact isUnit_of_mul_isUnit_right hKdet
    have hJ₁ : ∀ i j, σ (schur K b j i) = schur K b i j := by
      intro i j
      simp only [schur, map_sub, map_mul, hσb, hK]
      ring
    obtain ⟨g₁, d₁, hg₁, hd₁, hdiag⟩ := ih (schur K b) hJ₁ hJ₁det
    refine ⟨g₀ * uni r * bd 1 g₁, Fin.cons (K 0 0) d₁, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, det_uni, det_bd]
      simpa using hg₀.mul hg₁
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa using ⟨hβ, hσβ⟩
      · simpa using hd₁ i'
    · have e : cT σ (g₀ * uni r * bd 1 g₁) * J * (g₀ * uni r * bd 1 g₁) =
          cT σ (bd 1 g₁) * (cT σ (uni r) * K * uni r) * bd 1 g₁ := by
        rw [hKdef, cT_mul, cT_mul]
        simp only [Matrix.mul_assoc]
      rw [e, hstep, cT_bd, bd_mul, bd_mul, hdiag, map_one, one_mul, mul_one, bd_diagonal]

end GlobalTheory.CompanionTheory.SW.RingDiag
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RealFourier

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem fourierChar_smul (t : ℝ) (c : ℂ) :
    (Real.fourierChar t : Circle) • c = c * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

theorem inversion_neg (ι : Type) [Fintype ι] (Φ : (ι → ℝ) → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ)
    (hi : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ,
      Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume)
    (z : ι → ℝ) :
    ∫ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) *
      Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (y ⬝ᵥ z) : ℝ) : ℝ)) = Φ (-z) := by
  have mp := PiLp.volume_preserving_toLp ι
  have emb : MeasurableEmbedding (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  have hin : ∀ x y : ι → ℝ, inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (WithLp.toLp 2 y)
      = x ⬝ᵥ y := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  set Ψ : EuclideanSpace ℝ ι → ℂ := fun u => Φ u.ofLp with hΨ
  have hΨc : Continuous Ψ := hc.comp (PiLp.continuous_ofLp 2 _)
  have hΨi : Integrable Ψ volume :=
    (mp.integrable_comp_emb emb).1 (hc.integrable_of_hasCompactSupport hs)
  have hF : ∀ y : ι → ℝ, FourierTransform.fourier Ψ (WithLp.toLp 2 y) = ∫ x : ι → ℝ,
      Φ x * Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
    intro y
    rw [Real.fourier_eq, ← mp.integral_comp emb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hin, fourierChar_smul, hΨ]
    simp
  have hFi : Integrable (FourierTransform.fourier Ψ) volume := by
    refine (mp.integrable_comp_emb emb).1 ?_
    refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
    exact (hF y).symm
  have hinv := congrFun (hΨc.fourierInv_fourier_eq hΨi hFi) (WithLp.toLp 2 (-z))
  rw [Real.fourierInv_eq, ← mp.integral_comp emb] at hinv
  have hval : Ψ (WithLp.toLp 2 (-z)) = Φ (-z) := rfl
  rw [← hval, ← hinv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hin, fourierChar_smul, hF]
  simp

end GlobalTheory.CompanionTheory.SW.RealFourier

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem selfDual_real_coord : ∀ (ι : Type) [Fintype ι] (ε : ℝ), ε = 1 ∨ ε = -1 →
    SelfDual (volume : Measure (ι → ℝ))
      (fun x y => Complex.exp (2 * Real.pi * Complex.I * (ε * (x ⬝ᵥ y) : ℝ))) := by
  intro ι _ ε hε
  refine ⟨inferInstance, fun Φ hc hs hi z => ?_⟩
  rcases hε with rfl | rfl
  ·
    have hG : ∀ y : ι → ℝ, (∫ x : ι → ℝ,
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) =
        ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
          Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ)) := by
      intro y
      rw [← integral_neg_eq_self (fun x : ι → ℝ =>
        Φ x * Complex.exp (2 * Real.pi * Complex.I * (((1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    have hc' : Continuous fun u : ι → ℝ => Φ (-u) := hc.comp continuous_neg
    have hs' : HasCompactSupport fun u : ι → ℝ => Φ (-u) :=
      hs.comp_homeomorph (Homeomorph.neg (ι → ℝ))
    have hi' : Integrable (fun y : ι → ℝ => ∫ x : ι → ℝ, (fun u => Φ (-u)) x *
        Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℝ))) volume :=
      hi.congr (Filter.Eventually.of_forall hG)
    have key := RealFourier.inversion_neg ι (fun u => Φ (-u)) hc' hs' hi' (-z)
    simp only [neg_neg] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hG y]
    simp
  · exact RealFourier.inversion_neg ι Φ hc hs hi z

end GlobalTheory.CompanionTheory.SW
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.Packing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]

def Sep (e : Λ →+ V) (r R : ℝ) (s : Finset Λ) : Prop :=
  (∀ l ∈ s, ‖e l‖ ≤ R) ∧ (s : Set Λ).Pairwise fun a b => r ≤ ‖e a - e b‖

theorem Sep.card_le {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s : Finset Λ}
    (hs : Sep e r R s) : (s.card : ℝ) ≤ (3 * R / r) ^ Module.finrank ℝ V := by
  classical
  have hinj : Set.InjOn e (s : Set Λ) := by
    intro a ha b hb hab
    by_contra hne
    have : r ≤ ‖e a - e b‖ := hs.2 ha hb hne
    rw [hab, sub_self, norm_zero] at this
    linarith
  have hcard : (s.image e).card = s.card := Finset.card_image_of_injOn hinj
  have h1 := GlobalTheory.finset_card_le_of_separated (s.image e) hr (hr.le.trans hrR) (0 : V)
    (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
      simpa using hs.1 l hl)
    (by
      intro a ha b hb hab
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      have hlm : l ≠ m := fun h => hab (by rw [h])
      rw [dist_eq_norm]
      exact hs.2 hl hm hlm)
  rw [hcard] at h1
  exact h1.trans (GlobalTheory.one_add_two_mul_div_pow_le hr hrR _)

theorem exists_max_sep (e : Λ →+ V) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ s : Finset Λ, Sep e r R s ∧ ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card := by
  let S : Set ℕ := {n | ∃ s : Finset Λ, Sep e r R s ∧ s.card = n}
  have hne : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbd : BddAbove S := by
    refine ⟨⌊(3 * R / r) ^ Module.finrank ℝ V⌋₊, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact Nat.le_floor (Sep.card_le hr hrR hs)
  obtain ⟨s, hs, hc⟩ := Nat.sSup_mem hne hbd
  exact ⟨s, hs, fun t ht => hc ▸ le_csSup hbd ⟨t, ht, rfl⟩⟩

theorem Sep.exists_near {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) {s : Finset Λ}
    (hs : Sep e r R s) (hmax : ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card)
    {l : Λ} (hl : ‖e l‖ ≤ R) : ∃ t ∈ s, ‖e (l - t)‖ ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  have hns : l ∉ s := fun h => by
    have := hcon l h
    simp only [sub_self, map_zero, norm_zero] at this
    linarith
  have hins : Sep e r R (insert l s) := by
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hl
      · exact hs.1 m hm
    · rw [Finset.coe_insert]
      refine Set.pairwise_insert.2 ⟨hs.2, ?_⟩
      intro b hb _
      have h := hcon b hb
      rw [map_sub] at h
      exact ⟨h.le, by rw [norm_sub_rev]; exact h.le⟩
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem hns] at this
  omega

end GlobalTheory.CompanionTheory.Adelic.Packing


open GlobalTheory.CompanionTheory.Adelic.Packing in
theorem GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type)
      [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
        ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) *
          ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  intro V _ _ _ Λ _ e r R hr hrR
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_sep e hr hrR
  set f : Λ → ℝ≥0∞ := Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) with hf
  have hpt : ∀ l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
      ∑ t ∈ s, f (l - t) := by
    intro l
    by_cases hl : ‖e l‖ ≤ R
    · obtain ⟨t, ht, hlt⟩ := hs.exists_near hr hmax hl
      have h1 : f (l - t) = 1 := Set.indicator_of_mem (s := {l : Λ | ‖e l‖ ≤ r}) hlt _
      calc Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ 1 :=
            Set.indicator_le_self' (fun _ _ => zero_le) l
        _ = f (l - t) := h1.symm
        _ ≤ ∑ t ∈ s, f (l - t) :=
            Finset.single_le_sum (f := fun t => f (l - t)) (fun _ _ => zero_le) ht
    · rw [Set.indicator_of_notMem (by simpa using hl)]
      exact zero_le
  have hshift : ∀ t : Λ, ∑' l : Λ, f (l - t) = ∑' l : Λ, f l := fun t =>
    (Equiv.subRight t).tsum_eq f
  have hcard : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) := by
    have h3 : (s.card : ℝ) ≤ (5 * R / r) ^ Module.finrank ℝ V := by
      refine (Sep.card_le hr hrR hs).trans (pow_le_pow_left₀ (by have := hr.le.trans hrR; positivity) ?_ _)
      have := hr.le.trans hrR
      gcongr
      norm_num
    calc (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3
  calc ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l
      ≤ ∑' l : Λ, ∑ t ∈ s, f (l - t) := ENNReal.tsum_le_tsum hpt
    _ = ∑ t ∈ s, ∑' l : Λ, f (l - t) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = (s.card : ℝ≥0∞) * ∑' l : Λ, f l := by
        simp only [hshift, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B → ContinuousOn D' B → (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) → ∀ b ∈ B, D b = D' b := by
  first | exact @GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | exact GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | (intros; apply GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem tripleProduct_map_leftInvariant : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  exact CompanionTheory.PlacePermOperatorBicommutantSpan.nuabs

end GlobalTheory.CompanionTheory.Adelic
end
