module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Formalism.LocalToGlobal.Divisibility.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016

@[expose] public section

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

namespace GlobalTheory.RealLift.SpLie

open Matrix

def sgnD {p q : ℕ} : Ix p q → ℂ
  | .inl _ => 1
  | .inr _ => -1

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal sgnD := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, sgnD, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem lineSign_eq_mul {p q r s : ℕ} (a : Ix p q) (b : Ix r s) : lineSign a b = sgnD a * sgnD b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign, sgnD]

theorem upq_entry {r s : ℕ} {Y : Mat r s} (hY : Y ∈ upq r s) (b k : Ix r s) :
    star (Y k b) * sgnD k + sgnD b * Y b k = 0 := by
  have h : (Yᴴ * Jm r s + Jm r s * Y) b k = 0 := by
    rw [show Yᴴ * Jm r s + Jm r s * Y = 0 from hY]; rfl
  rw [Jm_eq_diagonal] at h
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h

theorem sympl_eq_dot {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
  simp only [mul_comm (v _)]
  ring

theorem sum_zero {P Q R S : ℕ} (c c' : Matrix (Ix P Q) (Ix R S) ℂ) (Y : Mat R S) (hY : Y ∈ upq R S) :
    (∑ a, ∑ b, lineSign a b * (c * Yᵀ) a b * star (c' a b)) +
      ∑ a, ∑ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) = 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  have e1 : ∀ b, lineSign a b * (c * Yᵀ) a b * star (c' a b) =
      ∑ k, sgnD a * c a k * star (c' a b) * (sgnD b * Y b k) := by
    intro b
    rw [lineSign_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply]; ring
  have e2 : ∀ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) =
      ∑ k, sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k)) := by
    intro b
    rw [lineSign_eq_mul, Matrix.mul_apply, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply, star_mul']; ring
  simp only [e1, e2]
  rw [Finset.sum_comm (f := fun b k => sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k))),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  linear_combination (sgnD a * c a k * star (c' a b)) * upq_entry hY b k

theorem mem_sp_of_sympl {l : Type} [Fintype l] [DecidableEq l] (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (Z *ᵥ u) v + sympl u (Z *ᵥ v) = 0) : Z ∈ LieAlgebra.Symplectic.sp l ℝ := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  show Zᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -Z
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_dot, sympl_eq_dot] at h1
  simp [mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply] at h1 ⊢
  linarith

theorem exists_sp_rightAct : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ Y hY
  let G : (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) :=
    { toFun := fun c w => c w * (Y w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef
  have hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ := by
    intro c; rw [hZdef, LinearMap.toMatrix'_mulVec]; simp [G]
  refine ⟨Z, ?_, hZ, ?_⟩
  · refine mem_sp_of_sympl Z fun u v => ?_
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    have hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) +
        (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)
    rw [hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]
    simp only [hs, Complex.zero_im, mul_zero]
  · intro t c
    have hpow : ∀ (n : ℕ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ),
        (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]
        have : (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ := by
          funext w; simp [Matrix.transpose_smul, Matrix.mul_smul]
        rw [this, ih]
        congr 1; funext w
        rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]
    letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
    letI : NormedRing (Mat R S) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Mat R S) := Matrix.linftyOpNormedAlgebra
    have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c)
        (NormedSpace.exp (t • Z) *ᵥ φ c) :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map
        (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)
    have hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ)
        (c w * (NormedSpace.exp (t • Y w))ᵀ) := by
      intro w
      have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose
      exact this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _)
        (continuous_const.matrix_mul continuous_id)
    have h2 := (Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)
    refine h1.unique ?_
    convert h2 using 1
    funext n
    rw [Matrix.smul_mulVec, hpow, ← φ.map_smul]
    congr 1; funext w
    simp [Matrix.transpose_smul, Matrix.mul_smul]

end GlobalTheory.RealLift.SpLie
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.ColAction

theorem sympl_eq_neg_dotProduct {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, Finset.sum_neg_distrib, mul_comm]
  ring

theorem mem_symplecticGroup_of_sympl {l : Type} [Fintype l] [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (M *ᵥ u) (M *ᵥ v) = sympl u v) : M ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  ext a b
  have key : ∀ u v, (M *ᵥ u) ⬝ᵥ (Matrix.J l ℝ *ᵥ (M *ᵥ v)) = u ⬝ᵥ ((Mᵀ * Matrix.J l ℝ * M) *ᵥ v) := by
    intro u v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ, Matrix.vecMul_transpose]
  have := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_neg_dotProduct, sympl_eq_neg_dotProduct, neg_inj, key] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem signed_sum_eq_trace {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) :
    ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) = Matrix.trace (Jm P Q * X * Jm R S * Yᴴ) := by
  have e : Jm P Q * X * Jm R S =
      Matrix.of fun a b => ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) a * X a b * ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) b := by
    ext a b
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [Fintype.sum_sum_type, lineSign]

theorem signed_sum_mul_transpose {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) (k : Mat R S)
    (hk : kᴴ * Jm R S * k = Jm R S) :
    ∑ a, ∑ b, lineSign a b * (X * kᵀ) a b * star ((Y * kᵀ) a b) = ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) := by
  have hJ : (Jm R S)ᵀ = Jm R S := by
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal]
  have e : (kᵀ)ᴴ = k.map star := by ext i j; simp
  have hk' : kᵀ * Jm R S * (kᵀ)ᴴ = Jm R S := by
    have := congrArg Matrix.transpose hk
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.conjTranspose_transpose] at this
    rw [e, Matrix.mul_assoc, this]
  rw [signed_sum_eq_trace, signed_sum_eq_trace, Matrix.conjTranspose_mul]
  congr 1
  calc Jm P Q * (X * kᵀ) * Jm R S * ((kᵀ)ᴴ * Yᴴ) = Jm P Q * X * (kᵀ * Jm R S * (kᵀ)ᴴ) * Yᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hk']

theorem exists_symplectic_hom_of_unitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ
  let A : G → (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) := fun g =>
    { toFun := fun c w => c w * (k g w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  let T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ) := fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap
  have hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ) := fun g c => by simp [T, A]
  have hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v := by
    intro g u v
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    rw [hT, hT, hφ, hφ]
    simp only [signed_sum_mul_transpose _ _ _ (hkJ g _)]
  have hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ := fun g =>
    mem_symplecticGroup_of_sympl _ (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)
  have hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h := by
    intro g h
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    show T (g * h) (φ c) = T g (T h (φ c))
    rw [hT, hT, hT]
    congr 1
    ext w : 1
    simp [map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    rw [hT]
    simp
  let s : G →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩
      map_one' := by
        apply Subtype.ext
        simp only [hT1, LinearMap.toMatrix'_id]
        rfl
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [hTmul, LinearMap.toMatrix'_comp]
        rfl }
  refine ⟨s, ?_, fun g c => ?_⟩
  · apply Continuous.subtype_mk
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a := by
      intro g
      rw [LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]
    simp only [e]
    exact (continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))
  · show LinearMap.toMatrix' (T g) *ᵥ φ c = _
    rw [LinearMap.toMatrix'_mulVec, hT]

end GlobalTheory.ColAction
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.VacuumWeight

theorem diagonal_eq_sum_Eab {r s : ℕ} (D : Ix r s → ℂ) :
    Matrix.diagonal D = ∑ c, D c • Eab c c := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eab, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; symm
    exact Finset.sum_eq_zero fun c _ => if_neg fun hc => h (hc.1.symm.trans hc.2)

theorem sum_lineSign {p q r s : ℕ} (c : Ix r s) :
    ∑ a : Ix p q, lineSign a c = ((p : ℂ) - q) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c := by
  rcases c with c | c <;> simp [Fintype.sum_sum_type, lineSign] <;> ring

theorem fockAct2_diagonal_one (p q r s : ℕ) (D : Ix r s → ℂ) :
    fockAct2 p q r s (Matrix.diagonal D) (1 : Formalism.BasicNotions.TH.Pol p q r s) =
    ((((p : ℂ) - q) / 2) * ∑ c, D c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c) • (1 : Formalism.BasicNotions.TH.Pol p q r s) := by
  have h1 : (1 : Formalism.BasicNotions.TH.Pol p q r s) = MvPolynomial.monomial 0 1 := rfl

  rw [diagonal_eq_sum_Eab, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, LinearMap.smul_apply, h1, cartan2, smul_smul]
  congr 1
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add]
  rw [← Finset.sum_mul, sum_lineSign]
  ring

end GlobalTheory.VacuumWeight
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock

variable {V : Type} [AddCommGroup V] [Module ℂ V]

open scoped IsMulCommutative in
def polEval {ι : Type} (m : ι → Module.End ℂ V) (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) :
    MvPolynomial ι ℂ →ₗ[ℂ] V :=
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range m)) :=
    Algebra.isMulCommutative_adjoin ℂ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hm i j)
  (LinearMap.applyₗ f₀ ∘ₗ (Algebra.adjoin ℂ (Set.range m)).val.toLinearMap) ∘ₗ
    (MvPolynomial.aeval (fun i => (⟨m i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range m)))).toLinearMap

def polMap (W Λ : Type) [Fintype W] [DecidableEq W] :
    (⨂[ℂ] _ : W, MvPolynomial Λ ℂ) →ₗ[ℂ] MvPolynomial (W × Λ) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (W × Λ) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Prod.mk w)).toLinearMap)

def unitAt {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    W → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

def fockM {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))

def fockD {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I)))

def coefM (z ε : ℂ) : ℂ := (z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

def coefD (z ε : ℂ) : ℂ := -(z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

end GlobalTheory.CCRFock
end
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

def chiOne (P Q R S : ℕ) (x : ℚ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ X : {X : Mat P Q // IsKC X}, LinearMap.ker (fockAct1 P Q R S X.1 - ((x : ℂ) * X.1.trace) • 1)

theorem mem_chiOne {P Q R S : ℕ} (x : ℚ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ chiOne P Q R S x ↔ ∀ X : Mat P Q, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f := by
  simp only [chiOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

def lowOne (P Q R S : ℕ) (x : ℚ) (d : ℕ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  chiOne P Q R S x ⊓ MvPolynomial.restrictTotalDegree (Ln P Q R S) ℂ d

theorem mem_lowOne {P Q R S : ℕ} (x : ℚ) (d : ℕ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ lowOne P Q R S x d ↔ f ∈ chiOne P Q R S x ∧ f.totalDegree ≤ d := by
  rw [lowOne, Submodule.mem_inf, MvPolynomial.mem_restrictTotalDegree]

def tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V) :
    Submodule ℂ (⨂[ℂ] _ : ι, V) :=
  Submodule.span ℂ {T | ∃ f : ι → V, (∀ w, f w ∈ H w) ∧ T = PiTensorProduct.tprod ℂ f}

theorem tprod_mem_tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V)
    (f : ι → V) (hf : ∀ w, f w ∈ H w) : PiTensorProduct.tprod ℂ f ∈ tensSpan H :=
  Submodule.subset_span ⟨f, hf, rfl⟩

end GlobalTheory.KFixIrr

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem tprod_one_pol_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  intro F _ _ P Q R S h
  let c : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ := (MvPolynomial.aeval (fun _ => (0:ℂ))).toLinearMap
  have key := congrArg (PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ (InfinitePlace F) ℂ).compLinearMap (fun _ => c))) h
  simp [PiTensorProduct.lift.tprod, c] at key

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobOrbit

theorem hasDerivAt_sobCont_orbit : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π ℓ → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, HasDerivAt (fun t : ℝ => ℓ (π (NormedSpace.exp (t • X)) v)) (ℓ (dRep π X v)) 0 :=
  fun _ _ _ _ _ _ _ hu hπ _ hv _ hℓ _ hX =>
    (GlobalTheory.UnitarySmVec.smFam_orbit hu hπ hv hX).hasDerivAt_form hu hπ hℓ

end GlobalTheory.SobOrbit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.nonempty_finite_type_index_of_rows_pos : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3), A3.fam3.Ok3 s → Zs.InBlock → (A3.side3 P ψ Zs).Pos → Nonempty A3.fam3.base3.Ix := by
  first | exact @GlobalTheory.Div.nonempty_ix_of_pos | exact GlobalTheory.Div.nonempty_ix_of_pos | (intros; apply GlobalTheory.Div.nonempty_ix_of_pos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.range_complex_points_level_forms_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.LUnif → ∀ b i, LinearMap.range ((R.toCx3 F).w0C b i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 b (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) := by
  first | exact @GlobalTheory.LevelRange.range_w0C_eq | exact GlobalTheory.LevelRange.range_w0C_eq | (intros; apply GlobalTheory.LevelRange.range_w0C_eq <;> assumption)
end
