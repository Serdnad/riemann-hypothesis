module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle012
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle001
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle011
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import Formalism.UnipotentAdelicQuotients.Bundle001
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.Invsum

theorem invariance_contraction {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β γ : Type} [Fintype β] (b : β → P)
    (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ) (E : γ → Module.End ℂ M)
    (hanti : ∀ i j k, c j i k = -c i j k) (hD : ∀ k j, D k (b j) = ∑ i, c i j k • b i)
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M)
    (hinv : ∀ k (Y : Fin q → P), E k (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s))))
    (k : γ) (J : Fin q → β) :
    ∑ s, ∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) = -E k (ω (b ∘ J)) := by
  have step : ∀ s, ω (Function.update (b ∘ J) s (D k ((b ∘ J) s))) =
      -∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) := by
    intro s
    have e : D k ((b ∘ J) s) = ∑ i, c i (J s) k • b i := hD k (J s)
    have h1 : ω (Function.update (b ∘ J) s (∑ i, c i (J s) k • b i)) =
        ∑ i, ω (Function.update (b ∘ J) s (c i (J s) k • b i)) :=
      ω.toMultilinearMap.map_update_sum Finset.univ s (fun i => c i (J s) k • b i) (b ∘ J)
    rw [e, h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : ω (Function.update (b ∘ J) s (c i (J s) k • b i)) =
        c i (J s) k • ω (Function.update (b ∘ J) s (b i)) :=
      ω.map_update_smul (b ∘ J) s (c i (J s) k) (b i)
    have h3 : ((c (J s) i k : ℝ) : ℂ) • ω (Function.update (b ∘ J) s (b i)) =
        c (J s) i k • ω (Function.update (b ∘ J) s (b i)) :=
      algebraMap_smul ℂ (c (J s) i k) (ω (Function.update (b ∘ J) s (b i)))
    rw [h2, h3, hanti (J s) i k, neg_smul]
  rw [hinv k (b ∘ J), Finset.sum_congr rfl fun s _ => step s, Finset.sum_neg_distrib, neg_neg]

end GlobalTheory.CompanionTheory.Invsum
end

section

open MeasureTheory
open scoped Matrix

theorem _root_.GlobalTheory.T.fourier_injective_matrix_space : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ, Continuous g → Integrable g → (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness | exact GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness | (intros; apply GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Iwasawa

theorem exists_upper_mul_unitary_complex {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y) :
    ∃ B R K : Matrix (Fin n) (Fin n) ℂ, B.IsUpperTriangular ∧ B * R = 1 ∧ R * B = 1 ∧
      K * Kᴴ = 1 ∧ Kᴴ * K = 1 ∧ Y = B * K := by
  let e : Fin n ≃ Fin n := Fin.revPerm
  have hYd : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY).ne_zero
  set Y' : Matrix (Fin n) (Fin n) ℂ := Y.submatrix e e with hY'
  have hY'u : IsUnit Y' := by
    rw [Matrix.isUnit_iff_isUnit_det, hY', Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det Y).mp hY
  have hpd : (Y' * Y'ᴴ).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self Y' (Matrix.vecMul_injective_iff_isUnit.mpr hY'u)
  obtain ⟨C, a, hCu, -, -, hC⟩ := CompanionTheory.D.gk.admitted.CholeskyDecomposition.exists_cholesky hpd
  have hBu : (Cᴴ.submatrix e e).IsUpperTriangular := by
    intro i j hij
    have h0 : C (e j) (e i) = 0 := hCu (Fin.rev_lt_rev.mpr hij)
    simp only [Matrix.submatrix_apply, Matrix.conjTranspose_apply]
    rw [h0, star_zero]
  have hBB : Cᴴ.submatrix e e * (Cᴴ.submatrix e e)ᴴ = Y * Yᴴ := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose, Matrix.submatrix_mul_equiv, hC,
      hY', Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix]
    have hee : (e : Fin n → Fin n) ∘ e = id := funext fun i => Fin.rev_rev i
    rw [hee, Matrix.submatrix_id_id]
  have hBd : (Cᴴ.submatrix e e).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBB
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, Matrix.det_conjTranspose] at this
    exact mul_ne_zero hYd (star_ne_zero.mpr hYd) this.symm
  set B := Cᴴ.submatrix e e with hBdef
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hBd)
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hBd)
  have hKK : (B⁻¹ * Y) * (B⁻¹ * Y)ᴴ = 1 := by
    calc (B⁻¹ * Y) * (B⁻¹ * Y)ᴴ = B⁻¹ * (Y * Yᴴ) * B⁻¹ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * Bᴴ) * B⁻¹ᴴ := by rw [hBB]
      _ = (B⁻¹ * B) * (B⁻¹ * B)ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBi, Matrix.conjTranspose_one, Matrix.mul_one]
  refine ⟨B, B⁻¹, B⁻¹ * Y, hBu, hBi', hBi, hKK, mul_eq_one_comm.mp hKK, ?_⟩
  rw [← Matrix.mul_assoc, hBi', Matrix.one_mul]

noncomputable abbrev evalMat {ι : Type} {n : ℕ} (w : ι) :
    Matrix (Fin n) (Fin n) (ι → ℂ) →+* Matrix (Fin n) (Fin n) ℂ :=
  (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix

theorem evalMat_apply {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ))
    (i j : Fin n) : evalMat w X i j = X i j w := rfl

theorem evalMat_conjTranspose {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ)) :
    evalMat w Xᴴ = (evalMat w X)ᴴ := by
  ext i j
  simp only [evalMat_apply, Matrix.conjTranspose_apply]
  rfl

theorem matrix_ext_eval {ι : Type} {n : ℕ} {X X' : Matrix (Fin n) (Fin n) (ι → ℂ)}
    (h : ∀ w, evalMat w X = evalMat w X') : X = X' := by
  ext i j w
  have := congrFun (congrFun (h w) i) j
  rwa [evalMat_apply, evalMat_apply] at this

theorem exists_upper_mul_unitary {ι : Type} {n : ℕ} (y : GL (Fin n) (ι → ℂ)) :
    ∃ (b : GL (Fin n) (ι → ℂ)) (k : Matrix.unitaryGroup (Fin n) (ι → ℂ)),
      (∀ i j : Fin n, j < i → b.val i j = 0) ∧ y = b * Unitary.toUnits k := by
  have hu : ∀ w : ι, IsUnit (evalMat w (y : Matrix (Fin n) (Fin n) (ι → ℂ))) :=
    fun w => (Units.isUnit y).map (evalMat w)
  choose B R K hB hBR hRB hKK hKK' hY using fun w => exists_upper_mul_unitary_complex _ (hu w)
  let b : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => B w i j
  let r : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => R w i j
  let k : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => K w i j
  have eb : ∀ w, evalMat w b = B w := fun w => by ext i j; rw [evalMat_apply]
  have er : ∀ w, evalMat w r = R w := fun w => by ext i j; rw [evalMat_apply]
  have ek : ∀ w, evalMat w k = K w := fun w => by ext i j; rw [evalMat_apply]
  have hbr : b * r = 1 := matrix_ext_eval fun w => by rw [map_mul, eb, er, hBR w, map_one]
  have hrb : r * b = 1 := matrix_ext_eval fun w => by rw [map_mul, eb, er, hRB w, map_one]
  have hk1 : k * star k = 1 := matrix_ext_eval fun w => by
    rw [map_mul, Matrix.star_eq_conjTranspose, evalMat_conjTranspose, ek, hKK w, map_one]
  have hk2 : star k * k = 1 := matrix_ext_eval fun w => by
    rw [map_mul, Matrix.star_eq_conjTranspose, evalMat_conjTranspose, ek, hKK' w, map_one]
  refine ⟨⟨b, r, hbr, hrb⟩, ⟨k, Unitary.mem_iff.mpr ⟨hk2, hk1⟩⟩, ?_, ?_⟩
  · intro i j hij
    funext w
    exact hB w hij
  · apply Units.ext
    apply matrix_ext_eval
    intro w
    rw [Units.val_mul]
    show evalMat w (y : Matrix (Fin n) (Fin n) (ι → ℂ)) = evalMat w (b * k)
    rw [map_mul, eb, ek]
    exact hY w

end GlobalTheory.CompanionTheory.Iwasawa
end

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_rightInvariant_measure_unitaryGroup
    (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] :
    ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ),
      IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
    GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  let μ : Measure (Matrix.unitaryGroup (Fin n) ℂ) := Measure.haarMeasure ⊤
  refine ⟨μ.inv, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.ModelS
end

section

open Matrix

theorem _root_.GlobalTheory.T.annihilator_compact_within_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) → ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧ ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | exact GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.lattice_annihilator_within_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)), U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | exact GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.unitary_frames_preserve_norm_sq_sum : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames | exact GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames | (intros; apply GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames <;> assumption)
end

section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem sum_addChar_ofMul_mul_ofMul_inv (G : Type) [CommGroup G] [Fintype G] [DecidableEq G]
    (a b : G) :
    ∑ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      if a = b then (Fintype.card G : ℂ) else 0 := by
  have h : ∀ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      ψ (Additive.ofMul (a * b⁻¹)) := by
    intro ψ
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul]
  simp_rw [h]
  rw [AddChar.sum_apply_eq_ite]
  have hc : Fintype.card (Additive G) = Fintype.card G :=
    Fintype.card_congr Additive.ofMul.symm
  simp only [hc, ofMul_eq_zero, mul_inv_eq_one]

end GlobalTheory.CompanionTheory.PartialZeta
end

section

open MeasureTheory
open scoped ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.exists_bump_with_nonzero_integral : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) (U : Set X), IsOpen U → m Uᶜ = 0 → m ≠ 0 → (∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U → Integrable χ m) → ∃ χ : X → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∫ x, χ x ∂m ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen | exact GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen | (intros; apply GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen <;> assumption)
end

section

open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroup

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem pow_mem_of_mul_closed {G : Set A} (h1 : (1 : A) ∈ G) (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {g : A} (hg : g ∈ G) (m : ℕ) : g ^ m ∈ G := by
  induction m with
  | zero => simpa using h1
  | succ m ih => rw [pow_succ]; exact hmul _ ih _ hg

theorem exp_neg_mem {G : Set A} (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1) {x : A}
    (hx : NormedSpace.exp x ∈ G) : NormedSpace.exp (-x) ∈ G := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨h, hh, hhg, -⟩ := hinv _ hx
  have hone : NormedSpace.exp x * NormedSpace.exp (-x) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl x)), add_neg_cancel,
      NormedSpace.exp_zero]
  have heq : h = NormedSpace.exp (-x) := by
    calc h = h * (NormedSpace.exp x * NormedSpace.exp (-x)) := by rw [hone, mul_one]
      _ = NormedSpace.exp (-x) := by rw [← mul_assoc, hhg, one_mul]
  exact heq ▸ hh

theorem exp_smul_limit_mem {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) {ε : ℕ → ℝ} {a : ℕ → A} {Y : A}
    (hε0 : ∀ k, 0 < ε k) (hε : Tendsto ε atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 Y))
    (hG : ∀ k, NormedSpace.exp (ε k • a k) ∈ G) {t : ℝ} (ht : 0 ≤ t) :
    NormedSpace.exp (t • Y) ∈ G := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hm : Tendsto (fun k => (⌊t / ε k⌋₊ : ℝ) * ε k) atTop (𝓝 t) := by
    have hlo : ∀ k, t - ε k ≤ (⌊t / ε k⌋₊ : ℝ) * ε k := by
      intro k
      have h3 := Nat.lt_floor_add_one (t / ε k)
      have h2 : t / ε k * ε k = t := div_mul_cancel₀ _ (hε0 k).ne'
      nlinarith [hε0 k]
    have hhi : ∀ k, (⌊t / ε k⌋₊ : ℝ) * ε k ≤ t := by
      intro k
      have h3 := Nat.floor_le (div_nonneg ht (hε0 k).le)
      have h2 : t / ε k * ε k = t := div_mul_cancel₀ _ (hε0 k).ne'
      nlinarith [hε0 k]
    have hl : Tendsto (fun k => t - ε k) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).sub hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hhi
  have hlim : Tendsto (fun k => NormedSpace.exp (((⌊t / ε k⌋₊ : ℝ) * ε k) • a k)) atTop
      (𝓝 (NormedSpace.exp (t • Y))) :=
    (NormedSpace.exp_continuous.tendsto _).comp (hm.smul ha)
  refine hc.mem_of_tendsto hlim (Eventually.of_forall fun k => ?_)
  have hk : ((⌊t / ε k⌋₊ : ℝ) * ε k) • a k = ⌊t / ε k⌋₊ • (ε k • a k) := by
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
  rw [hk, NormedSpace.exp_nsmul]
  exact pow_mem_of_mul_closed h1 hmul (hG k) _

theorem exists_nhds_kernel_eq_zero {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1)
    {S : Submodule ℝ A} (hS : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    (p : A →L[ℝ] A) (hp : ∀ Z ∈ S, p Z = Z) :
    ∃ W₀ ∈ 𝓝 (0 : A), ∀ Y ∈ W₀, NormedSpace.exp Y ∈ G → p Y = 0 → Y = 0 := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ Y : A, ‖Y‖ < 1 / ((k : ℝ) + 1) ∧ NormedSpace.exp Y ∈ G ∧ p Y = 0 ∧ Y ≠ 0 := by
    intro k
    obtain ⟨Y, hY, hYG, hYp, hY0⟩ :=
      hcon (Metric.ball 0 (1 / ((k : ℝ) + 1))) (Metric.ball_mem_nhds _ (by positivity))
    exact ⟨Y, by simpa using hY, hYG, hYp, hY0⟩
  choose Y hYn hYG hYp hY0 using hseq
  have hpos : ∀ k, 0 < ‖Y k‖ := fun k => norm_pos_iff.2 (hY0 k)
  have hsph : ∀ k, (‖Y k‖)⁻¹ • Y k ∈ Metric.sphere (0 : A) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hpos k).ne']
  haveI : ProperSpace A := FiniteDimensional.proper ℝ A
  obtain ⟨b, hb, φ, hφ, hlim⟩ := (isCompact_sphere (0 : A) 1).tendsto_subseq hsph
  have hε : Tendsto (fun k => ‖Y k‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun k => (hYn k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hεφ : Tendsto (fun k => ‖Y (φ k)‖) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
  have hmem : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • b) ∈ G := by
    intro t ht
    refine exp_smul_limit_mem hc h1 hmul (ε := fun k => ‖Y (φ k)‖)
      (a := fun k => (‖Y (φ k)‖)⁻¹ • Y (φ k)) (fun k => hpos _) hεφ hlim (fun k => ?_) ht
    have : ‖Y (φ k)‖ • (‖Y (φ k)‖)⁻¹ • Y (φ k) = Y (φ k) := by
      rw [smul_smul, mul_inv_cancel₀ (hpos _).ne', one_smul]
    simpa only [this] using hYG (φ k)
  have hbS : b ∈ S := by
    refine (hS b).2 fun t => ?_
    rcases le_total 0 t with ht | ht
    · exact hmem t ht
    · have := exp_neg_mem hinv (hmem (-t) (by linarith))
      simpa using this
  have hpb : p b = 0 := by
    have h2 : Tendsto (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) atTop (𝓝 (p b)) :=
      (p.continuous.tendsto b).comp hlim
    have h3 : (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) = fun _ => 0 := by
      funext k
      rw [map_smul, hYp, smul_zero]
    rw [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  have hb0 : b = 0 := by rw [← hp b hbS, hpb]
  have hb1 : ‖b‖ = 1 := mem_sphere_zero_iff_norm.1 hb
  rw [hb0, norm_zero] at hb1
  exact zero_ne_one hb1

theorem eventually_exp_of_mem {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1)
    {S : Submodule ℝ A} (hS : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {W : Set A} (hW : W ∈ 𝓝 (0 : A)) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ G → ∃ X ∈ S, X ∈ W ∧ NormedSpace.exp X = g := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨f, hf⟩ := S.subtype.exists_leftInverse_of_injective (by simp)
  let p : A →L[ℝ] A := LinearMap.toContinuousLinearMap (S.subtype ∘ₗ f)
  have hpS : ∀ Z, p Z ∈ S := fun Z => (f Z).2
  have hp : ∀ Z ∈ S, p Z = Z := by
    intro Z hZ
    have h2 := LinearMap.congr_fun hf ⟨Z, hZ⟩
    have h3 : f Z = ⟨Z, hZ⟩ := h2
    change ((f Z : S) : A) = Z
    rw [h3]
  obtain ⟨W₀, hW₀, hker⟩ := exists_nhds_kernel_eq_zero hc h1 hmul hinv hS p hp
  let q : A →L[ℝ] A := ContinuousLinearMap.id ℝ A - p
  have hq : ∀ Z, q Z = Z - p Z := fun Z => rfl
  let Φ : A → A := fun Z => NormedSpace.exp (p Z) * NormedSpace.exp (q Z)
  have hE : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  have hEp : HasStrictFDerivAt (fun Z => NormedSpace.exp (p Z)) p (0 : A) := by
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (p 0) := by
      simpa using hE
    exact (h2.comp (0 : A) p.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hEq : HasStrictFDerivAt (fun Z => NormedSpace.exp (q Z)) q (0 : A) := by
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (q 0) := by
      simpa using hE
    exact (h2.comp (0 : A) q.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    have h2 : HasStrictFDerivAt Φ _ 0 := hEp.mul' hEq
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    simp [hq]
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hmap := hΦ.map_nhds_eq_of_equiv
  have hW' : p ⁻¹' W ∩ q ⁻¹' W₀ ∈ 𝓝 (0 : A) := by
    refine inter_mem (p.continuous.continuousAt.preimage_mem_nhds ?_)
      (q.continuous.continuousAt.preimage_mem_nhds ?_)
    · simpa using hW
    · simpa using hW₀
  have himg : Φ '' (p ⁻¹' W ∩ q ⁻¹' W₀) ∈ 𝓝 (1 : A) := by
    rw [← hΦ0, ← hmap]
    exact image_mem_map hW'
  filter_upwards [himg]
  rintro g ⟨Z, ⟨hZ1, hZ2⟩, rfl⟩ hg
  have hpG : NormedSpace.exp (p Z) ∈ G := by
    simpa using (hS _).1 (hpS Z) 1
  have hnG : NormedSpace.exp (-(p Z)) ∈ G := exp_neg_mem hinv hpG
  have hone : NormedSpace.exp (-(p Z)) * NormedSpace.exp (p Z) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl (p Z))), neg_add_cancel,
      NormedSpace.exp_zero]
  have hqG : NormedSpace.exp (q Z) ∈ G := by
    have h2 := hmul _ hnG _ hg
    simpa only [Φ, ← mul_assoc, hone, one_mul] using h2
  have hpq : p (q Z) = 0 := by
    rw [hq, map_sub, hp _ (hpS Z), sub_self]
  have hq0 : q Z = 0 := hker _ hZ2 hqG hpq
  refine ⟨p Z, hpS Z, hZ1, ?_⟩
  simp [Φ, hq0]

end Banach

end GlobalTheory.CompanionTheory.ClosedSubgroup
end
end

section

open MeasureTheory
open scoped ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.local_unique_square_root_near_one : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V), Continuous ψ → Continuous ψ.symm → ∃ (r : B → B) (U : Set B), U ∈ nhds (1 : B) ∧ Filter.Tendsto r (nhds 1) (nhds 1) ∧ (∀ᶠ h in nhds (1 : B), r h * r h = h) ∧ ∀ x ∈ U, ∀ y ∈ U, x * x = y * y → x = y := by
  first | exact @GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | exact GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | (intros; apply GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt <;> assumption)
end
