module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle001
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle006
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

section

noncomputable section

open CategoryTheory Polynomial TensorProduct

namespace GlobalTheory.NormalDescent

theorem charpoly_reverse_coeff_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (c : K) (k : ℕ) :
    (c • f).charpoly.reverse.coeff k = c ^ k * f.charpoly.reverse.coeff k := by
  classical
  let e := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix _ e, ← LinearMap.charpoly_toMatrix _ e, Matrix.reverse_charpoly,
    Matrix.reverse_charpoly, map_smul, mul_comm, ← comp_C_mul_X_coeff]
  generalize LinearMap.toMatrix e e f = M
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]
  apply congrArg (fun p : K[X] => p.coeff)
  apply congrArg Matrix.det
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j <;> simp [hij] <;> ring

theorem exists_charK_coeff {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (n : ℕ) :
    ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).coeff n := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  let K := FractionRing A
  let Ω := AlgebraicClosure K
  let ι := algebraMap K Ω
  let V := K ⊗[A] B
  haveI : Module.Free K V := Module.Free.of_divisionRing _ _
  let e := Module.finBasis K V
  let Mx := Algebra.leftMulMatrix e ((1 : K) ⊗ₜ[A] b)
  have hg : charK φ hφ K b = Mx.charpoly := by
    show (Algebra.lmul K V ((1 : K) ⊗ₜ[A] b)).charpoly = _
    show _ = (Algebra.leftMulMatrix e _).charpoly
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  have hb : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have h1 : IsIntegral A ((1 : K) ⊗ₜ[A] b) :=
    hb.map (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B)
  have h2 : IsIntegral A Mx := h1.map ((Algebra.leftMulMatrix e).restrictScalars A)
  have h3 : IsIntegral A (Mx.map ι) := h2.map (AlgHom.mapMatrix (IsScalarTower.toAlgHom A K Ω))
  obtain ⟨p, hpm, hp⟩ := h3
  have hroot : ∀ μ ∈ (Mx.charpoly.map ι).roots, IsIntegral A μ := by
    intro μ hμ
    have hs : μ ∈ spectrum Ω (Mx.map ι) := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
      exact isRoot_of_mem_roots hμ
    have h4 := spectrum.subset_polynomial_aeval (Mx.map ι) (p.map (algebraMap A Ω)) ⟨μ, hs, rfl⟩
    have h5 : aeval (Mx.map ι) (p.map (algebraMap A Ω)) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h5] at h4
    refine ⟨p, hpm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap Ω]
    by_contra hne
    exact (spectrum.mem_iff.1 h4) (by
      simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) Ω)))
  have hl : Mx.charpoly.map ι ∈ Polynomial.lifts (integralClosure A Ω).val.toRingHom :=
    (IsAlgClosed.splits _).mem_lift_of_roots_mem_range ((Matrix.charpoly_monic _).map _) _
      fun μ hμ => ⟨⟨μ, hroot μ hμ⟩, rfl⟩
  rw [lifts_iff_coeff_lifts] at hl
  obtain ⟨s, hs⟩ := hl n
  have hc : IsIntegral A (Mx.charpoly.coeff n) := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K Ω) ι.injective).1 ?_
    show IsIntegral A (ι _)
    rw [← coeff_map, ← hs]
    exact s.2
  rw [hg]
  exact IsIntegrallyClosed.isIntegral_iff.1 hc

theorem normCoeff_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  intro A B _ _ _ _ φ hφ u b k
  have hrev : ∀ b' : B, ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b').reverse.coeff k :=
    fun b' => by rw [coeff_reverse]; exact exists_charK_coeff φ hφ b' _
  have key : (charK φ hφ (FractionRing A) (φ u * b)).reverse.coeff k
      = (algebraMap A (FractionRing A) u) ^ k * (charK φ hφ (FractionRing A) b).reverse.coeff k := by
    letI := φ.toAlgebra
    haveI : Module.Finite A B := hφ
    haveI : Module.Free (FractionRing A) (FractionRing A ⊗[A] B) := Module.Free.of_divisionRing _ _
    have e1 : (1 : FractionRing A) ⊗ₜ[A] (φ u * b)
        = algebraMap A (FractionRing A) u • ((1 : FractionRing A) ⊗ₜ[A] b) := by
      rw [algebraMap_smul, ← tmul_smul, Algebra.smul_def]; rfl
    show (Algebra.lmul _ _ ((1 : FractionRing A) ⊗ₜ[A] (φ u * b))).charpoly.reverse.coeff k = _
    rw [e1, map_smul]
    exact charpoly_reverse_coeff_smul _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [map_mul, map_pow, algebraMap_normCoeff _ _ _ _ (hrev _), algebraMap_normCoeff _ _ _ _ (hrev _), key]

end GlobalTheory.NormalDescent
end
end

section

open Matrix

theorem _root_.GlobalTheory.T.rat_mem_span_of_real_mem_span_fin : ∀ (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ), (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) → v ∈ Submodule.span ℚ (Set.range w) := by
  first | exact @GlobalTheory.rat_mem_span_of_real_mem_span | exact GlobalTheory.rat_mem_span_of_real_mem_span | (intros; apply GlobalTheory.rat_mem_span_of_real_mem_span <;> assumption)
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

variable {ι : Type} {N n : ℕ}

def subst2 (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l)

def substF (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l)

theorem subst2_X (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (p : Fin N × Fin n) :
    subst2 h g (X p) = ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l) := aeval_X _ _

theorem substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    substF h g (X p) = ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l) := aeval_X _ _

theorem totalDegree_aeval_le {κ : Type} (f : κ → MvPolynomial κ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial κ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeLinear.main
  | exact _root_.GlobalTheory.AevalTotalDegreeLinear.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeLinear.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeLinear.main ..)

theorem totalDegree_substF_le (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) : (substF h g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

theorem subst2_mul (h h' : Matrix (Fin N) (Fin N) ℂ) (g g' : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 h g (subst2 h' g' P) = subst2 (h * h') (g * g') P := by
  have key : (subst2 h g).comp (subst2 h' g') = subst2 (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, subst2_X, subst2_X]

    simp only [map_sum, map_mul, subst2_X, algHom_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

theorem subst2_one (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 1 1 P = P := by
  have key : subst2 (1 : Matrix (Fin N) (Fin N) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

end GlobalTheory.CompactHowe

end
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_pow_mul_mvEval_eq_eval_of_laurent : ∀ (σ : Type) (g : σ → ℂ → ℂ), (∀ a, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * g a t = p.eval t) → ∀ Q : MvPolynomial σ ℂ, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * MvPolynomial.eval (fun a => g a t) Q = p.eval t := by
  first | exact @GlobalTheory.laurent_poly_eval_of_laurent | exact GlobalTheory.laurent_poly_eval_of_laurent | (intros; apply GlobalTheory.laurent_poly_eval_of_laurent <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_zpow_of_multiplicative_of_pow_mul_eq_eval : ∀ (χ : ℂ → ℂ), (∀ s t : ℂ, s ≠ 0 → t ≠ 0 → χ (s * t) = χ s * χ t) → χ 1 = 1 → ∀ (N : ℕ) (p : Polynomial ℂ), (∀ t : ℂ, t ≠ 0 → t ^ N * χ t = p.eval t) → ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ t = t ^ k := by
  first | exact @GlobalTheory.mono_char_of_mul_poly_div_pow | exact GlobalTheory.mono_char_of_mul_poly_div_pow | (intros; apply GlobalTheory.mono_char_of_mul_poly_div_pow <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_isotropic_dual_of_skew_matrix' : ∀ (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε ψ : Fin g → Fin r → ℚ), Mqᵀ = -Mq → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧ (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧ ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  first | exact @GlobalTheory.exists_isotropic_dual_of_skew_matrix | exact GlobalTheory.exists_isotropic_dual_of_skew_matrix | (intros; apply GlobalTheory.exists_isotropic_dual_of_skew_matrix <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

def GeneratesAlong (I : W.IdealSheafData) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) : Prop :=
  (⨆ k, g ⁻¹ᵁ L.U k = ⊤) ∧ ∀ (k : L.ι) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ L.U k),
    I.ideal A = Ideal.span (Set.range fun j => (g.appLE (L.U k) A.1 h).hom ((σ j).f k))

end GlobalTheory.ProjBlowup
end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem _root_.GlobalTheory.T.exists_section_extending_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  first | exact @GlobalTheory.glue_of_dense_openImmersion | exact GlobalTheory.glue_of_dense_openImmersion | (intros; apply GlobalTheory.glue_of_dense_openImmersion <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero : ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  first | exact @GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | exact GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero | (intros; apply GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.FockDetDer

theorem trace_fromBlocks_diag {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    (fromBlocks X 0 0 Y).trace = X.trace + Y.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem symmetric_block_trace_inverse_eq_two_mul {P Q : ℕ} (C : Matrix (Fin Q) (Fin P) ℂ) (B : Matrix (Fin P) (Fin Q) ℂ) (c : ℂ)
    (h : IsUnit (1 - c • (C * B)).det) :
    IsUnit (1 - c • ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))).det ∧
    ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (1 - c • ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))⁻¹).trace =
      2 * ((1 - c • (C * B))⁻¹ * (C * B)).trace := by
  have hTS : (fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      fromBlocks (B * C) 0 0 (C * B)ᵀ := by
    rw [fromBlocks_multiply]; simp
  have h1 : (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - c • fromBlocks (B * C) 0 0 (C * B)ᵀ =
      fromBlocks (1 - c • (B * C)) 0 0 (1 - c • (C * B))ᵀ := by
    rw [← fromBlocks_one]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, eq_comm]
  have hd : (1 - c • (B * C)).det = (1 - c • (C * B)).det := by
    rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]
  have h' : IsUnit (1 - c • (B * C)).det := hd ▸ h
  rw [hTS, h1]
  refine ⟨?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_transpose]
    exact h'.mul h
  · have hinv : (fromBlocks (1 - c • (B * C)) 0 0 (1 - c • (C * B))ᵀ)⁻¹ =
        fromBlocks (1 - c • (B * C))⁻¹ 0 0 ((1 - c • (C * B))⁻¹)ᵀ := by
      apply Matrix.inv_eq_left_inv
      rw [fromBlocks_multiply, ← transpose_mul, nonsing_inv_mul _ h', mul_nonsing_inv _ h]
      simp
    have hMB : (1 - c • (B * C))⁻¹ * B = B * (1 - c • (C * B))⁻¹ := by
      have e : B * (1 - c • (C * B)) = (1 - c • (B * C)) * B := by
        simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      calc (1 - c • (B * C))⁻¹ * B
          = (1 - c • (B * C))⁻¹ * B * ((1 - c • (C * B)) * (1 - c • (C * B))⁻¹) := by
            rw [mul_nonsing_inv _ h, Matrix.mul_one]
        _ = (1 - c • (B * C))⁻¹ * (B * (1 - c • (C * B))) * (1 - c • (C * B))⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = B * (1 - c • (C * B))⁻¹ := by
            rw [e, ← Matrix.mul_assoc, nonsing_inv_mul _ h', Matrix.one_mul]
    rw [hinv, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [trace_fromBlocks_diag, ← transpose_mul, trace_transpose, two_mul]
    congr 1
    rw [trace_mul_comm (B * C), ← Matrix.mul_assoc, hMB, Matrix.mul_assoc, trace_mul_comm B,
      Matrix.mul_assoc]

theorem hasDerivAt_det_one_sub_sq :
    ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (t : ℝ),
      IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det →
      let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 (Matrix.transpose Aᴴ) Aᴴ 0
      let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0
      IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧
        HasDerivAt (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det)
          (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) *
            (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det) t := by
  intro P Q A B t h S T
  obtain ⟨h1, h2⟩ := symmetric_block_trace_inverse_eq_two_mul Aᴴ B ((t : ℂ) ^ 2) h
  refine ⟨h1, ?_⟩
  have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ)) t := by
    have := (hasDerivAt_pow 2 (t : ℂ)).comp_ofReal
    simpa using this
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s : ℝ => 1 - ((s : ℂ) ^ 2) • (Aᴴ * B))
    (-((2 * (t : ℂ)) • (Aᴴ * B))) t (fun i j => by
      have := (hsq.mul_const ((Aᴴ * B) i j)).const_sub ((1 : Matrix (Fin Q) (Fin Q) ℂ) i j)
      simpa using this)
  refine hd.congr_deriv ?_
  have hne := h.ne_zero
  have hadj : (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).adjugate =
      (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det • (1 - ((t : ℂ) ^ 2) • (Aᴴ * B))⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hne, one_smul]
  simp only [S, T]
  rw [h2, hadj, Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_smul, trace_smul, trace_neg, trace_smul]
  simp only [smul_eq_mul]
  ring

end GlobalTheory.FockDetDer
end

section

open Matrix

namespace GlobalTheory.Mem.InvDer

theorem hasDerivAt_inv_det_and_inv (n : ℕ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (M' : Matrix (Fin n) (Fin n) ℂ) (h0 : M 0 = 1)
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0) :
    HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 ∧
      ∀ i j, HasDerivAt (fun t => (M t)⁻¹ i j) (-M' i j) 0 := by
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det M M' 0 hM
  rw [h0, adjugate_one, Matrix.one_mul] at hd
  have hdet0 : (M 0).det = 1 := by rw [h0, det_one]
  have hne : (M 0).det ≠ 0 := by rw [hdet0]; exact one_ne_zero
  have hinv : HasDerivAt (fun t => ((M t).det)⁻¹) (-M'.trace) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-((M 0).det ^ 2)⁻¹) (M 0).det := hasDerivAt_inv hne
    have h2 := h1.comp_of_eq (0 : ℝ) hd rfl
    refine HasDerivAt.congr_deriv h2 ?_
    rw [hdet0]; simp
  refine ⟨hinv, ?_⟩
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun t => (M t)⁻¹ i j) 0 := by
    intro i j
    have hadj : DifferentiableAt ℝ (fun t => (M t).adjugate i j) 0 := by
      have := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t => (M t).updateRow j (Pi.single i 1))
        (M'.updateRow j 0) 0 (by
          intro a b
          by_cases h : a = j
          · simp only [updateRow_apply, h, if_true]
            exact hasDerivAt_const _ _
          · simp only [updateRow_apply, h, if_false]
            exact hM a b)
      simpa only [adjugate_apply] using this.differentiableAt
    have := hinv.differentiableAt.mul hadj
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  intro i j
  have hev : ∀ᶠ t in nhds (0 : ℝ), (M t).det ≠ 0 := hd.continuousAt.eventually_ne hne
  have hprod : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j)
      (∑ k, (deriv (fun t => (M t)⁻¹ i k) 0 * M 0 k j + (M 0)⁻¹ i k * M' k j)) 0 :=
    HasDerivAt.fun_sum fun k _ => ((hdiff i k).hasDerivAt.fun_mul (hM k j))
  have hconst : HasDerivAt (fun t => ∑ k, (M t)⁻¹ i k * M t k j) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)]
  have huniq := hprod.unique hconst
  rw [h0, inv_one, Finset.sum_add_distrib] at huniq
  simp [Matrix.one_apply] at huniq
  have hfin : deriv (fun t => (M t)⁻¹ i j) 0 = -M' i j := eq_neg_of_add_eq_zero_left huniq
  rw [← hfin]
  exact (hdiff i j).hasDerivAt

end GlobalTheory.Mem.InvDer
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 → ∀ f f' : K → ℂ, Continuous f → Continuous f' → (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) → (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  first | exact @GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | exact GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | (intros; apply GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero <;> assumption)
end
