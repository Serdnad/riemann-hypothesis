module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAnnihilatedOfAevalMemKerPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle024
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Perfect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle078
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle023
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open MvPolynomial

theorem _root_.GlobalTheory.T.totalDegree_le_of_root_of_monic_eval : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (j : Fin D), y j ≠ 0 → ∀ (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ) {ι : Type} (z : ι → K), (∀ i, ∃ (N : ℕ) (C : MvPolynomial (Fin D) ℤ), C.totalDegree ≤ N ∧ z i * y j ^ N = aeval y C) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom (aeval y T₀ / y j ^ q) = 0 → T₀.totalDegree ≤ q := by
  first | exact @GlobalTheory.totalDegree_le_of_integral_at_infinity | exact GlobalTheory.totalDegree_le_of_integral_at_infinity | (intros; apply GlobalTheory.totalDegree_le_of_integral_at_infinity <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_poly_entries_conj_left_right_mul : ∀ (n : ℕ) (a b : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (a * g * b) z.1 z.2) (fun z : Fin n × Fin n => star ((a * g * b) z.1 z.2))) P = MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (g) z.1 z.2) (fun z : Fin n × Fin n => star ((g) z.1 z.2))) Q := by
  first | exact @GlobalTheory.PolyEntryMul.main | exact GlobalTheory.PolyEntryMul.main | (intros; apply GlobalTheory.PolyEntryMul.main <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.coeff_allOnes_sumAlgEquiv_derivation_eq : ∀ {σ : Type} {L : ℕ} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (b : MvPolynomial (Fin L ⊕ σ) ℂ), AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ)) (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) = D (AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ))) := by
  first | exact @GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation | exact GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation | (intros; apply GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem exists_mvPolynomial_pick_point :
    ∀ (S : Type) (T : Finset (S → ℂ)) (p : S → ℂ), ∃ Q : MvPolynomial S ℂ,
      MvPolynomial.eval p Q = 1 ∧ ∀ t ∈ T, t ≠ p → MvPolynomial.eval t Q = 0 := by
  classical
  intro S T p
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a T _ ih =>
    obtain ⟨Q, hQ1, hQ0⟩ := ih
    by_cases hap : a = p
    · refine ⟨Q, hQ1, fun t ht htp => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact absurd hap htp
      · exact hQ0 t ht htp
    · obtain ⟨s, hs⟩ := Function.ne_iff.1 hap
      have hne : p s - a s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
      refine ⟨Q * (MvPolynomial.C (p s - a s)⁻¹ * (MvPolynomial.X s - MvPolynomial.C (a s))),
        ?_, fun t ht htp => ?_⟩
      · simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, hQ1, one_mul]
        exact inv_mul_cancel₀ hne
      · rcases Finset.mem_insert.1 ht with rfl | ht
        · simp
        · simp [hQ0 t ht htp]

end GlobalTheory.QFam
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow : ∀ (d N : ℕ), ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) → (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) → MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * AddMonoidAlgebra.coeff P α = 0 := by
  first | exact @GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | exact GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | (intros; apply GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  first | exact @GlobalTheory.ker_aeval_truncated | exact GlobalTheory.ker_aeval_truncated | (intros; apply GlobalTheory.ker_aeval_truncated <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localized_presentation_eval_quotient_fraction : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  first | exact @GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent | exact GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent | (intros; apply GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.cotangent_map_injective_of_square_presentation_at_point : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  first | exact @GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation | exact GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation | (intros; apply GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_presentation_square_at_point_of_localFactor : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  first | exact @GlobalTheory.sqloc_present | exact GlobalTheory.sqloc_present | (intros; apply GlobalTheory.sqloc_present <;> assumption)
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  first | exact @GlobalTheory.mem_sq_localization_of_pderiv_mem | exact GlobalTheory.mem_sq_localization_of_pderiv_mem | (intros; apply GlobalTheory.mem_sq_localization_of_pderiv_mem <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  first | exact @GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable | exact GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable | (intros; apply GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero : ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ), (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by
  first | exact @GlobalTheory.hypersurface_part_no_splitting_factorisation | exact GlobalTheory.hypersurface_part_no_splitting_factorisation | (intros; apply GlobalTheory.hypersurface_part_no_splitting_factorisation <;> assumption)
end
