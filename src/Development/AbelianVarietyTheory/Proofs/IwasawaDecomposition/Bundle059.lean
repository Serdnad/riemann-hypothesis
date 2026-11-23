module

public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameEisensteinExtensionUniqueTotallyRamifiedPlac
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import ReciprocityTheory.Automorphisms.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (ϖ : 𝓞 E), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 →
    ∀ (π : Ω) [FiniteDimensional E (IntermediateField.adjoin E {π})] [NumberField (IntermediateField.adjoin E {π})],
    π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ W : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal ∧
      (∀ W' : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
        W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal → W' = W) ∧
      IsPlaceOver A W ∧ normV W = normV v ∧
      ∀ c : (W.adicCompletion (IntermediateField.adjoin E {π}))ˣ,
        (c : W.adicCompletion (IntermediateField.adjoin E {π})) =
          algebraMap (IntermediateField.adjoin E {π}) _ (IntermediateField.AdjoinSimple.gen E π) → IsUnifAt W c := by
  first | exact @GlobalTheory.TameRecPlace.main | exact GlobalTheory.TameRecPlace.main | (intros; apply GlobalTheory.TameRecPlace.main <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem shift_minors_vanish_finite {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  classical
  let p : ℕ → Polynomial ℂ := fun k =>
    if hk : k ≤ n then (-(B.submatrix (Fin.castLE hk) (Fin.castLE hk))).charpoly else 1
  have key : ∀ (k : ℕ) (hk : k ≤ n) (s : ℂ),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det
        = (p k).eval s := by
    intro k hk s
    simp only [p, dif_pos hk, Matrix.eval_charpoly]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.castLE_inj, smul_eq_mul, sub_neg_eq_add]
    split_ifs <;> ring
  have hp : ∀ k, p k ≠ 0 := by
    intro k
    by_cases hk : k ≤ n
    · simp only [p, dif_pos hk]; exact (Matrix.charpoly_monic _).ne_zero
    · simp [p, dif_neg hk]
  refine Set.Finite.subset
    ((Finset.range (n + 1)).finite_toSet.biUnion fun k _ =>
      Polynomial.finite_setOf_isRoot (hp k)) ?_
  intro s hs
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hs
  obtain ⟨k, hk, h0⟩ := hs
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_setOf_eq]
  exact ⟨k, Nat.lt_succ_of_le hk, by rw [Polynomial.IsRoot, ← key k hk s, h0]⟩

end GlobalTheory
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.CayleyRat

theorem exists_mem_GQ0_eq_cayley_of_skew_hermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  intro L _ _ _ n S hS hdet
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  set T : Matrix (Fin n) (Fin n) L := 1 - S with hT
  set U : Matrix (Fin n) (Fin n) L := 1 + S with hU
  have hSc : conjT c S = -S := by
    unfold conjT; exact (neg_eq_of_add_eq_zero_right hS).symm
  have hcT : conjT c T = U := by
    have : conjT c T = conjT c 1 - conjT c S := by
      simp [conjT, hT, Matrix.map_sub, Matrix.transpose_sub]
    rw [this, conjT_one, hSc, hU, sub_neg_eq_add]
  have hcU : conjT c U = T := by
    have : conjT c U = conjT c 1 + conjT c S := by
      simp [conjT, hU, Matrix.map_add (f := _), Matrix.transpose_add]
    rw [this, conjT_one, hSc, hT, sub_eq_add_neg]
  have hdetU : U.det ≠ 0 := by
    have : U.det = c T.det := by
      rw [← hcT, conjT, Matrix.det_transpose, RingHom.map_det]; rfl
    rw [this]; exact (map_ne_zero c).mpr hdet
  have huT : IsUnit T.det := isUnit_iff_ne_zero.mpr hdet
  have huU : IsUnit U.det := isUnit_iff_ne_zero.mpr hdetU
  have hcTinv : conjT c T⁻¹ = U⁻¹ := by
    have h1 : U * conjT c T⁻¹ = 1 := by
      rw [← hcT, ← conjT_mul, Matrix.nonsing_inv_mul _ huT, conjT_one]
    exact (Matrix.inv_eq_right_inv h1).symm
  have hcomm : U * T = T * U := by
    simp [hU, hT, mul_sub, sub_mul, mul_add, add_mul]; abel
  have hinv : T⁻¹ * U⁻¹ = U⁻¹ * T⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hcomm]
  have hdetγ : IsUnit (U * T⁻¹).det := by
    rw [Matrix.det_mul]; exact huU.mul (Matrix.isUnit_nonsing_inv_det T huT)
  refine ⟨Matrix.nonsingInvUnit (U * T⁻¹) hdetγ, ?_, rfl⟩
  show (U * T⁻¹) * conjT c (U * T⁻¹) = 1
  rw [conjT_mul, hcTinv, hcU, Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹, hinv, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huU, Matrix.one_mul, Matrix.nonsing_inv_mul _ huT]

end GlobalTheory.CayleyRat
end
