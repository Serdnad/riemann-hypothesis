module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle181
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle239
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle210
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CasFamily

theorem sum_squares_eq {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (X Y : Fin a → Fin a → A) :
    ∑ i, ∑ j, ((X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
        ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i))) =
      (8 : ℂ) • (Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
        Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j))) := by
  have h1 : ∀ i j, (X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
      ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i)) =
      (2 : ℂ) • (X i j * X j i) + (2 : ℂ) • (X j i * X i j) -
        ((2 : ℂ) • (Y i j * Y j i) + (2 : ℂ) • (Y j i * Y i j)) := by
    intro i j
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    match_scalars <;> ring
  have h2 : ∀ i j, ((1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i - Complex.I • Y j i)) +
      ((1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i + Complex.I • Y j i)) =
      (1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i) := by
    intro i j
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, smul_smul]
    match_scalars <;> ring_nf <;> simp <;> norm_num
  have hX : ∑ i, ∑ j, X j i * X i j = ∑ i, ∑ j, X i j * X j i := Finset.sum_comm
  have hY : ∑ i, ∑ j, Y j i * Y i j = ∑ i, ∑ j, Y i j * Y j i := Finset.sum_comm
  have hc : Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
      Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) =
      ∑ i, ∑ j, ((1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i)) := by
    simp only [Formalism.REAL.Cas, ← Finset.sum_add_distrib, h2]
  rw [hc]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hX, hY]
  match_scalars <;> norm_num

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def sgl (i j : Fin a) : Cinf E →ₗ[ℝ] Lie E a :=
  (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))

def eW (w : InfinitePlace E) : Cinf E := atEmb w.embedding 1

def fW (w : InfinitePlace E) : Cinf E := atEmb w.embedding Complex.I

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
open Classical in
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_atEmb (w : InfinitePlace E) (z : ℂ) :
    star (atEmb w.embedding z) = atEmb w.embedding (starRingEnd ℂ z) := by
  classical
  funext v
  rw [Pi.star_apply, atEmb_embedding_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_eW (w : InfinitePlace E) : star (eW w) = eW w := by
  simp [eW, star_atEmb]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_fW (w : InfinitePlace E) : star (fW w) = -fW w := by
  classical
  funext v
  simp only [fW, star_atEmb, Pi.neg_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [_root_.NumberField.IsTotallyComplex E] in
theorem sum_atEmb (x : Cinf E) : x = ∑ w, ((x w).re • eW w + (x w).im • fW w) := by
  classical
  have e : ∀ w, (x w).re • eW w + (x w).im • fW w = atEmb w.embedding (x w) := fun w =>
    (atEmb_eq _ _).symm
  simp only [e]
  funext v
  simp [Finset.sum_apply, atEmb_embedding_apply]

def famZ : InfinitePlace E × Fin a × Fin a × Bool × Bool → Lie E a
  | (w, i, j, false, false) => sgl i j (eW w) + sgl j i (eW w)
  | (w, i, j, false, true) => sgl i j (eW w) - sgl j i (eW w)
  | (w, i, j, true, false) => sgl i j (fW w) - sgl j i (fW w)
  | (w, i, j, true, true) => sgl i j (fW w) + sgl j i (fW w)

theorem span_famZ : Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) = ⊤ := by
  set S := Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) with hS
  have hz : ∀ k, famZ (E := E) (a := a) k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hE : ∀ w i j, sgl (E := E) (a := a) i j (eW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (eW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, false, false) + famZ (w, i, j, false, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (eW w) + sgl j i (eW w)) + (sgl i j (eW w) - sgl j i (eW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hF : ∀ w i j, sgl (E := E) (a := a) i j (fW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (fW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, true, false) + famZ (w, i, j, true, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (fW w) - sgl j i (fW w)) + (sgl i j (fW w) + sgl j i (fW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hx : ∀ i j (x : Cinf E), sgl (a := a) i j x ∈ S := fun i j x => by

    rw [sum_atEmb x, map_sum]
    refine S.sum_mem fun w _ => ?_
    rw [map_add (f := _), map_smul, map_smul]
    exact S.add_mem (S.smul_mem _ (hE w i j)) (S.smul_mem _ (hF w i j))
  refine eq_top_iff.2 fun L _ => ?_
  have e : L = ∑ i, ∑ j, sgl i j (L i j) := Matrix.matrix_eq_sum_single (Matrix.of L)
  rw [e]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hx i j _

theorem conjTranspose_sgl (i j : Fin a) (x : Cinf E) :
    (Matrix.of (sgl i j x))ᴴ = Matrix.of (sgl j i (star x)) :=
  Matrix.conjTranspose_single i j x

theorem skew_famZ (k : InfinitePlace E × Fin a × Fin a × Bool × Bool) (hk : k.2.2.2.2 = true) :
    (Matrix.of (famZ k))ᴴ = -(Matrix.of (famZ k)) := by
  obtain ⟨w, i, j, b, c⟩ := k
  obtain rfl : c = true := hk
  cases b
  · change (Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))ᴴ =
      -(Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))
    rw [Matrix.conjTranspose_sub, conjTranspose_sgl, conjTranspose_sgl, star_eW, neg_sub]
  · change (Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))ᴴ =
      -(Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))
    have hn : ∀ i j : Fin a, Matrix.of (sgl i j (-fW w)) = -Matrix.of (sgl i j (fW w)) := fun i j => by
      rw [map_neg]; rfl
    rw [Matrix.conjTranspose_add, conjTranspose_sgl, conjTranspose_sgl, star_fW, hn, hn, neg_add, add_comm]

theorem Eop_embedding (w : InfinitePlace E) (i j : Fin a) :
    Eop w.embedding i j = (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w)) := rfl

theorem Eop_conjugate (w : InfinitePlace E) (i j : Fin a) :
    Eop (ComplexEmbedding.conjugate w.embedding) i j =
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w)) := by
  have h : atEmb w.embedding (-Complex.I) = -fW w := by
    rw [atEmb_eq]; simp [fW]
  rw [Eop, atEmb_conj, atEmb_conj, map_one, Complex.conj_I, h, map_neg, smul_neg, sub_neg_eq_add]
  rfl

theorem sum_famZ [DecidableEq (InfinitePlace E)] :
    ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ,
        lie E a (famZ k) * lie E a (famZ k) -
      ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true,
        lie E a (famZ k) * lie E a (famZ k) =
    ∑ w : InfinitePlace E, (8 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
      Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have e : ∀ f : InfinitePlace E × Fin a × Fin a × Bool × Bool → Module.End ℂ (Sm E a),
      ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ, f k -
        ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true, f k =
      ∑ k, if k.2.2.2.2 = true then -f k else f k := fun f => by
    rw [Finset.compl_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k.2.2.2.2 = true <;> simp [h]
  rw [e]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h := sum_squares_eq (fun i j : Fin a => lieS E a i j (eW w)) (fun i j => lieS E a i j (fW w))
  have c1 : Formalism.REAL.Cas (Eop (a := a) w.embedding) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w))) := rfl
  have c2 : Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding)) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w))) :=
    congrArg _ (funext fun i => funext fun j => Eop_conjugate w i j)
  rw [c1, c2, ← h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have f1 : lie E a (famZ (w, i, j, false, false)) = lieS E a i j (eW w) + lieS E a j i (eW w) := map_add _ _ _
  have f2 : lie E a (famZ (w, i, j, false, true)) = lieS E a i j (eW w) - lieS E a j i (eW w) := map_sub _ _ _
  have f3 : lie E a (famZ (w, i, j, true, false)) = lieS E a i j (fW w) - lieS E a j i (fW w) := map_sub _ _ _
  have f4 : lie E a (famZ (w, i, j, true, true)) = lieS E a i j (fW w) + lieS E a j i (fW w) := map_add _ _ _
  simp only [if_true, Bool.false_eq_true, if_false, f1, f2, f3, f4]
  abel

theorem exists_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Z : ι → GlobalTheory.CuspRep.Lie E a) (K : Finset ι), Submodule.span ℝ (Set.range Z) = ⊤ ∧ (∀ κ ∈ K, (Matrix.of (Z κ))ᴴ = -(Matrix.of (Z κ))) ∧ (∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ)) ∈ Zalg E a := by
  intro E _ _ _ a
  have : DecidableEq (InfinitePlace E) := Classical.decEq _
  refine ⟨InfinitePlace E × Fin a × Fin a × Bool × Bool, inferInstance, inferInstance, famZ,
    Finset.univ.filter fun k => k.2.2.2.2 = true, span_famZ, fun κ hκ => skew_famZ κ (Finset.mem_filter.1 hκ).2, ?_⟩
  rw [sum_famZ]
  exact Subalgebra.sum_mem _ fun w _ => Subalgebra.smul_mem _
    (Subalgebra.add_mem _ (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _) (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _)) _

end GlobalTheory.CompanionTheory.CasFamily
end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.LieCurve

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) : GL (Fin a) (Cinf E) where
  val := NormedSpace.exp (t • M)
  inv := NormedSpace.exp (-(t • M))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • M)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem expUnit_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    (expUnit E a M t).val = NormedSpace.exp (t • M) := rfl

theorem expUnit_inv_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    ((expUnit E a M t)⁻¹).val = NormedSpace.exp ((-t) • M) := by
  change NormedSpace.exp (-(t • M)) = _
  rw [neg_smul]

theorem hasDerivAt_exp (M : Matrix (Fin a) (Fin a) (Cinf E)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • M)) (NormedSpace.exp (t • M) * M) t := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) M t

theorem continuous_exp_smul (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun t : ℝ => NormedSpace.exp (t • M) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp E a M t).continuousAt

theorem continuous_expUnit (M : Matrix (Fin a) (Fin a) (Cinf E)) : Continuous (expUnit E a M) := by
  refine Units.continuous_iff.2 ⟨continuous_exp_smul E a M, ?_⟩
  exact ((continuous_exp_smul E a M).comp continuous_neg).congr fun t => (expUnit_inv_val E a M t).symm

theorem expUnit_zero (M : Matrix (Fin a) (Fin a) (Cinf E)) : expUnit E a M 0 = 1 := by
  ext1
  rw [expUnit_val, zero_smul, NormedSpace.exp_zero]
  rfl

theorem expUnit_add (M : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expUnit E a M (s + t) = expUnit E a M s * expUnit E a M t := by
  ext1
  rw [Units.val_mul, expUnit_val, expUnit_val, expUnit_val, add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left s).smul_right t)]

theorem expUnit_mem_unitary (M : Matrix (Fin a) (Fin a) (Cinf E)) (h : Mᴴ = -M) (t : ℝ) :
    (expUnit E a M t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  have e : star (NormedSpace.exp (t • M)) = NormedSpace.exp (-(t • M)) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, h]
    simp
  rw [Matrix.mem_unitaryGroup_iff, expUnit_val, e]
  exact (expUnit E a M t).val_inv

def toLieL : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.of.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem toLieL_apply (M : Matrix (Fin a) (Fin a) (Cinf E)) : toLieL E a M = Matrix.of.symm M := rfl

theorem hasDerivAt_toL (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t : ℝ => toL (expUnit E a M t).val) (Matrix.of.symm M) 0 := by
  have h := (toLieL E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp E a M 0)
  have e : toLieL E a (NormedSpace.exp ((0 : ℝ) • M) * M) = Matrix.of.symm M := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  exact h.congr_deriv e

end

theorem exists_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
      HasDerivAt (fun t => toL (c t).val) X 0 ∧
      ((Matrix.of X)ᴴ = -(Matrix.of X) → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) :=
  ⟨expUnit E a (Matrix.of X), continuous_expUnit E a _, expUnit_zero E a _, expUnit_add E a _,
    hasDerivAt_toL E a _, fun h t => expUnit_mem_unitary E a _ h t⟩

end GlobalTheory.CompanionTheory.LieCurve
end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.GrowthKernel

open GroundTheory.Global GroundTheory.Automorphic.Reduction AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth GlobalTheory.CompanionTheory.HCRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_aeval_lapOp_eq_zero_of_finite (φ : Sm E a)
    (hk : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)))
    (hz : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)))
    {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (hskew : ∀ i, ε i = -1 → b i ∈ archSkew E a) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (lapOp (⇑b)) P φ = 0 := by
  classical
  set Ω := omegaOp (E := E) (a := a) (⇑b) ε with hΩ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hWdef
  haveI : FiniteDimensional ℂ W := hk
  have hZ : Ω ∈ Zalg E a := by
    rw [hΩ, GlobalTheory.T.omega_operator_eq_casimir_sum E a d b ε hε horth]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun w _ => Subalgebra.add_mem _ ?_ ?_) _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
  set Vz := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hVz
  haveI : FiniteDimensional ℂ Vz := hz
  have hVs : ∀ w ∈ Vz, Ω w ∈ Vz := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Ω w ∈ Vz) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨Ω * z, Subalgebra.mul_mem _ hZ hz, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hφV : φ ∈ Vz := Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩
  obtain ⟨q, hqm, -, hq⟩ := AutomorphicForm.exists_monic_aeval_apply_eq_zero Ω Vz hVs hφV
  have hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Polynomial.aeval Ω q w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      have hcomm : ∀ m, cptRep E a k (Ω m) = Ω (cptRep E a k m) := fun m =>
        (congrArg (fun T : Module.End ℂ (Sm E a) => T m)
          (GlobalTheory.T.omega_operator_commutes_infinite_gl E a d b ε hε horth (Unitary.toUnits k))).symm
      have := AutomorphicForm.map_aeval_apply_of_intertwine (cptRep E a k) hcomm q φ
      rw [hq, map_zero] at this
      exact this.symm
    · rw [map_zero]
    · intro x y _ _ hx hy; rw [map_add (f := _), hx, hy, add_zero]
    · intro c x _ hx; rw [map_smul, hx, smul_zero]
  have hlap : Commute Ω (lapOp (⇑b)) := by
    simp only [lapOp, Commute, SemiconjBy]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Ω * liB (b i) = liB (b i) * Ω := omegaOp_comm_liB b ε hε horth (b i)
    rw [← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  have hTW : ∀ w ∈ W, (lapOp (⇑b) - Ω) w ∈ W := by
    intro w hw
    have e : (lapOp (E := E) (a := a) (⇑b) - Ω) w =
        ∑ i, ((1 : ℂ) - (ε i : ℂ)) • liB (b i) (liB (b i) w) := by
      simp only [hΩ, lapOp, omegaOp, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      module
    rw [e]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases hε i with h | h
    · simp [h]
    · refine W.smul_mem _ ?_
      have hs := mem_archSkew.1 (hskew i h)
      exact GlobalTheory.T.compact_span_finite_dim_stable E a φ (b i) hs hk _ (GlobalTheory.T.compact_span_finite_dim_stable E a φ (b i) hs hk _ hw)
  have hφW : φ ∈ W := by
    refine Submodule.subset_span ⟨1, ?_⟩
    change cptRep E a 1 φ = φ
    rw [map_one]
    rfl
  have hc : Commute Ω (lapOp (⇑b) - Ω) := by
    refine LinearMap.ext fun x => ?_
    have h2 := LinearMap.congr_fun hlap.eq x
    simp only [Module.End.mul_apply] at h2 ⊢
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h2]
  have hsum : Ω + (lapOp (⇑b) - Ω) = lapOp (⇑b) := LinearMap.ext fun x => by simp
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_monic_aeval_add Ω (lapOp (⇑b) - Ω) hc W hTW q hqm hqW hφW
  refine ⟨P, hP1, hP2, ?_⟩
  rwa [hsum] at hP3

theorem exists_kernel_of_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
      (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure],
      ∃ κ : AutomorphicForm.archGroup E a → ℂ, Continuous κ ∧ HasCompactSupport κ ∧
        ∀ g : GA E a, φ.1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * κ y ∂ν := by
  intro E _ _ _ a φ hk hz _ _ ν _
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := E) (n := a)
  obtain ⟨P, hm, hd, hP⟩ := exists_aeval_lapOp_eq_zero_of_finite φ hk hz b ε hε horth hskew
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra E a).exists_kernel_eq_conv_of_aeval_laplacian ν b P
    hm hd Filter.univ_mem
  refine ⟨κ, IsExpLieAlgebra.continuous_of_isSmoothFun hκs, hκc, fun g => ?_⟩
  have h1 := hκ (sliceL g (smL E a φ)) (by rw [← sliceL_aeval_lapOp, hP, map_zero, map_zero]) 1
  simpa [archSlice_apply, smL] using h1

end GlobalTheory.CompanionTheory.HCRep.GrowthKernel

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.compact_element_eigenvalues_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w) (s : Fin n → (w.adicCompletion E)ˣ), g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ → IsCompact (closure (Subgroup.zpowers g : Set H)) → ∀ i, Valued.v (s i : w.adicCompletion E) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | exact GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.nontrivial_infinite_place_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) := by
  first | exact @GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | exact GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twisted_centralizer_compact_part : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G), Continuous θ → ∀ (K I C : Subgroup G) (δ : G), IsCompact (K : Set G) → IsOpen (I : Set G) → IsCompact (C : Set G) → cptPart (twCent θ δ) = twCent θ δ ⊓ C → ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.CentOk.centraliser_hyps | exact GlobalTheory.CompanionTheory.CentOk.centraliser_hyps | (intros; apply GlobalTheory.CompanionTheory.CentOk.centraliser_hyps <;> assumption)
end
