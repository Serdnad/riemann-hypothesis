module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Summand
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle005
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle002
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle016
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle015
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle022
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle012
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle013
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle017
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle024
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem UpperTheory.polynomial_identity_coefficients_zero {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (v : Fin n → M)
    (h : ∀ u : ℂ, ∑ i : Fin n, u ^ (n - (i + 1)) • v i = 0) (i : Fin n) : v i = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hp : (∑ j : Fin n, Polynomial.monomial (n - (j + 1)) (f (v j)) : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro u
    have := congrArg f (h u)

    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (n - (i + 1))) hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg]
    intro e
    apply hj
    have := j.2
    have := i.2
    exact Fin.ext (by omega)
  · simp

private theorem UpperTheory.polynomial_coefficients_compare {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (a : ℕ → M) (b : Fin n → M)
    (h : ∀ u : ℂ, ∑ i ∈ Finset.range (n + 1), u ^ (n - i) • a i = u ^ n • a 0 + ∑ i : Fin n, u ^ (n - (i + 1)) • b i)
    (i : Fin n) : a (i + 1) = b i := by
  rw [← sub_eq_zero]
  refine UpperTheory.polynomial_identity_coefficients_zero (fun i : Fin n => a (i + 1) - b i) (fun u => ?_) i
  have := h u
  rw [Finset.sum_range_succ', add_comm, Nat.sub_zero, add_right_inj,
    ← Fin.sum_univ_eq_sum_range (fun i => u ^ (n - (i + 1)) • a (i + 1)) n] at this
  simp only [smul_sub, Finset.sum_sub_distrib, this, sub_self]

theorem UpperTheory.zC_succ_eq_and_envelopingAction_compatible :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
          (∀ (τ : E →+* ℂ) (i : Fin n), UpperTheory.ConvolutionTheory.BW.zC E n τ (i + 1) = zc τ i) ∧
          ∀ (u : UC E n) (φ : GlobalTheory.CuspRep.Sm E n), (UpperTheory.V.Cm.uC E n u φ).1 = (uAct u (UpperTheory.V.Cm.smEq E n φ)).1 := by
  intro E _ _ _ n
  refine ⟨fun τ i => ?_, fun u φ => ?_⟩
  · obtain ⟨h0, h1⟩ := UpperTheory.ConvolutionTheory.BW.zSpec E n τ
    refine UpperTheory.polynomial_coefficients_compare (M := UC E n) (UpperTheory.ConvolutionTheory.BW.zC E n τ) (zc τ) (fun u => ?_) i
    rw [h0]
    exact (h1 u).symm.trans ((UpperTheory.ConvolutionTheory.Dp.capZc E n τ).2 u)
  · induction u using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul c x =>
      have e : uAct (TensorProduct.tmul ℝ c x : UC E n) = c • uAction x :=
        (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (uAction x)).symm
      rw [UpperTheory.V.Cm.uC_tmul, e]
      rfl
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, ha, hb]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_multiplicative_of_prime_power_values :
    ∀ M : H.P ℚ → ℕ → ℂ, (∀ v, M v 0 = 1) → ∃ μ : ℕ → ℂ, μ 1 = 1 ∧
          (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → μ (m * n) = μ m * μ n) ∧
          ∀ (v : H.P ℚ) (k : ℕ), μ (normV v ^ k) = M v k := by
  intro M hM
  obtain ⟨hp, -, hinj, -⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  let f : ℕ → ℕ → ℂ := fun p k =>
    if h : ∃ v : H.P ℚ, normV v = p then M h.choose k else 1
  have hf : ∀ (v : H.P ℚ) (k : ℕ), f (normV v) k = M v k := by
    intro v k
    have h : ∃ w : H.P ℚ, normV w = normV v := ⟨v, rfl⟩
    have h2 : h.choose = v := hinj _ _ h.choose_spec
    simp only [f]
    rw [dite_eq_left h, h2]
  refine ⟨fun n => n.factorization.prod f, by simp, ?_, ?_⟩
  · intro m n hm hn hmn
    show (m * n).factorization.prod f = m.factorization.prod f * n.factorization.prod f
    rw [Nat.factorization_mul hm.ne' hn.ne']
    exact Finsupp.prod_add_index_of_disjoint
      (by simpa using hmn.disjoint_primeFactors) f
  · intro v k
    show (normV v ^ k).factorization.prod f = M v k
    rw [(hp v).factorization_pow, Finsupp.prod_single_index (by rw [hf, hM]), hf]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem sc_val {R : Type} [CommRing R] (z : Rˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z).val = Matrix.diagonal fun _ => (z : R) := rfl

private theorem aE_nU (y : (A ℚ)ˣ) (b : A ℚ) :
    aE y * gl (nU b) = gl (nU ((y : A ℚ) * b)) * aE y := by
  refine Units.ext ?_
  ext i j
  rw [Units.val_mul, Units.val_mul, gl_val, gl_val]
  fin_cases i <;> fin_cases j <;> simp [aE, nU, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem aE_mD (y ζ : (A ℚ)ˣ) :
    aE y * gl (mD ζ) = Matrix.GeneralLinearGroup.scalar (Fin 2) ζ⁻¹ * aE (y * ζ ^ 2) := by
  refine Units.ext ?_
  ext i j
  rw [Units.val_mul, Units.val_mul, gl_val, sc_val]
  have hz : ((ζ⁻¹ : (A ℚ)ˣ) : A ℚ) * (ζ : A ℚ) = 1 := Units.inv_mul ζ
  fin_cases i <;> fin_cases j <;> simp [aE, mD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  linear_combination (-(y : A ℚ) * (ζ : A ℚ)) * hz

private theorem em_nU {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (x : A ℚ) :
    em E (gl (nU x)) = nE D ![x, 0] := by
  refine Units.ext ?_
  ext i j
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.em, nE, Matrix.GeneralLinearGroup.map_apply, gl_val]
  fin_cases i <;> fin_cases j <;> simp [nU, Dat.mkE]

private theorem em_sc {E : Type} [Field E] [NumberField E] (z : (A ℚ)ˣ) :
    em E (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E z) := by
  refine Units.ext ?_
  ext i j
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply, sc_val, coe_ideleEmbedding]
  by_cases e : i = j <;> simp [e, Matrix.diagonal]

private theorem Wo_lev {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} {N : ℕ}
    (hl : ∀ k, Lev N k → ∀ g, φ (g * em E k) = φ g) {κ : GL (Fin 2) (A ℚ)} (hκ : Lev N κ) (h : GL (Fin 2) (A E)) :
    Wo D φ (h * em E κ) = Wo D φ h := by
  unfold Wo
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only []
  rw [← mul_assoc, hl κ hκ]

theorem UpperTheory.whittaker_diagTorus_mul_iwasawa_eq :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (N : ℕ), (∀ k, Lev N k → ∀ g, φ (g * em E k) = φ g) → ∀ (y ζ : (A ℚ)ˣ) (b : A ℚ) (r κ : GL (Fin 2) (A ℚ)), Lev N κ →
          Wo D φ (em E (aE y * (gl (nU b) * gl (mD ζ) * r * κ))) = ((ω.1 ζ⁻¹ : ℂˣ) : ℂ) ^ 2 * Wo D φ (em E (aE (y * ζ ^ 2) * r)) := by
  intro E _ _ D ω φ hφ N hl y ζ b r κ hκ
  obtain ⟨-, -, hn, hz⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hφ
  have e : aE y * (gl (nU b) * gl (mD ζ) * r * κ) =
      gl (nU ((y : A ℚ) * b)) * (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ⁻¹ * (aE (y * ζ ^ 2) * r)) * κ := by
    calc aE y * (gl (nU b) * gl (mD ζ) * r * κ) = (aE y * gl (nU b)) * gl (mD ζ) * r * κ := by
          simp only [mul_assoc]
      _ = gl (nU ((y : A ℚ) * b)) * (aE y * gl (mD ζ)) * r * κ := by
          rw [aE_nU]; simp only [mul_assoc]
      _ = _ := by rw [aE_mD]; simp only [mul_assoc]
  have hN : ideleNorm ℚ E (ideleEmbedding ℚ E ζ⁻¹) = ζ⁻¹ ^ 2 := by
    rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  rw [e, map_mul, Wo_lev D hl hκ, map_mul, map_mul, em_nU D, em_sc, hn, hz, hN, map_pow]
  simp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) (z : (A E)ˣ)
    (h : (z : A E) = AdeleBaseChange.adeleMap ℚ E (y : A ℚ)) : em E (aE y) = aE z := by
  apply Units.ext
  ext i j
  rw [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [aE, h]

private theorem cp_sg_ne {E : Type} [Field E] [NumberField E] {w w' : H.P E} (hne : w ≠ w') (x : H.Kv w') :
    H.cp w (H.sg w' x) = 0 := by
  have h := ((H.sgLaws E w').2.2.2.2.2.2.2.1 x).2 w hne
  show (H.sg w' x).2 w = 0
  exact h

private theorem KAt_aE {E : Type} [Field E] [NumberField E] {w w' : H.P E} (hne : w ≠ w') (x : (H.Kv w')ˣ)
    (g : GL (Fin 2) (A E)) (hg : H.KAt w g) : H.KAt w (aE (H.idl w' x) * g) := by
  have h1 : Matrix.GeneralLinearGroup.map (H.cp w) (aE (H.idl w' x)) = 1 := by
    rw [← (H.lcLaws E w').2.2.2.1 x]
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, (H.sgLaws E w').2.2.2.2.1, map_add (f := _), cp_sg_ne hne]
    fin_cases i <;> fin_cases j <;> simp
  unfold H.KAt at hg ⊢
  rw [map_mul, h1, one_mul]
  exact hg

theorem UpperTheory.exists_whittaker_heckeEigenvalues_at_split_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
          CenN P ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ) φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∀ v : H.P ℚ, ¬ Bad N v → ∀ w w' : H.P E, w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') →
          ∃ m : ℕ → ℂ, m 0 = 1 ∧
            (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧
            ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) =
              PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := by
  intro E _ _ _ D P ω χ _ hχω L N φ hA hG a hIs v hv w w' hne hw hw' hS hS' hall
  obtain ⟨-, B, hsat, hEig⟩ := hG.fix w (by rw [hw]; exact hv)
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w B).1 hsat))
  obtain ⟨-, B', hsat', hEig'⟩ := hG.fix w' (by rw [hw']; exact hv)
  obtain ⟨α', β', rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w' B').1 hsat'))
  obtain ⟨-, -, hleft, -⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hA
  have hEw := UpperTheory.eigAt_cmDatumOperator_of_eigAt E D φ w _ hA.cont hEig
  have hEw' := UpperTheory.eigAt_cmDatumOperator_of_eigAt E D φ w' _ hA.cont hEig'
  obtain ⟨χw, hχ, hχe⟩ := UpperTheory.exists_localCharacter_of_split_pair_rat E D v w w' hne hw hw' hS hS' hall (hG.pl v hv)
  obtain ⟨χw', hχ', hχe'⟩ := UpperTheory.exists_localCharacter_of_split_pair_rat E D v w' w hne.symm hw' hw hS' hS
    (fun w'' h => (hall w'' h).symm) (hG.pl v hv)
  have hnl : ∀ b h, Wo D φ (H.lc w (H.nL b) * h) = χw b * Wo D φ h := fun b h => by
    obtain ⟨u, t, e1, e2⟩ := hχe b
    rw [(H.lcLaws E w).1, e1, ← e2]
    exact hleft ![u, t] h
  have hnl' : ∀ b h, Wo D φ (H.lc w' (H.nL b) * h) = χw' b * Wo D φ h := fun b h => by
    obtain ⟨u, t, e1, e2⟩ := hχe' b
    rw [(H.lcLaws E w').1, e1, ← e2]
    exact hleft ![u, t] h
  obtain ⟨ϖ₁, ϖ₂, hϖ₁, hϖ₂, hz⟩ := UpperTheory.ideleEmbedding_uniformizer_of_split_place_pair E D v w w' hne hw hw' hS hS' hall
    (atFin v (unif v)) (unif_spec v)
  have hz' : ideleEmbedding ℚ E (pv v) = H.idl w ϖ₁ * H.idl w' ϖ₂ := hz
  have hem : ∀ k : ℕ, em E (aE (pv v ^ k)) = aE (H.idl w ϖ₁ ^ k) * aE (H.idl w' ϖ₂ ^ k) := fun k => by
    rw [← UpperTheory.ConvolutionTheory.R2.aE_mul, ← mul_pow, ← hz']
    refine em_aE _ _ ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]
    rfl
  have hnv : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  have hqv : (normV v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hqw : H.q w = (normV v : ℂ) := by
    have : H.q w = (normV w : ℂ) := by simp [H.q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [this, hS.1]
  have hqw' : H.q w' = (normV v : ℂ) := by
    have : H.q w' = (normV w' : ℂ) := by simp [H.q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [this, hS'.1]
  set s : ℂ := (normV v : ℂ) ^ (1 / 2 : ℂ) with hs
  have hss : s * s = (normV v : ℂ) := by
    rw [hs, ← Complex.cpow_add _ _ hqv]
    norm_num
  have hs0 : s ≠ 0 := fun h => hqv (by rw [← hss, h, zero_mul])
  refine ⟨fun k => ((s ^ k)⁻¹ * (s ^ k)⁻¹) * (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) *
      (∑ i ∈ Finset.range (k + 1), (α' : ℂ) ^ i * (β' : ℂ) ^ (k - i)), by simp,
    fun k g hg => ?_, ?_⟩
  · have e : H.idl w' ϖ₂ ^ k = H.idl w' (ϖ₂ ^ k) := (map_pow _ _ _).symm
    have hK : H.KAt w (aE (H.idl w' ϖ₂ ^ k) * g) := by
      rw [e]
      exact KAt_aE hne _ g (hg w hw)
    have h1 := UpperTheory.eigenform_shintani_formula_at_place E w ϖ₁ hϖ₁ χw hχ α β _ hEw hnl _ hK k
    have h2 := UpperTheory.eigenform_shintani_formula_at_place E w' ϖ₂ hϖ₂ χw' hχ' α' β' _ hEw' hnl' g (hg w' hw') k
    rw [hqw] at h1
    rw [hqw'] at h2
    rw [hem, mul_assoc]
    have ht : s ^ k ≠ 0 := pow_ne_zero k hs0
    beta_reduce
    field_simp
    linear_combination s ^ k * h1 + (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) * h2
  · rintro ⟨h, hh⟩
    obtain ⟨h₁, hh₁⟩ : ∃ h₁, φ h₁ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hh
      simp [Wo, hcon]
    set c : ℂ := ((χ.val v : ℂˣ) : ℂ) with hc
    have hprod : (α : ℂ) * β * α' * β' * c ^ 2 = 1 := by
      have e1 := UpperTheory.eigenform_central_uniformizer_eq_satake_product E w ϖ₁ hϖ₁ α β φ hEig (Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl w' ϖ₂) * h₁)
      have e2 := UpperTheory.eigenform_central_uniformizer_eq_satake_product E w' ϖ₂ hϖ₂ α' β' φ hEig' h₁
      have e3 := hA.cen (ideleEmbedding ℚ E (pv v)) h₁
      rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin, hz', map_mul, mul_assoc, e1, e2] at e3
      have e4 : ((ω.1 (pv v) : ℂˣ) : ℂ) ^ 2 = (α : ℂ) * β * α' * β' := by
        have : ((α : ℂ) * β * α' * β' - ((ω.1 (pv v) : ℂˣ) : ℂ) ^ 2) * φ h₁ = 0 := by
          rw [map_pow, Units.val_pow_eq_pow_val] at e3
          linear_combination e3
        rcases mul_eq_zero.1 this with h0 | h0
        · linear_combination -h0
        · exact absurd h0 hh₁
      have e5 := congrArg (fun u : ℂˣ => (u : ℂ)) (hχω (pv v))
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one] at e5
      have e6 : c = ((χ.1 (pv v) : ℂˣ) : ℂ) := rfl
      rw [e6, ← e4]
      linear_combination e5
    have hsp := hIs.split v hv w w' hne hw hw' α β α' β' hsat hsat'
    have h2 := UpperTheory.rankinSelberg_local_generating_series_identity α β α' β' c
    rw [hprod, map_one, one_mul] at h2
    simp only [Units.val_mul, ← hc] at hsp
    have h3 : (PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * c ^ k *
        (((s ^ k)⁻¹ * (s ^ k)⁻¹) * (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) *
          (∑ i ∈ Finset.range (k + 1), (α' : ℂ) ^ i * (β' : ℂ) ^ (k - i)))) =
        PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) *
          (∑ i ∈ Finset.range (k + 1), (α' : ℂ) ^ i * (β' : ℂ) ^ (k - i)) := by
      congr 1
      funext k
      have ht : s ^ k ≠ 0 := pow_ne_zero k hs0
      have hp : ((normV v ^ k : ℕ) : ℂ) = s ^ k * s ^ k := by
        rw [Nat.cast_pow, ← hss, mul_pow]
      rw [hp]
      field_simp
    rw [h3]
    linear_combination (PowerSeries.mk fun k => a (normV v ^ k)) * (-1 : PowerSeries ℂ) * h2 +
      (PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) *
          (∑ i ∈ Finset.range (k + 1), (α' : ℂ) ^ i * (β' : ℂ) ^ (k - i))) * hsp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.unfoldedIntegrand_measurable_integrable_of_re_gt_four :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ s : ℂ, 4 < s.re →
        Measurable (Un.Hh D χ φ Φ s) ∧ Integrable (Un.Hh D χ φ Φ s) ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) := by
  intro E _ _ D ω χ φ hA hU hχ M₀ Φ hΦ s hs
  haveI := M₀.prob
  have hχn : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    have h := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, hU a, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  have hχe : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ₑ = 1 := by
    intro a
    rw [← ofReal_norm, hχn a, ENNReal.ofReal_one]
  have hcn : ∀ (y : IdeleGroup ℚ) (w : ℂ), ‖((ab y : ℝ) : ℂ) ^ w‖ₑ = ENNReal.ofReal (ab y ^ w.re) := by
    intro y w
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos (M.ab_pos y)]
  have hW := UpperTheory.measurable_whittaker_idele_diagTorus_mul E D ω φ hA
  have hχm : Measurable fun y : IdeleGroup ℚ => ((χ.1 y : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp χ.2.1).measurable
  have habm : Measurable fun y : IdeleGroup ℚ => ab y := M.continuous_ab.measurable
  have hΦc : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * row p.2 j :=
    (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
      (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
  have hΦm := hΦc.measurable
  have hcp : ∀ w : ℂ, Measurable fun y : IdeleGroup ℚ => ((ab y : ℝ) : ℂ) ^ w := fun w =>
    (Complex.measurable_ofReal.comp habm).pow_const w
  have hrp : ∀ x : ℝ, Measurable fun y : IdeleGroup ℚ => ENNReal.ofReal (ab y ^ x) := fun x =>
    (habm.pow_const x).ennreal_ofReal
  have hm : Measurable (Un.Hh D χ φ Φ s) :=
    ((((hW.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
      (hχm.comp measurable_fst)).mul ((hcp _).comp measurable_fst))).mul
      ((hΦm.comp measurable_snd).mul ((hcp _).comp (measurable_fst.comp measurable_snd)))
  refine ⟨hm, hm.aestronglyMeasurable, ?_⟩
  obtain ⟨C₁, hC₁⟩ := UpperTheory.whittaker_lintegral_abs_pow_bounded_on_maximalCompact E D ω φ hA (s.re - 1) (by linarith)
  obtain ⟨C₂, hC₂⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ (2 * s.re) (by linarith)
  let Aa : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Wo D φ (em E (aE p.1 * gl p.2))‖ₑ * ENNReal.ofReal (ab p.1 ^ (s.re - 1))
  let Bb : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 * s.re))
  have hAm : Measurable Aa := hW.enorm.mul ((hrp _).comp measurable_fst)
  have hBm : Measurable Bb := hΦm.enorm.mul ((hrp _).comp measurable_fst)
  have hnorm : ∀ q, ‖Un.Hh D χ φ Φ s q‖ₑ = Aa (q.1, q.2.2) * Bb q.2 := by
    intro q
    have e1 : (s - 1).re = s.re - 1 := by simp
    have e2 : (2 * s).re = 2 * s.re := by simp
    simp only [Un.Hh, enorm_mul, hχe, mul_one, hcn, e1, e2, Aa, Bb]
  have hFm : Measurable fun q : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ => Aa (q.1, q.2.2) * Bb q.2 :=
    (hAm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul (hBm.comp measurable_snd)
  have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
    rw [ae_iff]
    exact M₀.supp
  show ∫⁻ q, ‖Un.Hh D χ φ Φ s q‖ₑ ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) < ⊤
  simp_rw [hnorm]
  rw [lintegral_prod_symm _ hFm.aemeasurable, lintegral_prod_symm _ hFm.lintegral_prod_left'.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun _ => (C₁ * C₂ : ℝ≥0∞)) (hae.mono fun k hk => ?_)) ?_
  · have h1 : ∀ z : IdeleGroup ℚ, ∫⁻ y : IdeleGroup ℚ, Aa (y, k) * Bb (z, k) ∂(ideleMeasure ℚ) ≤ C₁ * Bb (z, k) := by
      intro z
      have hAk : Measurable fun y : IdeleGroup ℚ => Aa (y, k) := hAm.comp measurable_prodMk_right
      rw [lintegral_mul_const _ hAk]
      exact mul_le_mul_left (hC₁ k hk) _
    refine (lintegral_mono h1).trans ?_
    have hBk : Measurable fun z : IdeleGroup ℚ => Bb (z, k) := hBm.comp measurable_prodMk_right
    rw [lintegral_const_mul _ hBk]
    exact mul_le_mul_right (hC₂ k hk) _
  · rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.ideleOfNat_mul_and_prime_pow :
    (∀ m n : ℕ, 0 < m → 0 < n → pin (m * n) = pin m * pin n) ∧ (∀ (v : H.P ℚ) (k : ℕ), pin (normV v ^ k) = pv v ^ k) := by
  obtain ⟨hp, -, hinj, -⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  have hfin : ∀ n : ℕ, (Function.mulSupport fun v : H.P ℚ => pv v ^ (n.factorization (normV v))).Finite := by
    intro n
    have h1 : ((fun v : H.P ℚ => normV v) ⁻¹' (n.factorization.support : Set ℕ)).Finite :=
      Set.Finite.preimage (fun a _ b _ h => hinj a b h) (Finset.finite_toSet _)
    refine h1.subset fun v hv => ?_
    simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hv (by simp only [h0, pow_zero])
  refine ⟨fun m n hm hn => ?_, fun v k => ?_⟩
  · unfold pin
    rw [← finprod_mul_distrib (hfin m) (hfin n), Nat.factorization_mul hm.ne' hn.ne']
    exact finprod_congr fun v => by rw [Finsupp.add_apply, pow_add]
  · unfold pin
    rw [(hp v).factorization_pow, finprod_eq_single _ v]
    · rw [Finsupp.single_eq_same]
    · intro w hw
      rw [Finsupp.single_eq_of_ne (fun h => hw (hinj _ _ h)), pow_zero]
end
