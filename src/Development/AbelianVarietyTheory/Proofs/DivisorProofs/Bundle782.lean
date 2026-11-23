module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle746
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.Params
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockBlockDeg

theorem Jm_apply_of_ne {r s : ℕ} {c e : Ix r s} (h : c ≠ e) : Jm r s c e = 0 := by
  rcases c with c | c <;> rcases e with e | e <;>
    simp_all [Jm, Formalism.UG.Jpq]

theorem totalDegree_omAct_kron_le : ∀ (p q r s : ℕ) (E : Mat p q), IsKC E → ∀ (d : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → (omAct p q r s (Matrix.kroneckerMap (· * ·) E (Jm r s)) P).totalDegree ≤ d := by
  intro p q r s E hE d P hP
  rw [← mem_restrictTotalDegree] at hP ⊢
  refine GlobalTheory.FockPolGK.omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change E a b * Jm r s c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hE a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Jm_apply_of_ne hc, mul_zero]

end GlobalTheory.FockBlockDeg
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.lowestType_not_jointShape_smaller_pairs : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → ∀ μ', ¬ JointShape _ _ (al.length + de.length + t - i) (ga.length + be.length - i) (blattner (lamA al be ga de)) μ') ∧ (i ≤ al.length + de.length → i ≤ ga.length + be.length + t → ∀ μ', ¬ JointShape _ _ (al.length + de.length - i) (ga.length + be.length + t - i) (blattner (lamA al be ga de)) μ') ∧ ((¬ (∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2) ∨ ¬ (∃ a, lamA al be ga de a = -(((t : ℚ) + 1) / 2))) → i ≤ al.length + be.length → i ≤ ga.length + de.length → (∀ μ, ¬ JointShape (al.length + be.length - i) (ga.length + de.length - i) _ _ μ (blattner (lamA' t al be ga de))) ∧ ∀ μ, ¬ JointShape (al.length + be.length - i) (ga.length + de.length - i) _ _ μ (blattner (lamM' t al be ga de))) := by
  first | exact @GlobalTheory.LowestTypeDrop.lowestType_not_jointShape | exact GlobalTheory.LowestTypeDrop.lowestType_not_jointShape | (intros; apply GlobalTheory.LowestTypeDrop.lowestType_not_jointShape <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.FockOm
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem omE_form_and_degree : ∀ (p q r s : ℕ) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → (linePos l = linePos l' → omE l l' P ∈ homog (Ix p q × Ix r s) d) ∧ (linePos l = true → linePos l' = false → omE l l' P = X l * X l' * P) ∧ (linePos l = false → linePos l' = true → omE l l' P = - pderiv l (pderiv l' P)) := by
  intro p q r s l l' d P hP
  refine ⟨fun h => GlobalTheory.FockDeg.omE_mem_homog h hP, fun hl hl' => ?_, fun hl hl' => ?_⟩
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne, mul_assoc]
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne]

end GlobalTheory.FockOm
end
end

section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.CoefTorusWeight

theorem coeff_aeval_scale {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) F) m = (∏ v, c v ^ m v) * AddMonoidAlgebra.coeff F m := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : aeval (fun v => (C (c v) * X v : MvPolynomial σ K)) (monomial u a)
        = monomial u ((∏ v, c v ^ u v) * a) := by
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), monomial_eq,
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, algebraMap_eq, C_mul]
      ring
    rw [h, coeff_monomial, coeff_monomial]
    split_ifs with hu
    · rw [hu]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem coeff_actP_diag {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (t : ι → Fin n → Kˣ) (F : Pol K ι n) (m : (ι × Fin n × Fin n) →₀ ℕ) :
    AddMonoidAlgebra.coeff (actP lam (fun τ => diagGL K n (t τ)) F) m
      = detTwK lam (fun τ => diagGL K n (t τ)) *
        ((∏ v : ι × Fin n × Fin n, (t v.1 v.2.1 : K) ^ m v) * AddMonoidAlgebra.coeff F m) := by
  classical
  have h : trAct (fun τ => diagGL K n (t τ))
      = aeval (fun v : ι × Fin n × Fin n => (C (t v.1 v.2.1 : K) * X v : Pol K ι n)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, diagGL, Matrix.diagonal_transpose]
    rw [Finset.sum_eq_single v.2.1]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · simp
  rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, MvPolynomial.coeff_smul, smul_eq_mul, h,
    coeff_aeval_scale]

theorem detTwK_ne_zero {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) : detTwK lam h ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Units.ne_zero _

theorem weight_preserved (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (g : Module.End K (VV K lam))
    (hg : ∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) (v : VV K lam)
    (hv : ∀ m ∈ (v : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) :
    ∀ m ∈ ((g v : VV K lam) : Pol K ι n).support, ∀ τ a,
      ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a := by
  classical
  intro m hm τ0 a0
  let u : Kˣ := Units.mk0 (2 : K) two_ne_zero
  let t : ι → Fin n → Kˣ := fun τ a => if τ = τ0 ∧ a = a0 then u else 1
  have hprod : ∀ m : (ι × Fin n × Fin n) →₀ ℕ,
      (∏ v : ι × Fin n × Fin n, (t v.1 v.2.1 : K) ^ m v) = 2 ^ (∑ s : Fin n, m (τ0, a0, s)) := by
    intro m
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ0, Fintype.prod_prod_type,
      Finset.prod_eq_single a0, ← Finset.prod_pow_eq_pow_sum]
    · simp [t, u]
    · intro b _ hb
      simp [t, hb]
    · simp
    · intro b _ hb
      simp [t, hb]
    · simp
  set h : ι → GL (Fin n) K := fun τ => diagGL K n (t τ) with hh
  have hco : ∀ (w : VV K lam) (m : (ι × Fin n × Fin n) →₀ ℕ),
      AddMonoidAlgebra.coeff ((rhoK lam h w : VV K lam) : Pol K ι n) m
        = detTwK lam h * (2 ^ (∑ s : Fin n, m (τ0, a0, s)) * AddMonoidAlgebra.coeff (w : Pol K ι n) m) := by
    intro w m
    rw [← hprod]
    exact coeff_actP_diag lam t w m
  have h1 : rhoK lam h v = (detTwK lam h * 2 ^ (lam τ0).natW a0) • v := by
    apply Subtype.ext
    ext m'
    rw [hco, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]
    by_cases hm' : m' ∈ (v : Pol K ι n).support
    · rw [hv m' hm']
    · rw [notMem_support_iff.mp hm']
      simp
  have h2 := hg h v
  rw [h1, map_smul] at h2
  have h3 := congrArg (fun w : VV K lam => AddMonoidAlgebra.coeff (w : Pol K ι n) m) h2
  simp only [hco, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc] at h3
  have h4 := mul_right_cancel₀ (mem_support_iff.mp hm) (mul_left_cancel₀ (detTwK_ne_zero lam h) h3)
  have h5 : (2 : ℕ) ^ (lam τ0).natW a0 = 2 ^ (∑ s : Fin n, m (τ0, a0, s)) := by
    exact_mod_cast h4
  exact (Nat.pow_right_injective le_rfl h5).symm

end GlobalTheory.CoefTorusWeight
end
end

section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem multilinear_mem_span_of_mem_span {K ι M N : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (m : (ι → M) →ₘₗ[K] N) (S : ι → Set M) (f : ι → M)
    (hf : ∀ τ, f τ ∈ Submodule.span K (S τ)) :
    m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
  classical
  have key : ∀ (s : Finset ι) (f : ι → M), (∀ τ, f τ ∈ Submodule.span K (S τ)) →
      (∀ τ, τ ∉ s → f τ ∈ S τ) →
      m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f _ h
      exact Submodule.subset_span ⟨f, fun τ => h τ (Finset.notMem_empty τ), rfl⟩
    | insert a s ha ih =>
      intro f h1 h2
      have hle : Submodule.span K (S a) ≤
          (Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g}).comap
            (m.toLinearMap f a) := by
        rw [Submodule.span_le]
        intro x hx
        rw [SetLike.mem_coe, Submodule.mem_comap, MultilinearMap.toLinearMap_apply]
        apply ih
        · intro τ
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact Submodule.subset_span hx
          · rw [Function.update_of_ne hτ]
            exact h1 τ
        · intro τ hτs
          by_cases hτ : τ = a
          · subst hτ
            rw [Function.update_self]
            exact hx
          · rw [Function.update_of_ne hτ]
            exact h2 τ (by simp [hτ, hτs])
      have h := hle (h1 a)
      rw [Submodule.mem_comap, MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h
      exact h
  exact key Finset.univ f hf (fun τ h => absurd (Finset.mem_univ τ) h)

theorem coefSpace_le_span_pure_tensors (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K))
    (hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) :
    VV K lam ≤ Submodule.span K
      {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  classical
  let m : (ι → MvPolynomial (Fin n × Fin n) K) →ₘₗ[K]
      (MvPolynomial (ι × Fin n × Fin n) K) :=
    (MultilinearMap.mkPiAlgebra K ι (MvPolynomial (ι × Fin n × Fin n) K)).compLinearMap
      (fun τ => (Formalism.GradedWeylDivisibility.blockEmb K τ).toLinearMap)
  have hm : ∀ f, m f = ten f := fun f => rfl
  unfold VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩
  exact multilinear_mem_span_of_mem_span m S F (fun τ => hS τ (hF τ))

end GlobalTheory
end
end

section

noncomputable section

open IsDedekindDomain NumberField Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.AdeleIdem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_tmul_mem {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    (1 : E) ⊗ₜ[F] y ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)

theorem oToS_algebraMap (r : 𝓞 F) :
    ((oToS F E (algebraMap (𝓞 F) (𝓞 E) r) : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) := by
  rw [oToS_coe]
  have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap F E (algebraMap (𝓞 F) F r) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
    ← IsScalarTower.algebraMap_apply]

theorem resS_eq_zero (w : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hw : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal)
    {b : FiniteAdeleRing (𝓞 F) F} (hb : b ∈ intAd F) (hv : b v = 0) :
    resS F w ⟨_, one_tmul_mem hb⟩ = 0 := by
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F d hd0 b hb
  have ev : b v = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) d * y v := by
    rw [e]; rfl
  have hr : r ∈ v.asIdeal := by
    rw [hv] at ev
    have e1 : algebraMap (𝓞 F) (v.adicCompletion F) r = -(algebraMap (𝓞 F) (v.adicCompletion F) d * y v) :=
      eq_neg_of_add_eq_zero_left ev.symm
    have e2 := congrArg Valued.v e1
    rw [Valuation.map_neg, Valuation.map_mul, Formalism.UG.P.csApprox_val_int, Formalism.UG.P.csApprox_val_int] at e2
    rw [← v.intValuation_lt_one_iff_mem] at hd ⊢
    rw [e2]
    have hy1 : Valued.v (y v) ≤ 1 := hy v
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy1) hd
  have hz : ∀ x ∈ v.asIdeal, resS F w (oToS F E (algebraMap (𝓞 F) (𝓞 E) x)) = 0 := by
    intro x hx
    rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hw] at hx
    exact hx
  have key : (⟨_, one_tmul_mem hb⟩ : Formalism.L2.Herm.intAf F E) =
      oToS F E (algebraMap (𝓞 F) (𝓞 E) r) + oToS F E (algebraMap (𝓞 F) (𝓞 E) d) * ⟨_, one_tmul_mem hy⟩ := by
    apply Subtype.ext
    rw [Subring.coe_add, Subring.coe_mul, oToS_algebraMap, oToS_algebraMap]
    show (1 : E) ⊗ₜ[F] b = _ + _ * (1 : E) ⊗ₜ[F] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
  rw [key, map_add (f := _), map_mul, hz r hr, hz d hd, zero_mul, add_zero]


open Classical in
def ind (S : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if v ∈ S then 1 else 0) ∈ v.adicCompletionIntegers F
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
theorem ind_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    ind S v = if v ∈ S then 1 else 0 := rfl

theorem ind_mem (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S ∈ intAd F := by
  intro v
  show ind S v ∈ v.adicCompletionIntegers F
  rw [ind_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

end GlobalTheory.AdeleIdem
end
end

section

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

theorem eq_one_off_mul {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (M N : Matrix (Fin r) (Fin r) F)
    (hM : ∀ i j, ¬ (S i ∧ S j) → M i j = (1 : Matrix (Fin r) (Fin r) F) i j)
    (hN : ∀ i j, ¬ (S i ∧ S j) → N i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    ∀ i j, ¬ (S i ∧ S j) → (M * N) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  intro i j hij
  by_cases hi : S i
  · have hj : ¬ S j := fun h => hij ⟨hi, h⟩
    have e : (M * N) i j = (M * (1 : Matrix (Fin r) (Fin r) F)) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [hN a j fun h => hj h.2]
    rw [e, Matrix.mul_one, hM i j hij]
  · have e : (M * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [hM i a fun h => hi h.1]
    rw [e, Matrix.one_mul, hN i j hij]

theorem exists_gl_vecMul_eq_single_of_ne {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (c : Fin r) (hc : S c)
    (l : Fin r → F) (hl : l c ≠ 0) (hS : ∀ i, l i ≠ 0 → S i) :
    ∃ h : GL (Fin r) F, (∀ i j, ¬ (S i ∧ S j) → (h : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) ∧
      Matrix.vecMul l (h : Matrix (Fin r) (Fin r) F) = Pi.single c 1 := by
  set e : Fin r → F := Pi.single c 1 with he
  set A : Matrix (Fin r) (Fin r) F := vecMulVec e (l - e) with hA
  have hd : (l - e) ⬝ᵥ e = l c - 1 := by simp [he]
  have hAA : A * A = (l c - 1) • A := by
    rw [hA, vecMulVec_mul_vecMulVec, hd, vecMulVec_smul]
  have h1 : (1 - (l c)⁻¹ • A) * (1 + A) = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc, mul_add, mul_one, hAA]
    have : A + (l c - 1) • A = l c • A := by rw [sub_smul, one_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hl, one_smul]; abel
  refine ⟨⟨1 - (l c)⁻¹ • A, 1 + A, h1, mul_eq_one_comm.mp h1⟩, ?_, ?_⟩
  · intro i j hij
    have : A i j = 0 := by
      rw [hA, vecMulVec_apply]
      by_cases hi : i = c
      · have hj : ¬ S j := fun h => hij ⟨hi ▸ hc, h⟩
        have hlj : l j = 0 := by
          by_contra h
          exact hj (hS j h)
        have hjc : j ≠ c := fun h => hj (h ▸ hc)
        simp [he, hlj, hjc]
      · simp [he, hi]
    simp [this]
  · have hv : Matrix.vecMul l A = l c • (l - e) := by
      rw [hA, vecMul_vecMulVec]
      simp [he]
    show Matrix.vecMul l (1 - (l c)⁻¹ • A) = e
    rw [vecMul_sub, vecMul_one, vecMul_smul, hv, smul_smul, inv_mul_cancel₀ hl, one_smul]
    abel

theorem exists_gl_vecMul_eq_single {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (c : Fin r) (hc : S c)
    (l : Fin r → F) (hl : l ≠ 0) (hS : ∀ i, l i ≠ 0 → S i) :
    ∃ h : GL (Fin r) F, (∀ i j, ¬ (S i ∧ S j) → (h : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) ∧
      Matrix.vecMul l (h : Matrix (Fin r) (Fin r) F) = Pi.single c 1 := by
  by_cases hlc : l c = 0
  swap
  · exact exists_gl_vecMul_eq_single_of_ne S c hc l hlc hS
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hl
  have ha : l a ≠ 0 := ha
  have hac : a ≠ c := fun h => ha (h ▸ hlc)
  have h1 : transvection a c (1 : F) * transvection a c (-1 : F) = 1 := by
    rw [transvection_mul_transvection_same a c hac, add_neg_cancel, transvection_zero]
  let t : GL (Fin r) F := ⟨transvection a c 1, transvection a c (-1), h1, mul_eq_one_comm.mp h1⟩
  have hv : ∀ j, Matrix.vecMul l (transvection a c (1 : F)) j = l j + if j = c then l a else 0 := by
    intro j
    rw [transvection, vecMul_add, vecMul_one, Pi.add_apply]
    congr 1
    by_cases hj : j = c
    · subst hj
      simp [vecMul, dotProduct, Matrix.single_apply]
    · simp [vecMul, dotProduct, Matrix.single_apply, hj, Ne.symm hj]
  obtain ⟨h, hh1, hh2⟩ := exists_gl_vecMul_eq_single_of_ne S c hc (Matrix.vecMul l (transvection a c (1 : F)))
    (by rw [hv]; simpa [hlc] using ha)
    (by
      intro i hi
      by_cases hic : i = c
      · exact hic ▸ hc
      · rw [hv] at hi
        exact hS i (by simpa [hic] using hi))
  refine ⟨t * h, ?_, ?_⟩
  · refine eq_one_off_mul S (transvection a c (1 : F)) _ ?_ hh1
    intro i j hij
    have : ¬ (a = i ∧ c = j) := fun h => hij ⟨h.1 ▸ hS a ha, h.2 ▸ hc⟩
    simp [transvection, Matrix.single_apply, this]
  · rw [← hh2, vecMul_vecMul]
    rfl

theorem exists_blockTri_vecMul_eq_single : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ), Monotone b → ∀ (k k' : Fin r), k'.val + 1 = k.val → ∀ l : Fin r → F, l ≠ 0 → (∀ i, l i ≠ 0 → i < k ∧ b i = b k) → ∃ h : blockTri (κ := F) b, (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) ∧ Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Pi.single k' 1 := by
  intro F _ r b hb k k' hk l hl hS
  have hk' : k' < k ∧ b k' = b k := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hl
    obtain ⟨h1, h2⟩ := hS a ha
    have h3 : k' < k := by rw [Fin.lt_def]; omega
    have h4 : a ≤ k' := by rw [Fin.lt_def] at h1; rw [Fin.le_def]; omega
    exact ⟨h3, le_antisymm (hb h3.le) (h2 ▸ hb h4)⟩
  obtain ⟨h, h1, h2⟩ := exists_gl_vecMul_eq_single (fun i => i < k ∧ b i = b k) k' hk' l hl hS
  refine ⟨⟨h, ?_⟩, ?_, h2⟩
  · have : (h : Matrix (Fin r) (Fin r) F).BlockTriangular b := by
      intro i j hij
      rw [h1 i j (fun hh => by rw [hh.1.2, hh.2.2] at hij; exact lt_irrefl _ hij)]
      exact Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
    exact this
  · intro i j hij
    by_contra hn
    exact hij (h1 i j fun hh => hn ⟨hh.1.1, hh.2.1⟩)

end GlobalTheory.FinGL.LeviWh
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

theorem _root_.GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 → IsIntegral ℤ (jT τ) := by
  first | exact @GlobalTheory.JInt.main | exact GlobalTheory.JInt.main | (intros; apply GlobalTheory.JInt.main <;> assumption)
end
