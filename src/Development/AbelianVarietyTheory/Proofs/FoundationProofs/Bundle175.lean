module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle166
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle164
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle165
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.NumberTheory.Modular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle163
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped Pointwise

namespace GlobalTheory.AntiRamConj

section General
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

def moveVal (c : Ω ≃+* Ω) (B : ValuationSubring Ω) : ValuationSubring Ω :=
  B.comap (c.symm : Ω →+* Ω)

theorem mem_moveVal (c : Ω ≃+* Ω) (B : ValuationSubring Ω) (y : Ω) :
    y ∈ moveVal c B ↔ c.symm y ∈ B := Iff.rfl

theorem moveVal_lt_one (c : Ω ≃+* Ω) (B : ValuationSubring Ω) (y : Ω) :
    (moveVal c B).valuation y < 1 ↔ B.valuation (c.symm y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_moveVal, mem_moveVal, map_inv₀,
    map_eq_zero_iff _ c.symm.injective]

def conjAut (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (σ : G E Ω) : G E Ω :=
  { (c.symm.trans (σ : Ω ≃+* Ω)).trans c with
    commutes' := fun x => by
      obtain ⟨y, hy⟩ := hc x
      show c (σ (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
      rw [hy, σ.commutes, ← hy, RingEquiv.apply_symm_apply] }

theorem conjAut_apply (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) (σ : G E Ω) (x : Ω) :
    conjAut c hc σ x = c (σ (c.symm x)) := rfl

theorem conjAut_mem_ine [NumberField E] (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) {B : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) : conjAut c hc σ ∈ Ine (F := E) (moveVal c B) := by
  have hd : σ ∈ Dec (F := E) B := hσ.1
  refine ⟨?_, fun x hx => ?_⟩
  · show conjAut c hc σ ∈ Dec (F := E) (moveVal c B)
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    obtain ⟨z, rfl⟩ := (conjAut c hc σ).surjective x
    have h1 : ((conjAut c hc σ)⁻¹ : G E Ω) (conjAut c hc σ z) = z := (conjAut c hc σ).symm_apply_apply z
    rw [h1, mem_moveVal, mem_moveVal, conjAut_apply, RingEquiv.symm_apply_apply,
      apply_mem_iff_of_mem_Dec hd]
  · rw [moveVal_lt_one, map_sub, conjAut_apply, RingEquiv.symm_apply_apply]
    apply hσ.2
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact hx

end General

theorem host_conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => D.host.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

theorem cc_algebraMap_host (D : D7) (x : D.host.E) :
    D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
  apply j.injective
  rw [hj]
  exact (D.host.conjE_apply
    (j.comp (algebraMap D.host.E D.nd.Om)) x).symm

theorem cc_symm_algebraMap_host (D : D7) (x : D.host.E) :
    D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  rw [RingEquiv.symm_apply_eq, cc_algebraMap_host, host_conj_conj]

theorem isPlaceOver_moveVal (D : D7) {P P' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : IsConjPl D.host P P') {B : ValuationSubring D.nd.Om} (hB : IsPlaceOver B P) :
    IsPlaceOver (moveVal D.ntw.cc B) P' := by
  intro y
  have hi : IsIntegral ℤ (D.host.conj (y : D.host.E)) :=
    (y.isIntegral_coe).map_of_comp_eq (RingHom.id ℤ) (D.host.conj : D.host.E →+* D.host.E) (by ext; simp)
  let x : 𝓞 D.host.E := ⟨_, hi⟩
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := rfl
  rw [moveVal_lt_one, cc_symm_algebraMap_host, ← hx, hB x]
  exact h x y (by rw [hx, host_conj_conj])

end GlobalTheory.AntiRamConj
end

section

namespace GlobalTheory.RationalOfReal

open IntermediateField

theorem exists_coords {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] (β : E) (d : ℚ)
    (hβ : β * β = -(d : E)) (y : E) (hy : y ∈ ℚ⟮β⟯) : ∃ u v : ℚ, y = (u : E) + (v : E) * β := by
  have hint : IsIntegral ℚ β := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : β ^ 2 = algebraMap ℚ E (-d) := by rw [pow_two, hβ]; simp
    rw [this]
    exact isIntegral_algebraMap
  have hy' : y ∈ Algebra.adjoin ℚ ({β} : Set E) := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  clear hy
  induction hy' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - d * v * v', u * v' + v * u', ?_⟩
    push_cast
    linear_combination (v : E) * (v' : E) * hβ

theorem rat_of_im_eq_zero {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] (φ : E →+* ℂ) (β : E)
    (d : ℕ) (hd : 0 < d) (hφ : φ β = Complex.I * (Real.sqrt d : ℂ)) (y : E) (hy : y ∈ ℚ⟮β⟯)
    (him : (φ y).im = 0) : ∃ a : ℚ, y = (a : E) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hβ : β * β = -(((d : ℚ)) : E) := by
    apply φ.injective
    have h2 : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    rw [map_mul, hφ, map_neg, map_ratCast]
    push_cast
    linear_combination (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) * Complex.I_mul_I - h2
  obtain ⟨u, v, rfl⟩ := exists_coords β d hβ y hy
  rw [map_add (f := _), map_mul, map_ratCast, map_ratCast, hφ] at him
  have hv : (v : ℝ) * Real.sqrt d = 0 := by simpa using him
  have hv0 : v = 0 := by
    have := (mul_eq_zero.1 hv).resolve_right hs.ne'
    exact_mod_cast this
  exact ⟨u, by simp [hv0]⟩

theorem rat_of_real (D : Formalism.BasicNotions.D7) (x : D.host.K)
    (hx : (D.host.φ₀ (x : D.host.E)).im = 0) : ∃ a : ℚ, x = (a : D.host.K) := by
  obtain ⟨a, ha⟩ := rat_of_im_eq_zero D.host.φ₀ (D.host.sqd) D.host.d
    D.host.hyp.2.1.pos D.host.φ₀_mem (x : D.host.E) x.2 hx
  exact ⟨a, Subtype.ext (by simpa using ha)⟩

end GlobalTheory.RationalOfReal
end

section

open Polynomial

noncomputable section

namespace GlobalTheory.Proof.ListFormLabels

open Formalism.BasicNotions

def ListFormAt (D : D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (∃ L : List (ℕ × ℕ × Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k))),
      (L.map fun p => (p.1, p.2.1) : Multiset (ℕ × ℕ)) = D.ntypes.bc σ ∧
      (∀ p ∈ L, Multiset.card p.2.2 = p.1 ∧ p.2.2.map (fun x => x ^ D.host.g k) = p.2.2) ∧
      Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v) = (L.map fun p => p.2.1 • p.2.2).sum) ∧
    (D.ntypes.cuspidal σ →
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ D.host.g k →
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w) x))).prod ∧
      ∃ φ : Formalism.MainNotions.N.GE D.nd,
        D.ntypes.rbar σ w (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ w (D.ntypes.tg k v) ^ D.host.g k)

end GlobalTheory.Proof.ListFormLabels
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.roots_norm_le_of_bounded_two_step_recurrence : ∀ (x y : ℂ) (c : ℕ → ℂ) (C R : ℝ), 0 ≤ R → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∀ r, ‖c r‖ ≤ C * R ^ r) → ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
  first | exact @GlobalTheory.roots_norm_le_of_bounded_two_step_recursion | exact GlobalTheory.roots_norm_le_of_bounded_two_step_recursion | (intros; apply GlobalTheory.roots_norm_le_of_bounded_two_step_recursion <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.second_difference_inv_pow_bound : ∀ j : ℕ, ∃ C : ℝ, ∀ z a b : ℂ, z ≠ 0 → 4 * ‖a‖ ≤ ‖z‖ → 4 * ‖b‖ ≤ ‖z‖ → ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹ - ((z + b) ^ j)⁻¹ + ((z + a + b) ^ j)⁻¹‖ ≤ C * ‖a‖ * ‖b‖ / ‖z‖ ^ (j + 2) := by
  first | exact @GlobalTheory.EisM.SecondDiff.second_diff_inv_pow | exact GlobalTheory.EisM.SecondDiff.second_diff_inv_pow | (intros; apply GlobalTheory.EisM.SecondDiff.second_diff_inv_pow <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.summable_card_divisors_sq_div_one_add_rpow : ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ (1 + s) := by
  first | exact @GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow | exact GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow | (intros; apply GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.not_summable_inv_primes_congr_neg_one : ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ => if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  first | exact @GlobalTheory.not_summable_one_div_primes_eq_neg_one | exact GlobalTheory.not_summable_one_div_primes_eq_neg_one | (intros; apply GlobalTheory.not_summable_one_div_primes_eq_neg_one <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

noncomputable section

namespace GlobalTheory
namespace TsenLang

variable {k : Type} [Field k]

def genSub (n s : ℕ) (j : Fin n) : (MvPolynomial (Fin n × Fin (s + 1)) k)[X] :=
  ∑ t : Fin (s + 1), Polynomial.monomial (t : ℕ) (MvPolynomial.X (j, t))

def genEval (n s : ℕ) (g : MvPolynomial (Fin n) k[X]) : (MvPolynomial (Fin n × Fin (s + 1)) k)[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C) (genSub n s) g

theorem map_genEval (n s : ℕ) (φ : MvPolynomial (Fin n × Fin (s + 1)) k →+* k)
    (hφ : ∀ a, φ (MvPolynomial.C a) = a) (g : MvPolynomial (Fin n) k[X]) :
    (genEval n s g).map φ = MvPolynomial.eval (fun j => (genSub n s j).map φ) g := by
  unfold genEval
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.hom_eval₂, Polynomial.mapRingHom_comp]
  have h : φ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (s + 1)) k) = RingHom.id k :=
    RingHom.ext hφ
  rw [h, Polynomial.mapRingHom_id]
  rfl

theorem natDegree_genSub_le (n s : ℕ) (j : Fin n) : (genSub (k := k) n s j).natDegree ≤ s := by
  unfold genSub
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro t _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp t.2)

theorem natDegree_genEval_le (n s d m : ℕ) (g : MvPolynomial (Fin n) k[X])
    (hg : ∀ μ, g.coeff μ ≠ 0 → μ.degree = d ∧ (g.coeff μ).natDegree ≤ m) :
    (genEval n s g).natDegree ≤ d * s + m := by
  unfold genEval
  rw [MvPolynomial.eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro μ hμ
  obtain ⟨h1, h2⟩ := hg μ (MvPolynomial.mem_support_iff.mp hμ)
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hA : (Polynomial.mapRingHom (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (s + 1)) k)
      (g.coeff μ)).natDegree ≤ m := (Polynomial.natDegree_map_le).trans h2
  have hB : (∏ j, genSub (k := k) n s j ^ μ j).natDegree ≤ d * s := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ j, (genSub (k := k) n s j ^ μ j).natDegree ≤ ∑ j, μ j * s :=
          Finset.sum_le_sum fun j _ =>
            (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (natDegree_genSub_le n s j))
      _ = (∑ j, μ j) * s := by rw [Finset.sum_mul]
      _ = d * s := by rw [← h1, Finsupp.degree_eq_sum]
  omega

theorem genSub_map_constantCoeff (n s : ℕ) (j : Fin n) :
    (genSub (k := k) n s j).map MvPolynomial.constantCoeff = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [genSub, Polynomial.map_sum]

theorem coeff_genSub_map_eval (n s : ℕ) (c : Fin n × Fin (s + 1) → k) (j : Fin n) (t : Fin (s + 1)) :
    ((genSub (k := k) n s j).map (MvPolynomial.eval c)).coeff t = c (j, t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [genSub, Polynomial.map_sum, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Fin.val_inj]

theorem constantCoeff_coeff_genEval (n s d : ℕ) (hd : 0 < d) (g : MvPolynomial (Fin n) k[X])
    (hg : ∀ μ, g.coeff μ ≠ 0 → μ.degree = d) (e : ℕ) :
    MvPolynomial.constantCoeff ((genEval n s g).coeff e) = 0 := by
  have h := map_genEval (k := k) n s MvPolynomial.constantCoeff (fun a => by simp) g
  have h2 : (fun j => (genSub (k := k) n s j).map MvPolynomial.constantCoeff) = 0 := by
    funext j; exact genSub_map_constantCoeff n s j
  rw [h2, MvPolynomial.eval_zero] at h
  have h3 : MvPolynomial.constantCoeff g = 0 := by
    by_contra hne
    have := hg 0 (by rwa [← MvPolynomial.constantCoeff_eq])
    simp at this; omega
  rw [h3] at h
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p e) h
  simpa [Polynomial.coeff_map] using this

theorem exists_ne_zero_polynomial_common_zero [IsAlgClosed k] (n r d m : ℕ)
    (g : Fin r → MvPolynomial (Fin n) k[X])
    (hg : ∀ i μ, (g i).coeff μ ≠ 0 → μ.degree = d ∧ ((g i).coeff μ).natDegree ≤ m)
    (hd : 0 < d) (hn : r * d < n) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (g i) = 0 := by
  classical
  set s := r * (m + 1) with hs
  set E := d * s + m + 1 with hE
  let F : Fin r × Fin E → MvPolynomial (Fin n × Fin (s + 1)) k :=
    fun p => (genEval n s (g p.1)).coeff p.2
  let e1 : Fin (r * E) ≃ Fin r × Fin E := finProdFinEquiv.symm
  let e2 : Fin (n * (s + 1)) ≃ Fin n × Fin (s + 1) := finProdFinEquiv.symm
  let F' : Fin (r * E) → MvPolynomial (Fin (n * (s + 1))) k :=
    fun q => MvPolynomial.rename e2.symm (F (e1 q))
  have hF' : ∀ q, MvPolynomial.constantCoeff (F' q) = 0 := by
    intro q
    simp only [F', MvPolynomial.constantCoeff_rename, F]
    exact constantCoeff_coeff_genEval n s d hd _ (fun μ h => (hg _ μ h).1) _
  have hlt : r * E < n * (s + 1) := by
    have h1 : r * d + 1 ≤ n := hn
    have h2 : (r * d + 1) * (s + 1) ≤ n * (s + 1) := Nat.mul_le_mul_right _ h1
    have h3 : r * E < (r * d + 1) * (s + 1) := by
      rw [hE, hs]; ring_nf; nlinarith
    omega
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_common_zero_of_constantCoeff_eq_zero k _ _ F' hF' hlt
  set c' : Fin n × Fin (s + 1) → k := c ∘ e2.symm with hc'
  refine ⟨fun j => (genSub n s j).map (MvPolynomial.eval c'), ?_, ?_⟩
  · intro h0
    obtain ⟨q, hq⟩ : ∃ q, c q ≠ 0 := by
      by_contra hh; push_neg at hh; exact hc0 (funext hh)
    have := congrArg (fun x : Fin n → k[X] => (x (e2 q).1).coeff (e2 q).2) h0
    simp only [coeff_genSub_map_eval, Pi.zero_apply, Polynomial.coeff_zero] at this
    apply hq
    simpa [hc'] using this
  · intro i
    rw [← map_genEval n s (MvPolynomial.eval c') (fun a => by simp)]
    ext e
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases he : e < E
    · have := hc (e1.symm (i, ⟨e, he⟩))
      simpa [F', F, MvPolynomial.eval_rename, hc'] using this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, map_zero]
      have := natDegree_genEval_le n s d m (g i) (hg i)
      omega

end TsenLang


open TsenLang in
theorem tsenLang_ratFunc :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) (RatFunc k)),
      (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
        ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r d f hf hd hn
  classical
  let S : Finset (RatFunc k) := Finset.univ.biUnion fun i => (f i).support.image fun μ => (f i).coeff μ
  obtain ⟨⟨b, hb⟩, hbS⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors k[X]) S
  let numer : RatFunc k → k[X] := fun a =>
    if h : IsLocalization.IsInteger k[X] (b • a) then (RingHom.mem_rangeS.mp h).choose else 0
  have hnumer : ∀ a ∈ S, algebraMap k[X] (RatFunc k) (numer a) = b • a := by
    intro a ha
    have h := hbS a ha
    simp only [numer, dif_pos h]
    exact (RingHom.mem_rangeS.mp h).choose_spec
  let g : Fin r → MvPolynomial (Fin n) k[X] := fun i =>
    ∑ μ ∈ (f i).support, MvPolynomial.monomial μ (numer ((f i).coeff μ))
  have hgc : ∀ i μ, (g i).coeff μ = if μ ∈ (f i).support then numer ((f i).coeff μ) else 0 := by
    intro i μ
    simp only [g, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hgmap : ∀ i, MvPolynomial.map (algebraMap k[X] (RatFunc k)) (g i) =
      MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f i := by
    intro i
    ext μ
    rw [MvPolynomial.coeff_map, hgc, MvPolynomial.coeff_C_mul]
    split_ifs with hμ
    · rw [hnumer _ (by simp only [S, Finset.mem_biUnion, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, μ, hμ, rfl⟩),
        Algebra.smul_def]
    · rw [MvPolynomial.notMem_support_iff.mp hμ]; simp
  let m : ℕ := Finset.univ.sup fun i => (g i).support.sup fun μ => ((g i).coeff μ).natDegree
  have hg : ∀ i μ, (g i).coeff μ ≠ 0 → μ.degree = d ∧ ((g i).coeff μ).natDegree ≤ m := by
    intro i μ hμ
    refine ⟨?_, ?_⟩
    · have hmem : μ ∈ (f i).support := by
        by_contra h; rw [hgc, if_neg h] at hμ; exact hμ rfl
      have := hf i (MvPolynomial.mem_support_iff.mp hmem)
      rwa [Finsupp.degree_eq_weight_one]
    · exact le_trans (Finset.le_sup (f := fun μ => ((g i).coeff μ).natDegree)
          (MvPolynomial.mem_support_iff.mpr hμ))
        (Finset.le_sup (f := fun i => (g i).support.sup fun μ => ((g i).coeff μ).natDegree)
          (Finset.mem_univ i))
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_polynomial_common_zero n r d m g hg hd hn
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) := IsFractionRing.injective k[X] (RatFunc k)
  have hb0 : algebraMap k[X] (RatFunc k) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨fun j => algebraMap k[X] (RatFunc k) (y j), ?_, ?_⟩
  · intro h
    apply hy0
    funext j
    have := congrFun h j
    exact hinj (by simpa using this)
  · intro i
    have h1 : algebraMap k[X] (RatFunc k) (MvPolynomial.eval y (g i)) =
        MvPolynomial.eval (fun j => algebraMap k[X] (RatFunc k) (y j))
          (MvPolynomial.map (algebraMap k[X] (RatFunc k)) (g i)) := by
      rw [MvPolynomial.eval_map]
      first
        | (simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂]; rfl)
        | exact MvPolynomial.eval₂_comp_left _ _ _ _
        | simp [MvPolynomial.eval₂_comp_left]
    rw [hy i, map_zero, hgmap, map_mul, MvPolynomial.eval_C] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hb0

end GlobalTheory
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.finite_slTwo_smul_mem_fundamentalDomain : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  first | exact @GlobalTheory.EisM.finite_smul_mem_fd | exact GlobalTheory.EisM.finite_smul_mem_fd | (intros; apply GlobalTheory.EisM.finite_smul_mem_fd <;> assumption)
end
