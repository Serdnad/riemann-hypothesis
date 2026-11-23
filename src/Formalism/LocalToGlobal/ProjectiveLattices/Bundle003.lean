module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

structure TRing (K : Type) [Field K] : Type where
  n : ℕ
  I : Ideal (MvPolynomial (Fin n) K)
  rad : I.IsRadical

namespace TRing

variable {K : Type} [Field K]

abbrev R (p : TRing K) : Type := MvPolynomial (Fin p.n) K ⧸ p.I

end TRing

section Rules

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

abbrev Rules : Type := ∀ p : TRing K, pts p.R → p.R

def wchar [Fintype ι] {S : Type} [CommRing S] (e : ι → ℕ) (t : ι → Sˣ) : S :=
  ∏ i, ((t i : Sˣ) : S) ^ e i

def IsNatural (f : Rules pts) : Prop :=
  ∀ (p q : TRing K) (φ : p.R →ₐ[K] q.R) (y : pts p.R) (z : pts q.R), mapR φ y z → f q z = φ (f p y)

def IsWeight [Fintype ι] (e : ι → ℕ) (f : Rules pts) : Prop :=
  ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' → f p y' = wchar e t * f p y

def secW [Fintype ι] (e : ι → ℕ) : Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ IsWeight pts borR e f}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

def FromTest {S : Type} [CommRing S] [Algebra K S] (y : pts S) : Prop :=
  ∃ (p : TRing K) (φ : p.R →ₐ[K] S) (y' : pts p.R), mapR φ y' y

def evalAt (f : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) : S :=
  open Classical in
  if h : FromTest pts mapR y then h.choose_spec.choose (f h.choose h.choose_spec.choose_spec.choose)
  else 0

theorem evalAt_add (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (f + g) y = evalAt pts mapR f y + evalAt pts mapR g y := by
  unfold evalAt; split_ifs <;> simp

theorem evalAt_smul (c : K) (f : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (c • f) y = algebraMap K S c * evalAt pts mapR f y := by
  unfold evalAt; split_ifs <;> simp [Algebra.smul_def]

theorem evalAt_zero {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (0 : Rules pts) y = 0 := by
  unfold evalAt; split_ifs <;> simp

theorem evalAt_mul (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (f * g) y = evalAt pts mapR f y * evalAt pts mapR g y := by
  unfold evalAt; split_ifs <;> simp

theorem evalAt_one {S : Type} [CommRing S] [Algebra K S] (y : pts S) (h : FromTest pts mapR y) :
    evalAt pts mapR (1 : Rules pts) y = 1 := by
  unfold evalAt; rw [dite_eq_left h]; simp

def evalL {S : Type} [CommRing S] [Algebra K S] (y : pts S) : Rules pts →ₗ[K] S where
  toFun f := evalAt pts mapR f y
  map_add' f g := evalAt_add pts mapR f g y
  map_smul' c f := by rw [RingHom.id_apply, evalAt_smul, Algebra.smul_def]

def EvalWD : Prop :=
  ∀ (f : Rules pts), IsNatural pts mapR f →
    ∀ (S : Type) [CommRing S] [Algebra K S] (p q : TRing K) (φ : p.R →ₐ[K] S) (ψ : q.R →ₐ[K] S)
      (y : pts p.R) (z : pts q.R) (w : pts S), mapR φ y w → mapR ψ z w → φ (f p y) = ψ (f q z)

end Rules

section Complex

variable {K : Type} [Field K]

def CAt (_σ : K →+* ℂ) : Type := ℂ

instance (σ : K →+* ℂ) : CommRing (CAt σ) := inferInstanceAs (CommRing ℂ)
instance (σ : K →+* ℂ) : Algebra K (CAt σ) := σ.toAlgebra

def cabs {σ : K →+* ℂ} (z : CAt σ) : ℝ := ‖(show ℂ from z)‖

variable {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

def ptNorm (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) : ℝ :=
  cabs (evalAt pts mapR f y) * ∏ i, |fnorm y i|⁻¹ ^ e i

theorem ptNorm_nonneg (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) : 0 ≤ ptNorm pts mapR σ fnorm e f y :=
  mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => pow_nonneg (inv_nonneg.2 (abs_nonneg _)) _)

theorem ptNorm_zero (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (y : pts (CAt σ)) :
    ptNorm pts mapR σ fnorm e 0 y = 0 := by
  unfold ptNorm; rw [evalAt_zero]
  exact mul_eq_zero_of_left (norm_zero (E := ℂ)) _

def supAt (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts) : ℝ :=
  ⨆ y : pts (CAt σ), ptNorm pts mapR σ fnorm e f y

def BddAt (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts) : Prop :=
  BddAbove (Set.range (ptNorm pts mapR σ fnorm e f))

end Complex

end Formalism.L2.Pj
end
end

section

open NumberField Polynomial

namespace Formalism.L2.Pj

attribute [local instance] FractionRing.liftAlgebra

theorem unramBridge_holds : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    (∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ θ : 𝓞 K,
      θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ ∉ P) →
    Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
  intro K _ _ _ hθ
  set F := maximalRealSubfield K with hF
  have hsep : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [Algebra.unramified_iff_forall]
  rintro ⟨Q, hQ⟩
  change Algebra.IsUnramifiedAt (𝓞 F) Q
  rcases eq_or_ne Q ⊥ with rfl | hne
  · exact Algebra.isUnramifiedAt_bot
  have hmax : Q.IsMaximal := hQ.isMaximal hne
  obtain ⟨θ, hθP⟩ := hθ Q hmax
  set θ' := RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ with hθ'
  have hσ : θ' = IsCMField.ringOfIntegersComplexConj K θ := RingOfIntegers.ext rfl
  have hne' : θ - θ' ≠ 0 := fun h => hθP (h ▸ Ideal.zero_mem _)

  have hnotF : (θ : K) ∉ F := by
    intro hm
    apply hne'
    rw [sub_eq_zero, hσ]
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    exact ((IsCMField.complexConj_eq_self_iff K _).mpr hm).symm

  have hfin : Module.finrank F K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F K
  have hint : IsIntegral F (θ : K) := Algebra.IsIntegral.isIntegral _
  have hadj : Algebra.adjoin F {algebraMap (𝓞 K) K θ} = ⊤ := by
    have : IsSimpleOrder (IntermediateField F K) :=
      IntermediateField.isSimpleOrder_of_finrank_prime F K (hfin ▸ Nat.prime_two)
    rcases eq_bot_or_eq_top (IntermediateField.adjoin F {(θ : K)}) with h | h
    · exfalso
      rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot] at h
      obtain ⟨y, hy⟩ := h
      exact hnotF (hy ▸ y.2)
    · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      change (IntermediateField.adjoin F {(θ : K)}).toSubalgebra = ⊤
      rw [h, IntermediateField.top_toSubalgebra]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F K θ hadj

  set f := minpoly (𝓞 F) θ with hf
  have hθint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral _
  have hmonic : f.Monic := minpoly.monic hθint
  have hdeg : f.natDegree ≤ 2 := by
    have h1 : f = minpoly (𝓞 F) (algebraMap (𝓞 K) K θ) :=
      (minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) θ).symm
    have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' F
      (IsIntegral.algebraMap hθint : IsIntegral (𝓞 F) (algebraMap (𝓞 K) K θ))
    have h3 : (minpoly F (algebraMap (𝓞 K) K θ)).natDegree ≤ 2 :=
      hfin ▸ minpoly.natDegree_le _
    rw [h2, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h3
    rw [h1]; exact h3
  set fK := f.map (algebraMap (𝓞 F) (𝓞 K)) with hfK
  have hKmonic : fK.Monic := hmonic.map _
  have hKdeg : fK.natDegree ≤ 2 := by
    rw [hfK, hmonic.natDegree_map]; exact hdeg
  have hr1 : fK.IsRoot θ := by
    rw [IsRoot, hfK, eval_map, ← aeval_def]; exact minpoly.aeval _ _
  have hr2 : fK.IsRoot θ' := by
    rw [IsRoot, hfK, eval_map, ← aeval_def, hσ]
    rw [show IsCMField.ringOfIntegersComplexConj K θ = (IsCMField.ringOfIntegersComplexConj K).toAlgHom θ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  set g := fK /ₘ (X - C θ) with hg
  have hfg : (X - C θ) * g = fK := (mul_divByMonic_eq_iff_isRoot).mpr hr1
  have hg2 : g.IsRoot θ' := by
    have := hr2
    rw [← hfg, IsRoot, eval_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hne'; simp at h; rw [sub_eq_zero] at h ⊢; exact h.symm
    · exact h
  set h := g /ₘ (X - C θ') with hh
  have hgh : (X - C θ') * h = g := (mul_divByMonic_eq_iff_isRoot).mpr hg2
  have hfac : fK = (X - C θ) * ((X - C θ') * h) := by rw [hgh, hfg]
  have hhmonic : h.Monic := by
    have hm2 : ((X - C θ) * (X - C θ')).Monic := (monic_X_sub_C θ).mul (monic_X_sub_C θ')
    rw [hfac, ← mul_assoc] at hKmonic
    exact hm2.of_mul_monic_left hKmonic
  have hh1 : h = 1 := by
    rw [← hhmonic.natDegree_eq_zero]
    have := hKdeg
    rw [hfac, natDegree_mul (X_sub_C_ne_zero θ) (mul_ne_zero (X_sub_C_ne_zero θ') hhmonic.ne_zero),
      natDegree_mul (X_sub_C_ne_zero θ') hhmonic.ne_zero, natDegree_X_sub_C, natDegree_X_sub_C] at this
    omega
  have hval : aeval θ (derivative f) = θ - θ' := by
    rw [aeval_def, ← eval_map, ← derivative_map, ← hfK, hfac, hh1]
    simp [derivative_mul]
  rw [← not_dvd_differentIdeal_iff, Ideal.dvd_iff_le]
  intro hle
  exact hθP (hle (hval ▸ hmem))

end Formalism.L2.Pj
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

structure IsDer {A : Type*} [CommRing A] (δ : A → A) : Prop where
  add : ∀ x y, δ (x + y) = δ x + δ y
  mul : ∀ x y, δ (x * y) = x * δ y + y * δ x

namespace IsDer

variable {A : Type*} [CommRing A] {δ : A → A}

theorem der_zero (h : IsDer δ) : δ 0 = 0 := by
  have e := h.add 0 0
  rw [add_zero] at e
  linear_combination -e

theorem der_one (h : IsDer δ) : δ 1 = 0 := by
  have e := h.mul 1 1
  simp only [one_mul] at e
  linear_combination -e

theorem der_neg (h : IsDer δ) (x : A) : δ (-x) = -δ x := by
  have e := h.add x (-x)
  rw [add_neg_cancel, h.der_zero] at e
  linear_combination -e

theorem der_sub (h : IsDer δ) (x y : A) : δ (x - y) = δ x - δ y := by
  rw [sub_eq_add_neg, h.add, h.der_neg, sub_eq_add_neg]

theorem der_pow_succ (h : IsDer δ) (x : A) (n : ℕ) : δ (x ^ (n + 1)) = (n + 1 : A) * x ^ n * δ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x (n + 1), h.mul, ih]
    push_cast
    ring

theorem mul_map_pow (h : IsDer δ) (z : A) (r : ℕ) : z * δ (z ^ r) = (r : A) * z ^ r * δ z := by
  cases r with
  | zero => simp [h.der_one]
  | succ n =>
    rw [h.der_pow_succ]
    push_cast
    ring

theorem der_sum (h : IsDer δ) {ι : Type*} (s : Finset ι) (f : ι → A) : δ (∑ i ∈ s, f i) = ∑ i ∈ s, δ (f i) := by
  exact map_sum (AddMonoidHom.mk' δ h.add) f s

theorem pow_map_mem_of_pow_mul_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    (y : A) : ∀ m r : ℕ, y ^ m * δ y ^ r ∈ I → δ y ^ (r + 2 * m) ∈ I := by
  intro m
  induction m with
  | zero => intro r hr; simpa using hr
  | succ m ih =>
    intro r hr
    have hwJ : δ y * δ (y ^ (m + 1) * δ y ^ r) ∈ I := I.mul_mem_left _ (hI _ hr)
    have e := h.mul_map_pow (δ y) r
    have key : δ y * δ (y ^ (m + 1) * δ y ^ r) =
        (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) + ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) := by
      rw [h.mul, h.der_pow_succ]
      linear_combination y ^ (m + 1) * e
    have h2 : ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) ∈ I := by
      have h3 : (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) ∈ I := I.mul_mem_left _ hr
      have h5 := I.sub_mem hwJ h3
      rwa [key, add_sub_cancel_left] at h5
    have hu1 := hu (m + 1) (Nat.succ_pos m)
    push_cast at hu1
    have h4 : y ^ m * δ y ^ (r + 2) ∈ I := (Ideal.unit_mul_mem_iff_mem I hu1).mp h2
    have h6 := ih (r + 2) h4
    rwa [show r + 2 + 2 * m = r + 2 * (m + 1) by ring] at h6

theorem pow_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    {y : A} {n : ℕ} (hy : y ^ n ∈ I) : δ y ^ (2 * n) ∈ I := by
  have e := h.pow_map_mem_of_pow_mul_mem I hI hu y n 0 (by simpa using hy)
  simpa using e

theorem mem_max [IsArtinianRing A] (h : IsDer δ) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A)) (m : Ideal A)
    [hm : m.IsMaximal] {x : A} (hx : x ∈ m) : δ x ∈ m := by

  have hx' : algebraMap A (Localization.AtPrime m) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m x).mpr hx
  have hnil : IsNilpotent (algebraMap A (Localization.AtPrime m) x) := by
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Localization.AtPrime m)
    refine ⟨k, ?_⟩
    have hj : algebraMap A (Localization.AtPrime m) x ∈ Ideal.jacobson (⊥ : Ideal (Localization.AtPrime m)) := by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    have := Ideal.pow_mem_pow hj k
    rwa [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  obtain ⟨n, hn⟩ := hnil
  rw [← map_pow] at hn
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) _).mp hn
  have hs' : s ∉ m := hs

  have hsx0 : (s * x) ^ (n + 1) ∈ (⊥ : Ideal A) := by
    rw [Ideal.mem_bot]
    calc (s * x) ^ (n + 1) = s ^ n * x * (s * x ^ n) := by ring
      _ = 0 := by simp only at hsx; rw [hsx, mul_zero]
  have hb : ∀ z ∈ (⊥ : Ideal A), δ z ∈ (⊥ : Ideal A) := by
    intro z hz
    rw [Ideal.mem_bot] at hz ⊢
    rw [hz, h.der_zero]
  have hd := h.pow_mem ⊥ hb hu hsx0
  rw [Ideal.mem_bot] at hd
  have hdm : δ (s * x) ∈ m := hm.isPrime.mem_of_pow_mem _ (by rw [hd]; exact m.zero_mem)
  rw [h.mul] at hdm
  have hxs : x * δ s ∈ m := m.mul_mem_right _ hx
  have hsd : s * δ x ∈ m := by
    have := m.sub_mem hdm hxs
    rwa [add_sub_cancel_right] at this
  exact (hm.isPrime.mem_or_mem hsd).resolve_left hs'

theorem quot (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) :
    ∃ δ' : A ⧸ I → A ⧸ I, IsDer δ' ∧ ∀ x, δ' (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (δ x) := by
  classical
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := Function.surjInv_eq _
  have key : ∀ x, Ideal.Quotient.mk I (δ (s (Ideal.Quotient.mk I x))) = Ideal.Quotient.mk I (δ x) := by
    intro x
    rw [Ideal.Quotient.eq, ← h.der_sub]
    exact hI _ (Ideal.Quotient.eq.mp (hs _))
  refine ⟨fun q => Ideal.Quotient.mk I (δ (s q)), ⟨fun a b => ?_, fun a b => ?_⟩, key⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add (f := _), key, key, key, h.add, map_add (f := _)]
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, key, key, h.mul, map_add (f := _), map_mul, map_mul]

theorem ofLoc {B : Type*} [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (d : A → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = algebraMap A B x * d y + algebraMap A B y * d x) :
    ∃ δ' : B → B, IsDer δ' ∧ ∀ a, δ' (algebraMap A B a) = d a := by
  have d1 : d 1 = 0 := by
    have e := hmul 1 1
    simp only [mul_one, map_one, one_mul] at e
    linear_combination -e
  have d0 : d 0 = 0 := by
    have e := hadd 0 0
    simp only [add_zero] at e
    linear_combination -e

  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A B a) + TrivSqZeroExt.inr (d a)
      map_one' := by ext <;> simp [d1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul, TrivSqZeroExt.snd_mul]; ring
      map_zero' := by ext <;> simp [d0]
      map_add' := fun x y => by
        ext
        · simp
        · simp [hadd] }
  have hψ : ∀ s : S, IsUnit (ψ s) := by
    intro s
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa [ψ] using IsLocalization.map_units B s
  let φ : B →+* TrivSqZeroExt B B := IsLocalization.lift hψ
  have hφ : ∀ a, φ (algebraMap A B a) = ψ a := IsLocalization.lift_eq hψ
  let fst : TrivSqZeroExt B B →+* B :=
    { toFun := TrivSqZeroExt.fst
      map_one' := rfl
      map_mul' := fun x y => TrivSqZeroExt.fst_mul x y
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hfst : ∀ x, (φ x).fst = x := by
    have e : fst.comp φ = RingHom.id B := by
      apply IsLocalization.ringHom_ext S
      ext a
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ]
      show TrivSqZeroExt.fst (ψ a) = _
      simp [ψ]
    intro x
    exact congrArg (fun f : B →+* B => f x) e
  refine ⟨fun x => (φ x).snd, ⟨fun x y => by simp, fun x y => ?_⟩, fun a => by simp [hφ, ψ]⟩
  simp only [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul, op_smul_eq_mul]
  ring

end IsDer

end Formalism.L2.Pj.GenericSectionMinimum
end
end
