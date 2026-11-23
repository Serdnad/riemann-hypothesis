module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Data.EReal.Basic
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
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Analysis.Complex.Cardinality

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0


open Polynomial in
noncomputable def hupsTw {σ R : Type*} [CommRing R] (w : σ → ℕ) :
    MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  MvPolynomial.aeval fun v => Polynomial.C (MvPolynomial.X v) * Polynomial.X ^ (w v)

def hupsWt {σ : Type*} (w : σ → ℕ) (s : σ →₀ ℕ) : ℕ := s.sum fun v k => k * w v

theorem hupsTw_monomial {σ R : Type*} [CommRing R] (w : σ → ℕ) (s : σ →₀ ℕ) (a : R) :
    hupsTw w (MvPolynomial.monomial s a) =
      Polynomial.C (MvPolynomial.monomial s a) * Polynomial.X ^ hupsWt w s := by
  rw [hupsTw, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, hupsWt, Finsupp.prod, Finsupp.sum, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  simp only [mul_comm (w _) _]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem hupsTw_eq {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R) :
    hupsTw w p = ∑ s ∈ p.support,
      Polynomial.C (MvPolynomial.monomial s (p.coeff s)) * Polynomial.X ^ hupsWt w s := by
  conv_lhs => rw [p.as_sum]

  rw [map_sum]
  simp only [hupsTw_monomial]

theorem hupsTw_coeff_coeff {σ R : Type*} [CommRing R] (w : σ → ℕ) (p : MvPolynomial σ R)
    (j : ℕ) (s : σ →₀ ℕ) :
    ((hupsTw w p).coeff j).coeff s = if hupsWt w s = j then p.coeff s else 0 := by
  classical
  rw [hupsTw_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [MvPolynomial.coeff_sum]
  simp only [apply_ite (AddMonoidAlgebra.coeff · s), MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero]
  rw [Finset.sum_eq_single s]
  · by_cases h : hupsWt w s = j
    · rw [if_pos h.symm, if_pos h, if_pos rfl]
    · simp [h, Ne.symm h]
  · intro t _ hts
    simp [hts, MvPolynomial.coeff_monomial]
  · intro hs
    rw [MvPolynomial.mem_support_iff, not_not] at hs
    simp [hs]

theorem hupsTw_ne_zero {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R}
    {s : σ →₀ ℕ} (hs : s ∈ p.support) : (hupsTw w p).coeff (hupsWt w s) ≠ 0 := by
  intro h
  have e := hupsTw_coeff_coeff w p (hupsWt w s) s
  rw [h, MvPolynomial.coeff_zero, if_pos rfl] at e
  exact (MvPolynomial.mem_support_iff.mp hs) e.symm

theorem hupsTw_hom {σ R : Type*} [CommRing R] (w : σ → ℕ) {p : MvPolynomial σ R} {a : ℕ}
    (hp : ∀ s ∈ p.support, hupsWt w s = a) :
    hupsTw w p = Polynomial.C p * Polynomial.X ^ a := by
  ext j s
  rw [hupsTw_coeff_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hs : s ∈ p.support
  · rw [hp s hs]
    by_cases hj : j = a
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  · rw [MvPolynomial.mem_support_iff, not_not] at hs
    split_ifs <;> simp [hs]

theorem hups_hom_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} (hF : F ≠ 0) {a n : ℕ} (hFa : ∀ s ∈ F.support, hupsWt w s = a)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s = n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + a = n := by
  have h1 : hupsTw w (F * P) = Polynomial.C (F * P) * Polynomial.X ^ n := hupsTw_hom w hFP
  have h2 : hupsTw w F = Polynomial.C F * Polynomial.X ^ a := hupsTw_hom w hFa
  rw [map_mul, h2, map_mul] at h1
  have hCF : (Polynomial.C F : Polynomial (MvPolynomial σ R)) ≠ 0 := Polynomial.C_ne_zero.mpr hF
  have h3 : Polynomial.X ^ a * hupsTw w P = Polynomial.C P * Polynomial.X ^ n := by
    apply mul_left_cancel₀ hCF
    rw [← mul_assoc, ← mul_assoc]
    exact h1
  have h4 := congrArg (fun q => q.coeff (hupsWt w s0 + a)) h3
  simp only [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C_mul_X_pow] at h4
  by_contra hne
  rw [if_neg hne] at h4
  exact hupsTw_ne_zero w hs0 h4

theorem hups_deg_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} {u n : ℕ} {sF : σ →₀ ℕ} (hsF : sF ∈ F.support)
    (hFu : hupsWt w sF = u)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s ≤ n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + u ≤ n := by
  have hTF : (hupsTw w F).coeff u ≠ 0 := by
    rw [← hFu]
    exact hupsTw_ne_zero w hsF
  have hTP : (hupsTw w P).coeff (hupsWt w s0) ≠ 0 := hupsTw_ne_zero w hs0
  have hF0 : hupsTw w F ≠ 0 := fun h => hTF (by rw [h, Polynomial.coeff_zero])
  have hP0 : hupsTw w P ≠ 0 := fun h => hTP (by rw [h, Polynomial.coeff_zero])
  have hdeg : (hupsTw w (F * P)).natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    ext s
    rw [hupsTw_coeff_coeff, MvPolynomial.coeff_zero]
    split_ifs with h
    · by_contra hc
      have := hFP s (MvPolynomial.mem_support_iff.mpr hc)
      omega
    · rfl
  rw [map_mul, Polynomial.natDegree_mul hF0 hP0] at hdeg
  have h1 := Polynomial.le_natDegree_of_ne_zero hTF
  have h2 := Polynomial.le_natDegree_of_ne_zero hTP
  omega

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0.WH

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]

def wt (s : σ →₀ ℕ) : ℕ := ∑ v, if p v then s v else 0

theorem wt_add (s t : σ →₀ ℕ) : wt p (s + t) = wt p s + wt p t := by
  simp only [wt, Finsupp.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem wt_single (v : σ) (e : ℕ) : wt p (Finsupp.single v e) = if p v then e else 0 := by
  simp only [wt]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ v) h

noncomputable def psiP : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun v => if p v then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiP_monomial (s : σ →₀ ℕ) (a : K) :
    psiP p (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ wt p s := by
  have key : ∀ v, (if p v then Polynomial.C (X v : MvPolynomial σ K) * Polynomial.X
      else Polynomial.C (X v)) ^ (s v)
      = Polynomial.C ((X v : MvPolynomial σ K) ^ s v) * Polynomial.X ^ (if p v then s v else 0) := by
    intro v
    split_ifs <;> simp [mul_pow]
  rw [psiP, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finset.prod_congr rfl (fun v _ => key v), Finset.prod_mul_distrib, ← map_prod,
    Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul, wt]
  ring

theorem psiP_eq_of_isWeightedHomogeneous (n : ℕ) (f : MvPolynomial σ K) (hf : ∀ s ∈ f.support, wt p s = n) :
    psiP p f = Polynomial.C f * Polynomial.X ^ n := by
  have h : ∀ s ∈ f.support, psiP p (monomial s (AddMonoidAlgebra.coeff f s))
      = Polynomial.C (monomial s (AddMonoidAlgebra.coeff f s)) * Polynomial.X ^ n := fun s hs => by
    rw [psiP_monomial, hf s hs]
  conv_lhs => rw [f.as_sum]

  rw [map_sum, Finset.sum_congr rfl h, ← Finset.sum_mul, ← map_sum, ← f.as_sum]

private theorem psiP_eq_sum_monomial (f : MvPolynomial σ K) :
    psiP p f = ∑ s ∈ f.support, Polynomial.C (monomial s (AddMonoidAlgebra.coeff f s)) * Polynomial.X ^ wt p s := by
  conv_lhs => rw [f.as_sum]

  rw [map_sum]
  simp only [psiP_monomial]

private theorem coeff_psiP (f : MvPolynomial σ K) (k : ℕ) :
    (psiP p f).coeff k = ∑ s ∈ f.support.filter (fun s => wt p s = k), monomial s (AddMonoidAlgebra.coeff f s) := by
  rw [psiP_eq_sum_monomial, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : wt p s = k
  · subst h
    simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

theorem coeff_psiP_ne_zero (f : MvPolynomial σ K) (s : σ →₀ ℕ) (hs : s ∈ f.support) :
    (psiP p f).coeff (wt p s) ≠ 0 := by
  intro h
  have h' := congrArg (AddMonoidAlgebra.coeff · s) h
  rw [coeff_psiP, MvPolynomial.coeff_sum, Finset.sum_eq_single s] at h'
  · classical
    simp only [coeff_monomial, ite_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h'
    exact (mem_support_iff.mp hs) h'
  · classical
    intro t _ hts
    rw [coeff_monomial, ite_eq_right hts]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨hs, rfl⟩)).elim

theorem hom_of_psiP (n : ℕ) (f : MvPolynomial σ K) (hf : psiP p f = Polynomial.C f * Polynomial.X ^ n) :
    ∀ s ∈ f.support, wt p s = n := by
  intro s hs
  by_contra hne
  apply coeff_psiP_ne_zero p f s hs
  rw [hf, Polynomial.coeff_C_mul_X_pow, ite_eq_right hne]

theorem hom_of_dvd (n : ℕ) (H A : MvPolynomial σ K) (hH0 : H ≠ 0)
    (hH : ∀ s ∈ H.support, wt p s = n) (hA : A ∣ H) : ∃ m, ∀ s ∈ A.support, wt p s = m := by
  obtain ⟨B, rfl⟩ := hA
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hH0
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hH0
  have hne : ∀ F : MvPolynomial σ K, F ≠ 0 → psiP p F ≠ 0 := by
    intro F hF h0
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hF
    exact coeff_psiP_ne_zero p F s (mem_support_iff.mpr hs) (by rw [h0, Polynomial.coeff_zero])
  have hprod : psiP p A * psiP p B = Polynomial.C (A * B) * Polynomial.X ^ n := by
    rw [← map_mul]
    exact psiP_eq_of_isWeightedHomogeneous p n _ hH
  have hd := congrArg Polynomial.natDegree hprod
  have ht := congrArg Polynomial.natTrailingDegree hprod
  rw [Polynomial.natDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.natDegree_C_mul_X_pow _ _ hH0] at hd
  rw [Polynomial.natTrailingDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hH0] at ht
  have h1 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p A)
  have h2 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p B)
  refine ⟨(psiP p A).natDegree, fun s hs => ?_⟩
  have hc := coeff_psiP_ne_zero p A s hs
  have h3 := Polynomial.le_natDegree_of_ne_zero hc
  have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
  omega

end ReciprocityTheory.ChartRestriction.G.T0.WH
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

lemma coeff_smul_C (q : MvPolynomial σ L) (e : E) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (q • C e : MvPolynomial σ E) m = algebraMap L E (AddMonoidAlgebra.coeff q m) * e := by
  rw [Algebra.smul_def, algebraMap_def, mul_comm, coeff_C_mul, coeff_map, mul_comm]

variable {n : Type} [Fintype n] (b : Module.Basis n L E)

noncomputable def crd (p : MvPolynomial σ E) (i : n) : MvPolynomial σ L :=
  ∑ m ∈ p.support, monomial m (b.repr (AddMonoidAlgebra.coeff p m) i)

lemma coeff_crd (p : MvPolynomial σ E) (i : n) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (crd b p i) m = b.repr (AddMonoidAlgebra.coeff p m) i := by
  classical
  rw [crd, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero, Finsupp.zero_apply]

lemma eq_sum_crd (p : MvPolynomial σ E) : p = ∑ i, crd b p i • (C (b i) : MvPolynomial σ E) := by
  ext m
  rw [coeff_sum]
  simp only [coeff_smul_C, coeff_crd, ← Algebra.smul_def]
  exact (b.sum_repr (AddMonoidAlgebra.coeff p m)).symm

lemma linearIndependent_C : LinearIndependent (MvPolynomial σ L) (fun i => (C (b i) : MvPolynomial σ E)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  apply MvPolynomial.ext
  intro m
  have h : ∑ j, AddMonoidAlgebra.coeff (g j) m • b j = 0 := by
    simpa only [coeff_sum, coeff_smul_C, ← Algebra.smul_def,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      congrArg (AddMonoidAlgebra.coeff · m) hg
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  exact (Fintype.linearIndependent_iff.1 b.linearIndependent) (fun j => AddMonoidAlgebra.coeff (g j) m) h i

end ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

def stdLat (K : Type) [Field K] [NumberField K] (r : ℕ) : Submodule (𝓞 K) (Fin r → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)

noncomputable def qdist {K : Type} [Field K] {r k : ℕ} (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (q : Fin r → K) : ℝ :=
  ⨅ z : Fin k → ℂ, Real.sqrt (∑ i, ‖σ (q i) + ∑ j, z j * σ (b j i)‖ ^ 2)

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField Cardinal

private lemma countable_of_intermediateField_fg {K Ω : Type} [Field K] [Countable K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) : Countable Ω := by
  obtain ⟨S, hS⟩ := hfg
  haveI : Countable (MvPolynomial (S : Set Ω) K) := by
    first
    | infer_instance
  let f : MvPolynomial (S : Set Ω) K × MvPolynomial (S : Set Ω) K → Ω := fun pq =>
    MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.1 /
      MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.2
  have hf : Function.Surjective f := by
    intro x
    have hx : x ∈ IntermediateField.adjoin K (S : Set Ω) := by
      rw [hS]; exact IntermediateField.mem_top
    obtain ⟨r, hr, t, ht, rfl⟩ := (IntermediateField.mem_adjoin_iff_div).mp hx
    rw [Algebra.adjoin_eq_range] at hr ht
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := ht
    exact ⟨(p, q), rfl⟩
  exact hf.countable

theorem exists_embedding_over {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) (sg : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = sg := by
  haveI hKc : Countable K := by
    first
    | infer_instance
    | exact (Module.finBasis ℚ K).equivFun.injective.countable
  haveI hΩc : Countable Ω := countable_of_intermediateField_fg hfg
  letI : Algebra K ℂ := sg.toAlgebra
  haveI : FaithfulSMul K ℂ := by
    first
    | infer_instance
  haveI : FaithfulSMul K Ω := by
    first
    | infer_instance
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hKle : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have htt : Cardinal.aleph0 < Cardinal.mk t := by
    first
    | (by_contra hle
       have h := IsAlgClosed.cardinal_le_max_transcendence_basis _ ht
       exact absurd (h.trans (max_le (max_le hKle (not_lt.mp hle)) le_rfl)) (not_le.mpr hC))
    | (have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hKle hC
       rw [Cardinal.lift_inj] at h
       rw [h] at hC
       exact hC)
  have hst : Cardinal.mk s ≤ Cardinal.mk t := Cardinal.mk_le_aleph0.trans htt.le
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hst
  let u : s → ℂ := fun i => ((e i : t) : ℂ)
  have hu : AlgebraicIndependent K u := ht.1.comp e e.injective
  let E := hs.1.aevalEquiv.symm.trans hu.aevalEquiv
  let φ : Algebra.adjoin K (Set.range (Subtype.val : s → Ω)) →ₐ[K] ℂ :=
    (Algebra.adjoin K (Set.range u)).val.comp E.toAlgHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp E.injective
  letI : Algebra (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    hs.isAlgebraic
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    NoZeroSMulDivisors.of_algebraMap_injective hφ
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ ℂ).mpr hφ
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    NoZeroSMulDivisors.of_algebraMap_injective Subtype.val_injective
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ Ω).mpr Subtype.val_injective
  let g : Ω →ₐ[Algebra.adjoin K (Set.range (Subtype.val : s → Ω))] ℂ := IsAlgClosed.lift
  refine ⟨g.toRingHom, ?_⟩
  ext k
  have h1 : algebraMap K Ω k = algebraMap (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω
      (algebraMap K (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) k) := by
    first
    | rfl
  show g (algebraMap K Ω k) = sg k
  rw [h1, g.commutes]
  exact φ.commutes k

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

def RegLaw {Λ Wt : Type*} (Forms : Wt → Type*) (Pt Pt' : Λ → Type*)
    (emb : ∀ la, Pt la → Pt' la) (v : ∀ la, Pt' la → ∀ {w : Wt}, Forms w → EReal)
    (Q : Type*) (ord : Q → ∀ {w : Wt}, Forms w → EReal)
    (NoZero : ∀ {w : Wt} {n : ℕ}, (Fin n → Forms w) → Prop) : Prop :=

  (∀ (w : Wt) (F : Forms w),
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) F) →
      (∀ la (y' : Pt' la), 0 ≤ v la y' F) ∧ ∀ q : Q, 0 ≤ ord q F) ∧

  (∀ (wL wE : Wt) (n : ℕ) (ws : Fin n → Forms wL) (et : Forms wE) (nu : Λ → ℝ) (c' : ℝ),
    0 ≤ c' → NoZero ws →
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) et ∧ (v la (emb la y) et ≠ ⊤ →
      (⨅ k, v la (emb la y) (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la (emb la y) et)) →
    (∀ la (y' : Pt' la), 0 ≤ v la y' et ∧ (v la y' et ≠ ⊤ →
      (⨅ k, v la y' (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la y' et)) ∧
    ∀ q : Q, 0 ≤ ord q et ∧ (ord q et ≠ ⊤ → (⨅ k, ord q (ws k)) ≤ (c' : EReal) * ord q et))

end ReciprocityTheory.ChartRestriction.G.T0
end
