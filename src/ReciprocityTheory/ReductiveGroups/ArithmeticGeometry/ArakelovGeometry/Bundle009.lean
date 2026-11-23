module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.GradedAlgebra.Radical
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.XZeroPowDvdOfIsHomogeneousAeval
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.BasisOfLinearIndependentOfCardEqFinrank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}

theorem fnField_comp_le (x : κ → Ω) (e : Fin (D + 1) → κ) : fnField (x ∘ e) ≤ fnField x := by
  exact TraceNormBounds.fnField_comp_le' x e

theorem projDeg_pos (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    0 < projDeg x e :=
  TraceNormBounds.projDeg_pos' x e h

def fnTrace (x : κ → Ω) (e : Fin (D + 1) → κ) (t : Ω) : Ω :=
  open Classical in
  if ht : t ∈ fnField x then
    ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le x e)) ⟨t, ht⟩ : fnField (x ∘ e)) : Ω)
  else 0

def secTrace (x : κ → Ω) (e : Fin (D + 1) → κ) (n : ℕ) (s : Ω) : Ω :=
  x (e 0) ^ n * fnTrace x e (s / x (e 0) ^ n)

theorem exists_indep_sections (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    ∃ (k : ℕ) (ε : Fin (projDeg x e) → Ω), (∀ l, ε l ∈ sec ℤ x k) ∧
      LinearIndependent (fnField (x ∘ e)) ε := by
  exact TraceNormBounds.exists_indep_sections' x e h

theorem secTrace_mem (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) (n : ℕ) {s : Ω}
    (hs : s ∈ sec ℤ x n) : secTrace x e n s ∈ sec ℤ (x ∘ e) n := by
  unfold secTrace fnTrace
  rw [dite_eq_left (TraceNormBounds.sec_div_mem x (e 0) hs)]
  exact TraceNormBounds.trace_mem_sec x e h n hs

theorem eq_zero_of_secTrace_mul_eq_zero (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n)
    (h0 : ∀ l, secTrace x e (n + k) (s * ε l) = 0) : s = 0 := by
  have hx0 : x (e 0) ≠ 0 := by
    intro h0
    have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
      rw [coordIdeal, RingHom.mem_ker]
      simp [coneMap, h0]
    rw [h.free] at hmem
    exact MvPolynomial.X_ne_zero 0 ((Ideal.mem_bot).1 hmem)
  refine TraceNormBounds.eq_zero_of_trace' x e h ε hε hli n hs (fun l => ?_)
  have h1 := h0 l
  unfold secTrace fnTrace at h1
  split_ifs at h1 with hm
  · exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hx0)
  · exact absurd (TraceNormBounds.sec_div_mem x (e 0) (by first | exact TraceNormBounds.mul_mem_sec x hs (hε l) | exact mul_mem_sec x hs (hε l) | exact ReciprocityTheory.ChartRestriction.G.Geo.mul_mem_sec x hs (hε l))) hm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq

attribute [local instance 2000] lexDecEq

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

def lexW (e : K ≃ Fin n) : (Σ k, ι k) → Lex (Fin n → ℕ) :=
  fun p => toLex (Pi.single (e p.1) 1)

theorem weight_lexW (e : K ≃ Fin n) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexW (ι := ι) e) m = toLex (fun j => ∑ i, m ⟨e.symm j, i⟩) := by
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • lexW (ι := ι) e i) (fun i => zero_nsmul _)]
  show (∑ p, m p • (Pi.single (e p.1) 1 : Fin n → ℕ)) = fun j => ∑ i, m ⟨e.symm j, i⟩
  funext j
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single (e.symm j)]
  · simp [Pi.single_apply]
  · intro k _ hk
    refine Finset.sum_eq_zero fun i _ => ?_
    have hjk : j ≠ e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [Pi.single_apply, hjk]
  · simp

theorem isMultiHomog_iff_lex (e : K ≃ Fin n) (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (lexW e) f (toLex (a ∘ e.symm)) := by
  constructor
  · intro h d hd
    rw [weight_lexW]
    congr 1
    funext j
    exact h d (MvPolynomial.mem_support_iff.mpr hd) (e.symm j)
  · intro h d hd k
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_lexW] at h1
    obtain ⟨j, rfl⟩ := e.symm.surjective k
    exact congrFun (toLex.injective h1) j

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomog_of_mem_lex (e : K ≃ Fin n) {f : MRing ι} {m : Lex (Fin n → ℕ)}
    (h : f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) m) :
    IsMultiHomog f (fun k => ofLex m (e k)) := by
  rw [mem_weightedHomogeneousSubmodule] at h
  rw [isMultiHomog_iff_lex e]
  have hm : (fun k => ofLex m (e k)) ∘ e.symm = ofLex m := by
    funext j
    simp
  rw [hm, toLex_ofLex]
  exact h

theorem mem_lex_of_isMultiHomog (e : K ≃ Fin n) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) (toLex (a ∘ e.symm)) := by
  rw [mem_weightedHomogeneousSubmodule]
  exact (isMultiHomog_iff_lex e f a).1 h

theorem isHomogeneous_lex_iff (e : K ≃ Fin n) (J : Ideal (MRing ι)) :
    J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) ↔ IsMultiHomogIdeal J := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ J).1 h
    refine ⟨Subtype.val '' S, ?_, hS⟩
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨i, hi⟩ := x.2
    exact ⟨_, isMultiHomog_of_mem_lex e hi⟩
  · rintro ⟨S, hS, rfl⟩
    apply Ideal.homogeneous_span
    intro x hx
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨_, mem_lex_of_isMultiHomog e ha⟩

end Lex

section Filtration

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    by_contra h
    exact hm (if_neg (Ne.symm h))
  simp [hm0]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem exists_colon_prime (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) (hJt : J ≠ ⊤) :
    ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧
      (J.colon {f}).IsPrime ∧ IsMultiHomogIdeal (J.colon {f}) := by
  let e := Fintype.equivFin K
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) :=
    (isHomogeneous_lex_iff e J).2 hJ

  have hcolh : ∀ (f : MRing ι) (d : Lex (Fin (Fintype.card K) → ℕ)),
      f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) d →
      (J.colon {f}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) := by
    intro f d hf i g hg
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
    rw [← DirectSum.coe_decompose_mul_add_of_right_mem _ hf]
    exact hJh (i + d) hg

  let S : Set (Ideal (MRing ι)) := {P | ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧ P = J.colon {f}}
  have hne : S.Nonempty := by
    refine ⟨J.colon {1}, ?_⟩
    simp only [S, Set.mem_setOf_eq]
    exact ⟨1, 0, isMultiHomog_one, fun h => hJt ((Ideal.eq_top_iff_one J).2 h), rfl⟩
  obtain ⟨P, hP, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (MRing ι) (MRing ι)) S hne
  obtain ⟨f, c, hf, hfJ, rfl⟩ := hP
  have hfm := mem_lex_of_isMultiHomog e hf
  have hPh := hcolh f _ hfm
  refine ⟨f, c, hf, hfJ, ?_, (isHomogeneous_lex_iff e _).1 hPh⟩
  apply Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem hPh
  · intro h
    apply hfJ
    have h1 : (1 : MRing ι) ∈ J.colon {f} := by rw [h]; exact Submodule.mem_top
    rwa [Submodule.mem_colon_singleton, one_smul] at h1
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    by_cases hxP : x ∈ J.colon {f}
    · exact Or.inl hxP
    right
    have hxf := SetLike.GradedMul.mul_mem hx hfm
    have hxfJ : x * f ∉ J := by rwa [Submodule.mem_colon_singleton, smul_eq_mul] at hxP
    have hmem : J.colon {x * f} ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      exact ⟨x * f, _, isMultiHomog_of_mem_lex e hxf, hxfJ, rfl⟩
    have hle : J.colon {f} ≤ J.colon {x * f} := by
      intro g hg
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
      rw [← mul_assoc, mul_comm g x, mul_assoc]
      exact J.mul_mem_left x hg
    have heq : J.colon {f} = J.colon {x * f} := by
      by_contra hne'
      exact hmax _ hmem (lt_of_le_of_ne hle hne')
    rw [heq, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hxy
    rw [← mul_assoc, mul_comm y x]
    exact hxy

theorem isMultiHomogIdeal_sup_span_via_span_union {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hJ
  refine ⟨S ∪ {f}, ?_, (Ideal.span_union _ _).symm⟩
  rintro g (hg | hg)
  · exact hS g hg
  · rw [Set.mem_singleton_iff.mp hg]
    exact ⟨c, hf⟩

theorem exists_primeFiltration_of_isMultiHomogIdeal (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = ⊤ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc := by
  induction J using WellFoundedGT.induction
  rename_i J ih
  by_cases hJt : J = ⊤
  · exact ⟨0, fun _ => J, Fin.elim0, Fin.elim0, Fin.elim0, rfl, hJt, fun j => Fin.elim0 j⟩
  obtain ⟨f, c, hf, hfJ, hprime, hqh⟩ := exists_colon_prime J hJ hJt
  have hlt : J < J ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun h =>
    hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨N, F, g, cc, q, hF0, hFl, hstep⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨N + 1, Fin.cons J F, Fin.cons f g, Fin.cons c cc, Fin.cons (J.colon {f}) q, rfl, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hFl
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨by simpa using hf, ?_, by simpa using hprime, by simpa using hqh, fun g' => ?_⟩
      · simp [hF0]
      · simp [Submodule.mem_colon_singleton, smul_eq_mul]
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      exact hstep j

end Filtration

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end
