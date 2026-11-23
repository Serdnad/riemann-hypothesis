module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FaithfulIntegralClosure
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle056
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

open MvPolynomial in
theorem exists_pderiv_not_dvd {K σ : Type*} [Field K] [CharZero K] (π : MvPolynomial σ K)
    (hπ : Prime π) : ∃ j, ¬ π ∣ pderiv j π := by
  classical
  have hT : π.totalDegree ≠ 0 := by
    intro h
    have hC := totalDegree_eq_zero_iff_eq_C.1 h
    by_cases ha : π.coeff 0 = 0
    · rw [ha, map_zero] at hC
      exact hπ.ne_zero hC
    · apply hπ.not_isUnit
      rw [hC]
      exact (IsUnit.mk0 _ ha).map C
  have h1 : ¬ ∀ m ∈ π.support, ∀ x, m x = 0 := by
    rwa [← totalDegree_eq_zero_iff]
  push Not at h1
  obtain ⟨m, hm, j, hj⟩ := h1
  refine ⟨j, fun hd => ?_⟩
  have hm' : (m - Finsupp.single j 1) + Finsupp.single j 1 = m := by
    ext i
    by_cases hi : i = j
    · subst hi
      simp
      omega
    · simp [Ne.symm hi]
  have hne : pderiv j π ≠ 0 := by
    intro h0
    have h2 := coeff_pderiv (i := j) π (m - Finsupp.single j 1)
    rw [h0, hm', AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h2
    have h3 : (((m - Finsupp.single j 1 : σ →₀ ℕ) j : ℕ) + 1 : K) ≠ 0 := by
      exact Nat.cast_add_one_ne_zero _
    exact mul_ne_zero (mem_support_iff.1 hm) h3 h2.symm
  obtain ⟨q, hq⟩ := hd
  have hq0 : q ≠ 0 := fun h => hne (by rw [hq, h, mul_zero])
  have hdeg : (pderiv j π).totalDegree = π.totalDegree + q.totalDegree := by
    rw [hq]; exact totalDegree_mul_of_isDomain hπ.ne_zero hq0
  have hlt : (pderiv j π).totalDegree < π.totalDegree := by
    have : (pderiv j π).totalDegree + 1 ≤ π.totalDegree := by
      have h4 : ∀ s ∈ (pderiv j π).support, s.sum (fun _ e => e) + 1 ≤ π.totalDegree := by
        intro s hs
        have h5 : s + Finsupp.single j 1 ∈ π.support := by
          rw [mem_support_iff] at hs ⊢
          intro h6
          apply hs
          rw [coeff_pderiv, h6, zero_mul]
        have := le_totalDegree h5
        rwa [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_single_index rfl] at this
      obtain ⟨s, hs, hs'⟩ : ∃ s ∈ (pderiv j π).support, (pderiv j π).totalDegree = s.sum (fun _ e => e) := by
        rw [totalDegree]
        obtain ⟨s, hs, hs'⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.2 hne) (fun s : σ →₀ ℕ => s.sum fun _ e => e)
        exact ⟨s, hs, hs'⟩
      rw [hs']; exact h4 s hs
    omega
  omega

theorem finite_frac {A B F L : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Field F] [Field L] [Algebra A F] [IsFractionRing A F]
    [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
    [IsScalarTower A B L] : FiniteDimensional F L := by
  classical
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule A B).FG)
  let W := IntermediateField.adjoin F ((T.image (algebraMap B L) : Finset L) : Set L)
  have hint : ∀ x ∈ ((T.image (algebraMap B L) : Finset L) : Set L), IsIntegral F x := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨t, -, rfl⟩ := hx
    have h1 : IsIntegral A t := IsIntegral.of_finite A t
    exact (h1.algebraMap (B := L)).tower_top
  haveI : FiniteDimensional F W :=
    IntermediateField.finiteDimensional_adjoin hint
  have hB : ∀ x : B, algebraMap B L x ∈ W := by
    intro x
    have hx : x ∈ Submodule.span A (T : Set B) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem s hs =>
      refine IntermediateField.subset_adjoin _ _ ?_
      simp only [Finset.coe_image]
      exact ⟨s, hs, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
    | smul r a _ ha =>
      have h1 : algebraMap B L (r • a) = algebraMap F L (algebraMap A F r) * algebraMap B L a := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [h1]
      exact W.mul_mem (W.algebraMap_mem _) ha
  have hW : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact W.div_mem (hB a) (hB s)
  have key : ∀ W' : IntermediateField F L, FiniteDimensional F W' → W' = ⊤ →
      FiniteDimensional F L := by
    rintro _ h rfl
    exact (IntermediateField.topEquiv (F := F) (E := L)).toLinearEquiv.finiteDimensional
  exact key W inferInstance hW

open Polynomial in
theorem integral_of_range {A R L : Type*} [CommRing A] [CommRing R] [Field L] [Algebra A L]
    [Algebra R L] (hr : ∀ a : A, algebraMap A L a ∈ (algebraMap R L).range) (x : L)
    (h : IsIntegral A x) : IsIntegral R x := by
  obtain ⟨p, hp, h0⟩ := h
  have hl : p.map (algebraMap A L) ∈ Polynomial.lifts (algebraMap R L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact hr _
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map]
  exact h0

end GlobalTheory.CompanionTheory.TraceJac

namespace GlobalTheory.CompanionTheory.TraceJac

theorem at_prime_abs {P L F R n : Type*} [CommRing P] [IsDomain P] [IsNoetherianRing P] [Field L]
    [Field F] [CommRing R] [Algebra P R] [Algebra P F] [Algebra P L] [Algebra R F]
    [IsScalarTower P R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [IsScalarTower P R L]
    [IsFractionRing P F] [FiniteDimensional F L] [Algebra.IsSeparable F L] [Fintype n]
    [DecidableEq n] (π : P) (hπ : Prime π) (p : Ideal P) [p.IsPrime] (hp : p = Ideal.span {π})
    [IsLocalization.AtPrime R p] (E : n → Derivation ℤ L L)
    (hE : ∀ k f, ∃ f', E k (algebraMap P L f) = algebraMap P L f') (j : n) (fj : P)
    (hfj : E j (algebraMap P L π) = algebraMap P L fj) (hj : ¬ π ∣ fj)
    (hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R))
    (c : L) (hc : IsIntegral R c) (b : n → L) (hb : ∀ l, IsIntegral R (b l)) :
    ∃ f s : P, ¬ π ∣ s ∧
      algebraMap P F s * Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) =
        algebraMap P F f := by
  classical
  have hmem : ∀ s, s ∈ p ↔ π ∣ s := fun s => by rw [hp, Ideal.mem_span_singleton]
  have hmemM : ∀ s, s ∈ p.primeCompl ↔ ¬ π ∣ s := fun s => by
    rw [Ideal.mem_primeCompl_iff, hmem]
  haveI : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors R
    p.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing p.primeCompl R inferInstance
  haveI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p
  haveI : IsFractionRing R F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl R F
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap P R π} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p R, hp, Ideal.map_span, Set.image_singleton]
  have hπR0 : algebraMap P R π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact IsLocalization.injective R (M := p.primeCompl) p.primeCompl_le_nonZeroDivisors
      (h.trans (map_zero _).symm)
  have hnf : ¬ IsField R := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax]
    simpa using hπR0
  have hprin : (IsLocalRing.maximalIdeal R).IsPrincipal := ⟨⟨_, hmax⟩⟩
  haveI : IsDiscreteValuationRing R := by
    have h5 := (IsDiscreteValuationRing.TFAE R hnf).out 1 5
    exact h5.2 hprin
  have hirr : Irreducible (algebraMap P R π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  have hρP : ∀ f, algebraMap R L (algebraMap P R f) = algebraMap P L f := fun f =>
    (IsScalarTower.algebraMap_apply P R L f).symm
  have hR : ∀ k (r : R), ∃ r' : R, E k (algebraMap R L r) = algebraMap R L r' := by
    intro k r
    obtain ⟨f, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
    have h1 := IsLocalization.mk'_spec R f s
    obtain ⟨w, hw⟩ := (IsLocalization.map_units R s).exists_right_inv
    obtain ⟨f1, hf1⟩ := hE k f
    obtain ⟨s1, hs1⟩ := hE k (s : P)
    refine ⟨(algebraMap P R f1 - IsLocalization.mk' R f s * algebraMap P R s1) * w, ?_⟩
    set x := algebraMap R L (IsLocalization.mk' R f s) with hx
    have h2 : x * algebraMap P L s = algebraMap P L f := by
      rw [hx, ← hρP, ← hρP, ← map_mul, h1]
    have h3 : algebraMap P L s * algebraMap R L w = 1 := by
      rw [← hρP, ← map_mul, hw, map_one]
    have h4 := congrArg (E k) h2
    rw [Derivation.leibniz, hf1, hs1] at h4
    simp only [smul_eq_mul] at h4
    rw [map_mul, map_sub, map_mul, hρP, hρP, ← hx, ← h4]
    linear_combination (-E k x) * h3
  obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨fj, (hmemM _).2 hj⟩ : p.primeCompl)
  obtain ⟨r, hr⟩ := trace_jac_dvr (F := F) hnat E hR (algebraMap P R π) hirr j u
    (by rw [hρP, hfj, hu, hρP]) c hc b hb
  obtain ⟨f, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
  refine ⟨f, s, (hmemM _).1 s.2, ?_⟩
  rw [← hr, IsScalarTower.algebraMap_apply P R F, IsScalarTower.algebraMap_apply P R F f,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

end GlobalTheory.CompanionTheory.TraceJac
end

section

open Polynomial

namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def preserving (I : Submodule ℂ V) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {f | ∀ F ∈ I, f F ∈ I}
  mul_mem' {f g} hf hg F hF := hf _ (hg F hF)
  add_mem' {f g} hf hg F hF := I.add_mem (hf F hF) (hg F hF)
  algebraMap_mem' r F hF := by
    simp only [Set.mem_setOf_eq, Module.algebraMap_end_apply]
    exact I.smul_mem r hF

lemma pow_apply_mem (D : Module.End ℂ V) (Wn : Submodule ℂ V) (hD : ∀ F ∈ Wn, D F ∈ Wn) :
    ∀ n : ℕ, ∀ F ∈ Wn, (D ^ n) F ∈ Wn := by
  intro n
  induction n with
  | zero => intro F hF; simpa using hF
  | succ n ih =>
    intro F hF
    rw [pow_succ', Module.End.mul_apply]
    exact hD _ (ih F hF)

lemma pow_sub_pow_mem (β D : Module.End ℂ V) (Wn I : Submodule ℂ V)
    (hβ : ∀ F ∈ I, β F ∈ I) (hD : ∀ F ∈ Wn, D F ∈ Wn) (hDβ : ∀ F ∈ Wn, D F - β F ∈ I) :
    ∀ n : ℕ, ∀ F ∈ Wn, (β ^ n) F - (D ^ n) F ∈ I := by
  intro n
  induction n with
  | zero => intro F _; simp
  | succ n ih =>
    intro F hF
    have h1 := hβ _ (ih F hF)
    have h2 := hDβ _ (pow_apply_mem D Wn hD n F hF)
    have : (β ^ (n + 1)) F - (D ^ (n + 1)) F
        = β ((β ^ n) F - (D ^ n) F) - (D ((D ^ n) F) - β ((D ^ n) F)) := by
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, map_sub]
      abel
    rw [this]
    exact I.sub_mem h1 h2

lemma aeval_sub_aeval_mem (β D : Module.End ℂ V) (Wn I : Submodule ℂ V)
    (hβ : ∀ F ∈ I, β F ∈ I) (hD : ∀ F ∈ Wn, D F ∈ Wn) (hDβ : ∀ F ∈ Wn, D F - β F ∈ I)
    (p : ℂ[X]) : ∀ F ∈ Wn, (aeval β p) F - (aeval D p) F ∈ I := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro F hF
    have := I.add_mem (hp F hF) (hq F hF)
    simp only [map_add (f := _), LinearMap.add_apply]
    convert this using 1
    abel
  | monomial n c =>
    intro F hF
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [← smul_sub]
    exact I.smul_mem c (pow_sub_pow_mem β D Wn I hβ hD hDβ n F hF)

lemma isIntegral_eval {A : Type} [CommRing A] [Algebra ℂ A] (P : A[X])
    (h : ∀ k, IsIntegral ℂ (P.coeff k)) (x : A) (hx : IsIntegral ℂ x) :
    IsIntegral ℂ (P.eval x) := by
  rw [Polynomial.eval_eq_sum_range]
  exact (integralClosure ℂ A).sum_mem fun i _ =>
    (integralClosure ℂ A).mul_mem (h i) ((integralClosure ℂ A).pow_mem hx _)

end GlobalTheory.CompanionTheory.Dblock.CentreBlocks

namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks

noncomputable def sumPoly {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) : A[X] :=
  ∑ k ∈ Finset.range (n + 1), C (c k) * X ^ k

lemma sumPoly_eval {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) (x : A) :
    (sumPoly c n).eval x = ∑ k ∈ Finset.range (n + 1), c k * x ^ k := by
  simp [sumPoly, Polynomial.eval_finsetSum]

lemma sumPoly_coeff {A : Type} [CommRing A] (c : ℕ → A) (n m : ℕ) :
    (sumPoly c n).coeff m = if m < n + 1 then c m else 0 := by
  simp [sumPoly, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow]

lemma sumPoly_monic {A : Type} [CommRing A] (c : ℕ → A) (n : ℕ) (h : c n = 1) :
    (sumPoly c n).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  · rw [sumPoly_coeff]; simp [h]

theorem monic_relations_to_blocks : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (D R S : ℂ → Module.End ℂ V) (Wn I : Submodule ℂ V) (W₀ : Set V) (c₁ c₂ : ℂ) (n₁ n₂ : ℕ) (a b : ℕ → Module.End ℂ V), (∀ u v, Commute (R u) (R v)) → (∀ u v, Commute (R u) (S v)) → (∀ u v, Commute (S u) (S v)) → (∀ u, ∀ F ∈ Wn, D u F ∈ Wn) → (∀ u, ∀ F ∈ I, R u F ∈ I) → (∀ u, ∀ F ∈ I, S u F ∈ I) → (∀ u, ∀ F ∈ Wn, D u F - S (u + c₂) (R (u + c₁) F) ∈ I) → a n₁ = 1 → (∀ k, a k ∈ Submodule.span ℂ (Set.range R)) → (∀ u : ℂ, R u = ∑ k ∈ Finset.range (n₁ + 1), u ^ k • a k) → b n₂ = 1 → (∀ k, b k ∈ Submodule.span ℂ (Set.range S)) → (∀ u : ℂ, S u = ∑ k ∈ Finset.range (n₂ + 1), u ^ k • b k) → W₀ ⊆ Wn → (∀ u, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (D u) p F = 0) → (∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (R u) q F ∈ I) ∧ ∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (S u) q F ∈ I := by
  intro V _ _ D R S Wn I W₀ c₁ c₂ n₁ n₂ a b hRR hRS hSS hD hRI hSI hDβ ha1 haspan hRform hb1
    hbspan hSform hW0 hp
  let s : Set (Module.End ℂ V) := Set.range R ∪ Set.range S
  have hcomm : s.Pairwise Commute := by
    rintro x (⟨u, rfl⟩ | ⟨u, rfl⟩) y (⟨v, rfl⟩ | ⟨v, rfl⟩) _
    · exact hRR u v
    · exact hRS u v
    · exact (hRS v u).symm
    · exact hSS u v
  letI : IsMulCommutative (Algebra.adjoin ℂ s) := Algebra.isMulCommutative_adjoin ℂ hcomm
  letI : CommRing (Algebra.adjoin ℂ s) := open scoped IsMulCommutative in inferInstance
  have hpres : Algebra.adjoin ℂ s ≤ preserving I := by
    rw [Algebra.adjoin_le_iff]
    rintro x (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact hRI u
    · exact hSI u
  let Y : Ideal (Algebra.adjoin ℂ s) :=
    { carrier := {x | ∀ F ∈ W₀, (x : Module.End ℂ V) F ∈ I}
      add_mem' := fun {x y} hx hy F hF => by
        simpa using I.add_mem (hx F hF) (hy F hF)
      zero_mem' := fun F _ => by simp
      smul_mem' := fun c x hx F hF => by
        show ((c * x : Algebra.adjoin ℂ s) : Module.End ℂ V) F ∈ I
        rw [Subalgebra.coe_mul, Module.End.mul_apply]
        exact hpres c.2 _ (hx F hF) }
  let π := Ideal.Quotient.mkₐ ℂ Y
  have hRmem : ∀ u, R u ∈ Algebra.adjoin ℂ s := fun u => Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)
  have hSmem : ∀ u, S u ∈ Algebra.adjoin ℂ s := fun u => Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)
  have hamem : ∀ k, a k ∈ Algebra.adjoin ℂ s := fun k =>
    (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin ℂ s))).mpr
      (by rintro x ⟨u, rfl⟩; exact hRmem u) (haspan k)
  have hbmem : ∀ k, b k ∈ Algebra.adjoin ℂ s := fun k =>
    (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin ℂ s))).mpr
      (by rintro x ⟨u, rfl⟩; exact hSmem u) (hbspan k)
  let P : (Algebra.adjoin ℂ s ⧸ Y)[X] := sumPoly (fun k => π ⟨a k, hamem k⟩) n₁
  let Q : (Algebra.adjoin ℂ s ⧸ Y)[X] := sumPoly (fun k => π ⟨b k, hbmem k⟩) n₂
  have hPm : P.Monic := sumPoly_monic _ _ (by
    have : (⟨a n₁, hamem n₁⟩ : Algebra.adjoin ℂ s) = 1 := Subtype.ext ha1
    change π ⟨a n₁, hamem n₁⟩ = 1
    rw [this, map_one])
  have hQm : Q.Monic := sumPoly_monic _ _ (by
    have : (⟨b n₂, hbmem n₂⟩ : Algebra.adjoin ℂ s) = 1 := Subtype.ext hb1
    change π ⟨b n₂, hbmem n₂⟩ = 1
    rw [this, map_one])
  have hPev : ∀ t : ℂ, P.eval (algebraMap ℂ _ t) = π ⟨R t, hRmem t⟩ := by
    intro t
    have : (⟨R t, hRmem t⟩ : Algebra.adjoin ℂ s)
        = ∑ k ∈ Finset.range (n₁ + 1), t ^ k • (⟨a k, hamem k⟩ : Algebra.adjoin ℂ s) := by
      apply Subtype.ext; simp [hRform t]

    rw [this, map_sum, sumPoly_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, map_pow, mul_comm]
  have hQev : ∀ t : ℂ, Q.eval (algebraMap ℂ _ t) = π ⟨S t, hSmem t⟩ := by
    intro t
    have : (⟨S t, hSmem t⟩ : Algebra.adjoin ℂ s)
        = ∑ k ∈ Finset.range (n₂ + 1), t ^ k • (⟨b k, hbmem k⟩ : Algebra.adjoin ℂ s) := by
      apply Subtype.ext; simp [hSform t]

    rw [this, map_sum, sumPoly_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, map_pow, mul_comm]
  have hβ : ∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ _ (u + c₁)) *
      Q.eval (algebraMap ℂ _ (u + c₂))) := by
    intro u
    rw [hPev, hQev, ← map_mul]
    obtain ⟨p, hpm, hp0⟩ := hp u
    refine ⟨p, hpm, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    intro F hF
    rw [Polynomial.aeval_subalgebra_coe]
    have key := aeval_sub_aeval_mem (R (u + c₁) * S (u + c₂)) (D u) Wn I
      (hpres (mul_mem (hRmem _) (hSmem _))) (hD u)
      (fun F hF => by rw [(hRS _ _).eq]; exact hDβ u F hF) p F (hW0 hF)
    rw [hp0 F hF, sub_zero] at key
    exact key
  have hcoef := GlobalTheory.T.monic_factor_coefficients_integral (Algebra.adjoin ℂ s ⧸ Y) P Q c₁ c₂ hPm hQm hβ
  refine ⟨fun u => ?_, fun u => ?_⟩
  · have hint : IsIntegral ℂ (π ⟨R u, hRmem u⟩) := by
      rw [← hPev]
      exact isIntegral_eval P (fun k => (hcoef k).1) _ isIntegral_algebraMap
    obtain ⟨q, hqm, hq0⟩ := hint
    refine ⟨q, hqm, fun F hF => ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hq0
    have := hq0 F hF
    rwa [Polynomial.aeval_subalgebra_coe] at this
  · have hint : IsIntegral ℂ (π ⟨S u, hSmem u⟩) := by
      rw [← hQev]
      exact isIntegral_eval Q (fun k => (hcoef k).2) _ isIntegral_algebraMap
    obtain ⟨q, hqm, hq0⟩ := hint
    refine ⟨q, hqm, fun F hF => ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hq0
    have := hq0 F hF
    rwa [Polynomial.aeval_subalgebra_coe] at this

end GlobalTheory.CompanionTheory.Dblock.CentreBlocks
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_restrictScalars_toLin' {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((Matrix.toLin' D).restrictScalars ℝ) = Complex.normSq (Matrix.det D) := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem lintegral_eq_normSq_det_mul_lintegral_mulVec (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : Matrix.det D ≠ 0) (g : (Fin n → ℂ) → ENNReal) (hg : Measurable g) :
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' D).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq (Matrix.det D) := det_restrictScalars_toLin' D
  have hpos : 0 < Complex.normSq (Matrix.det D) := Complex.normSq_pos.mpr hD
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact hpos.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin n → ℂ)) hne
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have key : ∫⁻ v, g (D *ᵥ v) = ENNReal.ofReal (Complex.normSq (Matrix.det D))⁻¹ * ∫⁻ u, g u := by
    have e : ∀ v, D *ᵥ v = f v := fun v => by simp [hf, Matrix.toLin'_apply]
    simp_rw [e]
    rw [← lintegral_map hg hfm, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.mpr hpos), smul_eq_mul]
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
    one_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
