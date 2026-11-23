module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionBundle
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
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
import Mathlib.RingTheory.LocalProperties.Reduced
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

def restrictUnion (I J : Chart y) : Chart y :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem redAt_isUnit_of_isUnit {I J : Chart y} (h : I.1 ⊆ J.1)
    (a : chartRing k x (liftChart hxy I))
    (ha : IsUnit (chartIncl (S := k) (x := x) (I := liftChart hxy I) (J := liftChart hxy J) h a)) :
    (a : Ω) ∈ locAt k x y ∧ ∃ b ∈ chartRing k y J, redAt k x y a * b = 1 := by
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  have hc' : (a : Ω) * (c : Ω) = 1 := congrArg Subtype.val hc
  have haL := chartRing_sub_locAt hsp hxy I a.2
  have hcL := chartRing_sub_locAt hsp hxy J c.2
  refine ⟨haL.1, _, hcL.2, ?_⟩
  rw [← (locAt_mul hsp haL.1 hcL.1).2, hc', (locAt_one hsp).2]

theorem exists_mul_mem_of_mem_restrictUnion (Q : LineBundle k x) (I J : Chart y) {z : Ω}
    (hz : z ∈ Q.sub (liftChart hxy (restrictUnion I J))) :
    ∃ a ∈ chartRing k x (liftChart hxy I), a ∈ locAt k x y ∧ redAt k x y a ≠ 0 ∧
      a * z ∈ Q.sub (liftChart hxy I) := by
  have hIJ : I.1 ⊆ (restrictUnion I J).1 := Finset.subset_union_left
  obtain ⟨a, ha, haz⟩ := (Q.mem_iff (liftChart hxy I) (liftChart hxy (restrictUnion I J)) hIJ z).mp hz
  obtain ⟨haL, b, -, hb⟩ := redAt_isUnit_of_isUnit hsp hxy hIJ a ha
  rw [smul_eq_mul] at haz
  exact ⟨a, a.2, haL, left_ne_zero_of_mul_eq_one hb, haz⟩

theorem exists_restrict_gen (Q : LineBundle k x) :
    ∃ γ : Ω, γ ≠ 0 ∧ RedGood hxy Q.toSubSystem γ ∧ ∀ I : Chart y,
      ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
        b * γ ∈ Q.sub (liftChart hxy I) := by
  by_cases hI : Nonempty (Chart y)
  swap
  · exact ⟨1, one_ne_zero, fun I => (hI ⟨I⟩).elim, fun I => (hI ⟨I⟩).elim⟩
  obtain ⟨I₀⟩ := hI
  obtain ⟨M, hM⟩ := Q.invertible (liftChart hxy I₀)
  have hA : ∀ {q m : Ω}, q ∈ Q.sub (liftChart hxy I₀) → m ∈ M → q * m ∈ locAt k x y :=
    fun hq hm => (chartRing_sub_locAt hsp hxy I₀ (mul_mem_chartRing_of_mul_eq_one hM hq hm)).1
  have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy I₀) * M := by
    rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨γ, hγ, m₀, hm₀, hne⟩ :
      ∃ γ ∈ Q.sub (liftChart hxy I₀), ∃ m₀ ∈ M, redAt k x y (γ * m₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z = 0) h1
      (fun q hq m hm => ⟨hA hq hm, hcon q hq m hm⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2, hu.2, hv.2, add_zero]⟩)
    rw [(locAt_one hsp).2] at this
    exact one_ne_zero this.2
  have hγm := hA hγ hm₀
  have hγm0 := (locAt_inv hsp hγm hne).1
  have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hγm0
  have hm0 : m₀ ≠ 0 := right_ne_zero_of_mul hγm0
  refine ⟨γ, hγ0, ?_, ?_⟩
  · intro I q hq
    have hsub : I.1 ⊆ (restrictUnion I₀ I).1 := Finset.subset_union_right
    obtain ⟨a, -, haL, har, haq⟩ := exists_mul_mem_of_mem_restrictUnion hsp hxy Q I₀ I
      (Q.mono (liftChart hxy I) (liftChart hxy (restrictUnion I₀ I)) hsub q hq)
    have ha0 : a ≠ 0 := (locAt_inv hsp haL har).1
    have hnum := hA haq hm₀
    have hden := locAt_mul hsp haL hγm
    have hden0 : redAt k x y (a * (γ * m₀)) ≠ 0 := by rw [hden.2]; exact mul_ne_zero har hne
    have heq : q / γ = a * q * m₀ / (a * (γ * m₀)) := by
      rw [mul_assoc a q m₀, mul_div_mul_left _ _ ha0, mul_div_mul_right _ _ hm0]
    rw [heq]; exact (locAt_div hsp hnum hden.1 hden0).1
  · intro I
    have hsub : I₀.1 ⊆ (restrictUnion I I₀).1 := Finset.subset_union_right
    exact exists_mul_mem_of_mem_restrictUnion hsp hxy Q I I₀
      (Q.mono (liftChart hxy I₀) (liftChart hxy (restrictUnion I I₀)) hsub γ hγ)

variable {γ : Ω} {Q : LineBundle k x}

theorem redSys_sub_eq_span (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y) {s : Set Ω}
    (hs : Submodule.span (chartRing k x (liftChart hxy I)) s = Q.sub (liftChart hxy I)) :
    (redSys hxy Q.toSubSystem γ).sub I =
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Submodule.span (chartRing k x (liftChart hxy I)) s := by rw [hs]; exact hq
    refine Submodule.span_induction (p := fun q _ => redAt k x y (q / γ) ∈
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s)) ?_ ?_ ?_ ?_ hq'
    · intro q hq; exact Submodule.subset_span ⟨q, hq, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hg I u (hs ▸ hu)) (hg I v (hs ▸ hv))).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hg I u (hs ▸ hu))).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Q.sub (liftChart hxy I) := by rw [← hs]; exact Submodule.subset_span hq
    exact Submodule.subset_span ⟨q, hq', rfl⟩

theorem redSys_mem_iff (hg : RedGood hxy Q.toSubSystem γ) (I J : Chart y) (h : I.1 ⊆ J.1) (z : K') :
    z ∈ (redSys hxy Q.toSubSystem γ).sub J ↔ ∃ c : chartRing k y I, IsUnit (chartIncl h c) ∧
      (c : K') • z ∈ (redSys hxy Q.toSubSystem γ).sub I := by
  constructor
  · intro hz
    obtain ⟨q, hq, rfl⟩ := (mem_redSys_iff hsp hxy hg J z).mp hz
    obtain ⟨b, hb, hbq⟩ := (Q.mem_iff (liftChart hxy I) (liftChart hxy J) h q).mp hq
    obtain ⟨hbL, b', hb'A, hbb'⟩ := redAt_isUnit_of_isUnit hsp hxy h b hb
    have hbI := (chartRing_sub_locAt hsp hxy I b.2).2
    refine ⟨⟨_, hbI⟩, IsUnit.of_mul_eq_one ⟨b', hb'A⟩ (Subtype.ext hbb'), ?_⟩
    rw [smul_eq_mul] at hbq
    change redAt k x y b * redAt k x y (q / γ) ∈ (redSys hxy Q.toSubSystem γ).sub I
    rw [← (locAt_mul hsp hbL (hg J q hq)).2, ← mul_div_assoc]
    exact Submodule.subset_span ⟨_, hbq, rfl⟩
  · rintro ⟨c, hc, hcz⟩
    obtain ⟨c', hc'⟩ := hc.exists_left_inv
    have hc'' : (c' : K') * (c : K') = 1 := congrArg Subtype.val hc'
    have := Submodule.smul_mem _ c' ((redSys hxy Q.toSubSystem γ).mono I J h _ hcz)
    rwa [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hc'', one_mul] at this

theorem redSys_invertible (hγ0 : γ ≠ 0) (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y)
    (hb : ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
      b * γ ∈ Q.sub (liftChart hxy I)) :
    ∃ M' : Submodule (chartRing k y I) K', (redSys hxy Q.toSubSystem γ).sub I * M' = 1 := by
  obtain ⟨b, -, hbL, hbr, hbγ⟩ := hb
  obtain ⟨M, hM⟩ := Q.invertible (liftChart hxy I)
  refine ⟨Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * γ)) '' M), ?_⟩
  have hA : ∀ {q m : Ω}, q ∈ Q.sub (liftChart hxy I) → m ∈ M →
      q * m ∈ chartRing k x (liftChart hxy I) :=
    fun hq hm => mul_mem_chartRing_of_mul_eq_one hM hq hm
  have hb0 : b ≠ 0 := (locAt_inv hsp hbL hbr).1
  have hmg : ∀ {m : Ω}, m ∈ M → m * γ ∈ locAt k x y := by
    intro m hm
    have h1 := (chartRing_sub_locAt hsp hxy I (hA hbγ hm)).1
    have heq : m * γ = b * γ * m / b := by rw [eq_div_iff hb0]; ring
    rw [heq]; exact (locAt_div hsp h1 hbL hbr).1
  have hsplit : ∀ q m : Ω, q * m = q / γ * (m * γ) := fun q m => by field_simp
  apply le_antisymm
  · change Submodule.span _ _ * Submodule.span _ _ ≤ 1
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨q, hq, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
    show redAt k x y (q / γ) * redAt k x y (m * γ) ∈ (1 : Submodule (chartRing k y I) K')
    rw [← (locAt_mul hsp (hg I q hq) (hmg hm)).2, ← hsplit]
    exact Submodule.mem_one.mpr ⟨⟨_, (chartRing_sub_locAt hsp hxy I (hA hq hm)).2⟩, rfl⟩
  · rw [Submodule.one_le]
    have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy I) * M := by
      rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z ∈
        (redSys hxy Q.toSubSystem γ).sub I *
          Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * γ)) '' M)) h1
      (fun q hq m hm => ⟨(chartRing_sub_locAt hsp hxy I (hA hq hm)).1, by
        rw [hsplit, (locAt_mul hsp (hg I q hq) (hmg hm)).2]
        exact Submodule.mul_mem_mul (Submodule.subset_span ⟨q, hq, rfl⟩)
          (Submodule.subset_span ⟨m, hm, rfl⟩)⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2]; exact Submodule.add_mem _ hu.2 hv.2⟩)
    rw [(locAt_one hsp).2] at this
    exact this.2


end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type} [Field F]


omit [Fintype K] in
theorem segre_weight_mapDomain (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (segreIdx ι))
        (Finsupp.mapDomain (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) e) =
      Sum.elim (fun _ => 0) (Finsupp.weight (NumbersDVR.blockWeight ι) e) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index
      (h := fun (v : Σ c, segreIdx ι c) (n : ℕ) => n • NumbersDVR.blockWeight (segreIdx ι) v)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext c
  rcases c with ⟨⟨⟩⟩ | k
  · simp [Finsupp.sum, Finset.sum_apply, NumbersDVR.blockWeight]
  · simp [Finsupp.sum, Finset.sum_apply, NumbersDVR.blockWeight, Pi.single_apply]

theorem segreIncl_weightedHomogeneousComponent (b : K → ℕ) (f : MRing ι F) :
    segreIncl ι F (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (segreIdx ι)) (Sum.elim (fun _ => 0) b)
        (segreIncl ι F f) := by
  classical
  have hinj : Function.Injective (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) := by
    rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 := Sigma.mk.inj h
    obtain rfl := Sum.inr_injective h1.1
    obtain rfl := eq_of_heq h1.2
    rfl
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain
      (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [segreIncl, coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj,
      coeff_weightedHomogeneousComponent, segre_weight_mapDomain]
    by_cases hd : Finsupp.weight (NumbersDVR.blockWeight ι) e = b
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (funext fun k => congrFun h (Sum.inr k))]
  · push Not at he
    rw [segreIncl, coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

theorem segreLiftVal_eq (W : Ideal (MRing ι F)) (v : Σ c, segreIdx ι c) :
    ∃ β, segreLiftVal ι F W v =
      Polynomial.X ^ (NumbersDVR.blockWeight (segreIdx ι) v (Sum.inl ())) * Polynomial.C β := by
  rcases v with ⟨⟨⟨⟩⟩ | k, i⟩
  · exact ⟨Ideal.Quotient.mk W (∏ k, X ⟨k, i k⟩), by
      simp [segreLiftVal, NumbersDVR.blockWeight]⟩
  · exact ⟨Ideal.Quotient.mk W (X ⟨k, i⟩), by simp [segreLiftVal, NumbersDVR.blockWeight]⟩

theorem segreLiftMap_monomial (W : Ideal (MRing ι F)) (s : (Σ c, segreIdx ι c) →₀ ℕ) :
    ∀ r : F, ∃ a, segreLiftMap ι F W (monomial s r) =
      Polynomial.X ^ (Finsupp.weight (NumbersDVR.blockWeight (segreIdx ι)) s (Sum.inl ())) *
        Polynomial.C a := by
  refine Finsupp.induction s ?_ ?_
  · intro r
    refine ⟨algebraMap F _ r, ?_⟩
    simp [segreLiftMap, Polynomial.algebraMap_apply]
  · intro v n s _ _ ih r
    obtain ⟨a, ha⟩ := ih r
    obtain ⟨β, hβ⟩ := segreLiftVal_eq W v
    refine ⟨β ^ n * a, ?_⟩
    have hm : (monomial (Finsupp.single v n + s) r : MRing (segreIdx ι) F) =
        X v ^ n * monomial s r := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [hm, map_mul, map_pow, ha, segreLiftMap, aeval_X, hβ, map_add (f := _), Pi.add_apply,
      Finsupp.weight_single, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    ring

theorem segreLiftMap_of_isWeightedHomogeneous (W : Ideal (MRing ι F)) {f : MRing (segreIdx ι) F}
    {e : Unit ⊕ K → ℕ} (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight (segreIdx ι)) f e) :
    ∃ a, segreLiftMap ι F W f = Polynomial.X ^ e (Sum.inl ()) * Polynomial.C a := by
  classical
  choose a ha using fun s => segreLiftMap_monomial W s (AddMonoidAlgebra.coeff f s)
  refine ⟨∑ s ∈ f.support, a s, ?_⟩
  conv_lhs => rw [f.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [ha s, hf (mem_support_iff.mp hs)]

end

theorem SegreLiftComap.proof : SegreLiftComap.Statement := by
  intro F _ K _ _ ι _ W' hW' hrel
  classical
  have := hW'.isPrime
  have hW : IsMultiProjPrime (W'.comap (segreIncl ι F)) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · intro f hf b
      rw [Ideal.mem_comap, segreIncl_weightedHomogeneousComponent]
      exact hW'.multiHomog _ hf _
    · intro k
      obtain ⟨i, hi⟩ := hW'.relevant (Sum.inr k)
      exact ⟨i, by rwa [Ideal.mem_comap, segreIncl, rename_X]⟩
  refine ⟨hW, ?_⟩
  set W := W'.comap (segreIncl ι F) with hWdef

  choose c' hc using fun k => hW'.relevant (Sum.inr k)
  let c : ∀ k, ι k := c'
  let D := MRing (segreIdx ι) F ⧸ W'
  let L := FractionRing D
  let π : MRing (segreIdx ι) F →+* L := (algebraMap D L).comp (Ideal.Quotient.mk W')
  have hπ : ∀ f, π f = 0 ↔ f ∈ W' := by
    intro f
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective D L).eq_iff' (map_zero _)
  have hmc : segreMon (R := F) c ∉ W' := by
    intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k hk
  have hYc : segreY (R := F) c ∉ W' := by
    intro h
    obtain ⟨d, hd⟩ := hW'.relevant (Sum.inl ())
    have hr : segreY c * segreMon d - segreY d * segreMon c ∈ W' := hrel ⟨c, d, rfl⟩
    have : segreY (R := F) d * segreMon c ∈ W' := by
      have := W'.sub_mem (W'.mul_mem_right (segreMon d) h) hr
      rwa [sub_sub_cancel] at this
    exact (hW'.isPrime.mem_or_mem this).elim hd hmc
  have hMc : π (segreMon c) ≠ 0 := fun h => hmc ((hπ _).mp h)
  let u : L := π (segreY c) / π (segreMon c)
  have hu : u ≠ 0 := div_ne_zero (fun h => hYc ((hπ _).mp h)) hMc
  let j : MRing ι F ⧸ W →+* D :=
    Ideal.quotientMap W' (segreIncl ι F : MRing ι F →+* MRing (segreIdx ι) F) le_rfl
  have hj : Function.Injective j := Ideal.quotientMap_injective' le_rfl
  have hjmk : ∀ x, j (Ideal.Quotient.mk W x) = Ideal.Quotient.mk W' (segreIncl ι F x) :=
    fun x => Ideal.quotientMap_mk
  let Φ : Polynomial (MRing ι F ⧸ W) →+* L := Polynomial.eval₂RingHom ((algebraMap D L).comp j) u
  have hΦ : ∀ a, Φ (Polynomial.C a) = algebraMap D L (j a) := fun a => by
    simp [Φ]
  have hkey : ∀ f, Φ (segreLiftMap ι F W f) = π f := by
    have : Φ.comp (segreLiftMap ι F W : MRing (segreIdx ι) F →+* Polynomial (MRing ι F ⧸ W)) = π := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_C,
          Polynomial.algebraMap_apply, hΦ]
        rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, hjmk, segreIncl, rename_C]
        rfl
      · rcases v with ⟨⟨⟨⟩⟩ | k, i⟩
        · have hs : π (segreY c) * π (segreMon i) = π (segreY i) * π (segreMon c) := by
            have := (hπ _).mpr (hrel ⟨c, i, rfl⟩)
            rwa [map_sub, map_mul, map_mul, sub_eq_zero] at this
          have hinc : segreIncl ι F (∏ k, X ⟨k, i k⟩) = segreMon i := by
            simp [segreIncl, segreMon, map_prod]
          simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_X, segreLiftVal,
            map_mul, hΦ]
          simp only [Φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
          rw [hjmk, hinc]
          change u * π (segreMon i) = π (segreY i)
          rw [div_mul_eq_mul_div, div_eq_iff hMc, hs]
        · simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_X, segreLiftVal, hΦ]
          rw [hjmk, segreIncl, rename_X]
          rfl
    intro f
    exact RingHom.congr_fun this f
  ext f
  rw [segreLift, RingHom.mem_ker]
  constructor
  · intro hf

    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight (segreIdx ι)) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun e _ => ?_
    obtain ⟨a, ha⟩ := segreLiftMap_of_isWeightedHomogeneous W
      (weightedHomogeneousComponent_isWeightedHomogeneous
        (w := NumbersDVR.blockWeight (segreIdx ι)) e f)
    have h0 : Φ (Polynomial.X ^ e (Sum.inl ()) * Polynomial.C a) = 0 := by
      rw [← ha, hkey]
      exact (hπ _).mpr (hW'.multiHomog f hf e)
    rw [map_mul, map_pow, hΦ] at h0
    have h1 := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (by simpa [Φ] using hu))
    have h2 : j a = 0 := (IsFractionRing.injective D L) (by rw [h1, map_zero])
    have h3 : a = 0 := hj (by rw [h2, map_zero])
    rw [ha, h3, map_zero, mul_zero]
  · intro hf
    exact (hπ f).mp (by rw [← hkey, hf, map_zero])

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace KHCechDDeg

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem cellRes_mem_locPart {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {c : K → ℤ}
    {J I : ∀ k, Finset (ι k)} (h : KH.cellMon S J ≤ KH.cellMon S I) {x : LocalizedModule (KH.cellMon S J) M}
    (hx : x ∈ KH.locPart ι 𝓜 (KH.cellMon S J) c) :
    KH.cellRes S M J I x ∈ KH.locPart ι 𝓜 (KH.cellMon S I) c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellRes_mk h]
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep.mk_mem_locPart m ⟨t.1, h t.2⟩ a ht hm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ s hx

theorem face_subset {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, DecidableEq (ι k)]
    (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

end KHCechDDeg

theorem KHCechDDeg.full : KH.CechDDegStatement := by
  classical
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 c n φ hφ
  refine Submodule.mem_pi.mpr fun I _ => ?_
  simp only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hI
  · change KH.faceSign I.1 k i • KH.cellRes S M _ I.1 (φ ⟨_, hI⟩) ∈ _
    refine zsmul_mem (KHCechDDeg.cellRes_mem_locPart ?_ (Submodule.mem_pi.mp hφ _ (Set.mem_univ _))) _
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellMon_mono
      (KHCechDDeg.face_subset I.1 k i)
  · rw [LinearMap.zero_apply]
    exact zero_mem _

end GroundTheory.Heights₂.Heights.Kleiman
end
