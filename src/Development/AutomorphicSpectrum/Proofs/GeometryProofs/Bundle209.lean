module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle206
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle009
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt

open MvPolynomial

theorem norm_le_one_of_monic_eval₂ {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜] {R : Type} [CommRing R]
    (φ : R →+* 𝕜) (hφ : ∀ r, ‖φ r‖ ≤ 1) {f : Polynomial R} (hmon : f.Monic) {x : 𝕜}
    (hf : f.eval₂ φ x = 0) : ‖x‖ ≤ 1 := by
  by_contra! h
  rw [hmon.as_sum] at hf
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hf
  have hsum : x ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hf
  have hpos : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
    · rw [h0] at hsum
      simp at hsum
    · exact h0
  have hle : ‖∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (f.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ f.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖φ (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (f.natDegree - 1) :=
          mul_le_mul (hφ _) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (f.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ f.natDegree ≤ ‖x‖ ^ (f.natDegree - 1) := by
    rw [← norm_pow, hsum, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (f.natDegree - 1) < ‖x‖ ^ f.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

section Ring

variable {Ω : Type} [Field Ω] {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜]

def unitBall (A : Subring Ω) (ev : A →+* 𝕜) : Subring Ω where
  carrier := {x | ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : (⟨a * b, A.mul_mem ha hb⟩ : A) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, norm_mul]
    exact mul_le_one₀ ha1 (norm_nonneg _) hb1
  one_mem' := by
    refine ⟨A.one_mem, ?_⟩
    have e : (⟨1, A.one_mem⟩ : A) = 1 := rfl
    rw [e, map_one, norm_one]
  add_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.add_mem ha hb, ?_⟩
    have e : (⟨a + b, A.add_mem ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 hb1)
  zero_mem' := by
    refine ⟨A.zero_mem, ?_⟩
    have e : (⟨0, A.zero_mem⟩ : A) = 0 := rfl
    rw [e, map_zero, norm_zero]
    exact zero_le_one
  neg_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨A.neg_mem ha, ?_⟩
    have e : (⟨-a, A.neg_mem ha⟩ : A) = -⟨a, ha⟩ := rfl
    rw [e, map_neg, norm_neg]
    exact ha1

theorem norm_ev_le_one (A : Subring Ω) (ev : A →+* 𝕜) (R : Subalgebra ℤ Ω)
    (hR : ∀ x ∈ R, ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1) {t : Ω} (ht : t ∈ integralClosure R Ω) (hb : t ∈ A) :
    ‖ev ⟨t, hb⟩‖ ≤ 1 := by
  obtain ⟨f, hmon, hf⟩ := ht
  let ψ : R →+* A :=
    { toFun := fun r => ⟨r, (hR r r.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h1 : f.eval₂ ψ ⟨t, hb⟩ = 0 := by
    apply Subtype.ext
    exact (Polynomial.hom_eval₂ f ψ A.subtype ⟨t, hb⟩).trans hf
  have h2 : f.eval₂ (ev.comp ψ) (ev ⟨t, hb⟩) = 0 := by
    rw [← Polynomial.hom_eval₂, h1, map_zero]
  exact norm_le_one_of_monic_eval₂ (ev.comp ψ) (fun r => (hR r r.2).2) hmon h2

end Ring

section Pt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}

theorem isMultiHomog_X_single [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm b
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hb : b = k
  · subst hb
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (by simpa using h.symm)
    · simp
  · rw [Pi.single_eq_of_ne hb]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (congrArg Sigma.fst h).symm

theorem hasVal_coord [DecidableEq K] (k : K) (i : ι k) :
    Small.HasVal y (Pi.single k 1) (y ⟨k, i⟩) z (z ⟨k, i⟩) := by
  refine ⟨Pi.single k 1, 0, X ⟨k, i⟩, 1, isMultiHomog_X_single k i, ?_, fun b => ?_, by simp, by simp, by simp⟩
  · exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one
  · by_cases hb : b = k
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]

theorem hasVal_ratio_coord {k : K} (i c : ι k) (hy : y ⟨k, c⟩ ≠ 0) (hz : z ⟨k, c⟩ ≠ 0) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c⟩) z (z ⟨k, i⟩ / z ⟨k, c⟩) := by
  classical
  refine ⟨Pi.single k 1, Pi.single k 1, X ⟨k, i⟩, X ⟨k, c⟩, isMultiHomog_X_single k i, isMultiHomog_X_single k c,
    fun b => by simp, ?_, by simpa using hz, ?_⟩
  · simp only [aeval_X]
    field_simp
  · simp only [aeval_X]
    field_simp

theorem coord_ne_zero (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (p : Σ k, ι k) (h : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  have hm : (X p : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (X p) = 0
    simp [mConeMap, h0]
  exact h (by simpa using hz.2 _ hm)

end Pt

theorem exists_hasVal_norm_le_supMet :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  classical
  intro K _ ι _ Ω _ y 𝕜 _ _ z hz A ev a s hs H
  have hc : ∀ k, ∃ c : ι k, ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c⟩‖ := fun k => by
    obtain ⟨i0, -⟩ := hz.1 k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun i => ‖z ⟨k, i⟩‖)
  choose c hc using hc
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have h1 := hc k i0
    rw [h0, norm_zero] at h1
    exact hi0 (norm_le_zero_iff.1 h1)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => coord_ne_zero hz _ (hzc k)
  obtain ⟨hr, hb, hv⟩ := H c hyc
  have hle : chartRingZ y c ≤ subalgebraOfSubring (unitBall A ev) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    obtain ⟨hb', hv'⟩ := hr k i
    have e := Small.ReadFinTest.hasVal_unique hz hv' (hasVal_ratio_coord i (c k) (hyc k) (hzc k))
    refine ⟨hb', ?_⟩
    rw [e, norm_div]
    exact div_le_one_of_le₀ (hc k i) (norm_nonneg _)
  have hn : ‖ev ⟨_, hb⟩‖ ≤ 1 := norm_ev_le_one A ev _ (fun x hx => hle hx) (hs c hyc) hb
  refine ⟨ev ⟨_, hb⟩ * ∏ k, z ⟨k, c k⟩ ^ a k, ?_, ?_⟩
  · have hp : ∀ k ∈ (Finset.univ : Finset K), Small.HasVal y (a k • (Pi.single k 1 : K → ℤ)) (y ⟨k, c k⟩ ^ a k) z
        (z ⟨k, c k⟩ ^ a k) := fun k _ => hv_zpow hz (hasVal_coord k (c k)) (hyc k) (hzc k) (a k)
    have h3 := hv_mul hv (hv_prod Finset.univ hp)
    have e1 : (0 : K → ℤ) + ∑ k, a k • (Pi.single k 1 : K → ℤ) = a := by
      funext b
      simp [Finset.sum_apply, Pi.single_apply]
    have e2 : (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ a k = s := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      have : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) * y ⟨k, c k⟩ ^ a k = 1 := fun k => by
        rw [← zpow_add₀ (hyc k)]
        simp
      rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_const_one, mul_one]
    rw [e1, e2] at h3
    exact h3
  · have hm : Small.supMet a z = ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := by
      unfold Small.supMet
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (hc k))
        (norm_le_pi_norm (fun i => z ⟨k, i⟩) (c k))]
    rw [norm_mul, norm_prod, hm]
    simp only [norm_zpow]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun k _ => by positivity) hn

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mh_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem mh_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem mh_C (r : ℤ) : IsMultiHomog (MvPolynomial.C r : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
    by_contra hne
    exact hm (if_neg (Ne.symm hne))
  subst hm0
  simp

private theorem isMultiHomog_mul_of_mRing {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hf m1 h1 k, hg m2 h2 k]

theorem mh_prod {I : Type} (S : Finset I) {f : I → MRing ι} {d : I → K → ℕ}
    (h : ∀ i ∈ S, IsMultiHomog (f i) (d i)) : IsMultiHomog (∏ i ∈ S, f i) (∑ i ∈ S, d i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa using mh_C (ι := ι) 1
  · intro i S hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact isMultiHomog_mul_of_mRing (h i (Finset.mem_insert_self i S)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Forms

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hv_zero : Small.HasVal y (0 : K → ℤ) (0 : Ω) z (0 : 𝕜) := by
  refine ⟨0, 0, 0, 1, mh_zero 0, by simpa using mh_C (ι := ι) 1, fun k => by simp, by simp, by simp, by simp⟩

theorem hv_add {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y (0 : K → ℤ) s z w)
    (h' : Small.HasVal y (0 : K → ℤ) s' z w') : Small.HasVal y (0 : K → ℤ) (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, hp, hg, hh, e, ey, hz, ez⟩ := h
  obtain ⟨dg', dh', g', hp', hg', hh', e', ey', hz', ez'⟩ := h'
  have hd : dg = dh := funext fun k => by
    have := e k
    simp only [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hd' : dg' = dh' := funext fun k => by
    have := e' k
    simp only [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  subst hd hd'
  refine ⟨dg + dg', dg + dg', g * hp' + g' * hp, hp * hp', mh_add (isMultiHomog_mul_of_mRing hg hh') ?_,
    isMultiHomog_mul_of_mRing hh hh', fun k => by simp, ?_, ?_, ?_⟩
  · rw [add_comm dg dg']
    exact isMultiHomog_mul_of_mRing hg' hh
  · simp only [map_add (f := _), map_mul, ey, ey']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_add (f := _), map_mul, ez, ez']
    ring

theorem hv_neg {s : Ω} {w : 𝕜} (h : Small.HasVal y (0 : K → ℤ) s z w) :
    Small.HasVal y (0 : K → ℤ) (-s) z (-w) := by
  obtain ⟨dg, dh, g, hp, hg, hh, e, ey, hz, ez⟩ := h
  exact ⟨dg, dh, -g, hp, mh_neg hg, hh, e, by rw [map_neg, ey, neg_mul], hz, by rw [map_neg, ez, neg_mul]⟩

theorem hv_quot {d : K → ℕ} {g h : MRing ι} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d)
    {s : Ω} (e : MvPolynomial.aeval y g = s * MvPolynomial.aeval y h) (hz : MvPolynomial.aeval z h ≠ 0) :
    Small.HasVal y (0 : K → ℤ) s z (MvPolynomial.aeval z g / MvPolynomial.aeval z h) := by
  exact ⟨d, d, g, h, hg, hh, fun k => by simp, e, hz, (div_mul_cancel₀ _ hz).symm⟩

theorem hv_natInv [CharZero Ω] [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) :
    Small.HasVal y (0 : K → ℤ) ((n : Ω))⁻¹ z ((n : 𝕜))⁻¹ := by
  refine ⟨0, 0, 1, MvPolynomial.C (n : ℤ), by simpa using mh_C (ι := ι) 1, mh_C (n : ℤ), fun k => by simp,
    ?_, ?_, ?_⟩
  · simp [hn]
  · simpa using hn
  · simp [hn]

def valRing (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → 𝕜) : Subring Ω where
  carrier := {s | ∃ w, Small.HasVal y (0 : K → ℤ) s z w}
  mul_mem' := by
    rintro a b ⟨w, hw⟩ ⟨w', hw'⟩
    have := hv_mul hw hw'
    rw [add_zero] at this
    exact ⟨_, this⟩
  one_mem' := ⟨1, hv_one⟩
  add_mem' := by
    rintro a b ⟨w, hw⟩ ⟨w', hw'⟩
    exact ⟨_, hv_add hw hw'⟩
  zero_mem' := ⟨0, hv_zero⟩
  neg_mem' := by
    rintro a ⟨w, hw⟩
    exact ⟨_, hv_neg hw⟩

def valMap (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) : valRing y z →+* 𝕜 where
  toFun x := x.2.choose
  map_one' := GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (valRing y z).one_mem.choose_spec hv_one
  map_mul' a b := by
    have := hv_mul a.2.choose_spec b.2.choose_spec
    rw [add_zero] at this
    exact GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (a * b).2.choose_spec this
  map_zero' := GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (valRing y z).zero_mem.choose_spec hv_zero
  map_add' a b :=
    GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (a + b).2.choose_spec
      (hv_add a.2.choose_spec b.2.choose_spec)

theorem hasVal_valMap (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (x : valRing y z) :
    Small.HasVal y (0 : K → ℤ) (x : Ω) z (valMap hz x) := by
  exact x.2.choose_spec

end Values

theorem exists_subring_val : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω), Birational y → ∀ B : Finset Ω, ∃ u : MRing ι, Small.IsFormOff (mCoordIdeal y) u ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → MvPolynomial.aeval z u ≠ 0 → ∃ (A : Subring Ω) (ev : A →+* 𝕜), (↑B : Set Ω) ⊆ A ∧ (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) ∧ ∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x) := by
  intro K _ ι _ Ω _ _ y hbir B
  have hb' : ∀ s : Ω, ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
      MvPolynomial.aeval y h ≠ 0 ∧ MvPolynomial.aeval y g = s * MvPolynomial.aeval y h := hbir
  choose d g hq hg hh hyne e using hb'
  have key : ∀ f : MRing ι, MvPolynomial.eval (fun _ => (1 : Ω)) (mConeMap y f) = MvPolynomial.aeval y f := by
    intro f
    induction f using MvPolynomial.induction_on
    · simp [mConeMap]
    · rename_i hp hq
      simp only [map_add (f := _), hp, hq]
    · rename_i hp
      simp only [map_mul, hp]
      simp [mConeMap]
  refine ⟨∏ b ∈ B, hq b, ⟨⟨∑ b ∈ B, d b, mh_prod B fun b _ => hh b⟩, ?_⟩, ?_⟩
  · intro hu
    have h0 : MvPolynomial.aeval y (∏ b ∈ B, hq b) = 0 := by
      rw [← key, show mConeMap y (∏ b ∈ B, hq b) = 0 from hu, map_zero]
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨b, _, hb⟩ := h0
    exact hyne b hb
  · intro 𝕜 _ _ z hz hzu
    rw [map_prod] at hzu
    refine ⟨valRing y z, valMap hz, ?_, ?_, fun x => hasVal_valMap hz x⟩
    · intro b hb
      exact ⟨_, hv_quot (hg b) (hh b) (e b) (Finset.prod_ne_zero_iff.mp hzu b hb)⟩
    · intro n hn
      exact ⟨_, hv_natInv hn⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_quotient_gauge_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → AdRel Q.tB (𝟙 (Sp k)) d' gB.x gB.B.A.act gB.B.ad gB.e a wB → ∀ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u → (ax0 t x).appTop.hom u.val = 1 ∧ (ax1 t x).appTop.hom u.val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis.unit_one_on_axes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis.unit_one_on_axes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis.unit_one_on_axes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.projective_over_restrict_int : ∀ (o : Type) [CommRing o] [Module.Finite ℤ o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → IsProjOver (s ≫ spMap (Int.castRingHom o)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int | exact GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU


theorem _root_.GlobalTheory.T.cubical_triple_trivial : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ), (∀ (T : Over (Sp K)) (x y : T ⟶ G), (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧ (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧ (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1) → ∀ x y w : 𝟙_ (Over (Sp K)) ⟶ G, (lift x (lift y w)).left.appTop.hom v.val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points | exact GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points | (intros; apply GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points <;> assumption)
end
