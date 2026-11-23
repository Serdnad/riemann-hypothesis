module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle099
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle104
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem _root_.GlobalTheory.T.regular_function_in_block_field : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] [CharZero Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (s : M.Ω), zb ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal zb) s → algebraMap M.Ω Φ s ∈ blockFnField y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField.algebraMap_mem_blockFnField <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_chart_regular_with_boundary_choice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (x : SncRes.Pts P) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (σ : Fin e → Option (Fin (SncRes.rc P D))), IsMultiHomogIdeal P → IsMultiHomogIdeal D → x ∈ SncRes.src P p → (∀ h ∈ (SncRes.ideal P p), eval (SncRes.coord P p x) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (SncRes.coord P p x)) → ringKrullDim (locRing (SncRes.ideal P p) (SncRes.coord P p x)) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x)) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x))) (ptIdeal (SncRes.coord P p x)) → (∀ l, σ l = none ↔ l ∉ Jf) → (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)) → (∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0) → ∃ l ∈ Jf, σ l = some k) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∀ k, SncRes.comp P D k ∩ O = {x' ∈ O | ∃ l, σ l = some k ∧ eval (SncRes.coord P p x') (r l) = 0} := by
  intro K _ ι _ P D e p x r Jf σ hP hD hx _ _ _ _ _ hch hout
  classical
  have zero_iff {Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hQ : IsMultiHomogIdeal Q)
      (y : SncRes.Pts P) (hy : y ∈ SncRes.src P p) :
      (∀ f ∈ Q, eval (SncRes.rep y) f = 0) ↔
        ∀ h ∈ SncRes.ideal Q p, eval (SncRes.coord P p y) h = 0 := by
    have hchart := mem_conePts_iff_chartIdeal hQ p (SncRes.rep y) hy
    constructor
    · intro h
      exact renPt_zero _ _ (hchart.1 ⟨(SncRes.rep_mem y).1, h⟩)
    · intro h
      have hyQ : SncRes.rep y ∈ conePts Q := hchart.2 fun f hf => by
        rw [← eval_renC]
        exact h _ (Ideal.mem_map_of_mem _ hf)
      exact hyQ.2
  have norm_ne (y : SncRes.Pts P) (k : K) :
      ((∑ i, ‖SncRes.rep y ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (SncRes.Top.normSq_pos ((SncRes.rep_mem y).1 k)).ne'
  have mem_src_iff (y : SncRes.Pts P) :
      y ∈ SncRes.src P p ↔ ∀ k, y.1 ⟨k, (p k, p k)⟩ ≠ 0 := by
    refine forall_congr' fun k => ?_
    rw [← SncRes.proj_rep y]
    simp only [SncRes.proj, ne_eq, div_eq_zero_iff, norm_ne, or_false, mul_eq_zero,
      map_eq_zero, or_self]
  have hopen : IsOpen (SncRes.src P p) := by
    have heq : SncRes.src P p = ⋂ k, {y : SncRes.Pts P | y.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
      ext y
      simp [mem_src_iff]
    rw [heq]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
  have hcoord : ContinuousOn (SncRes.coord P p) (SncRes.src P p) := by
    refine continuousOn_iff_continuous_domRestrict.2 (continuous_pi fun j => ?_)
    let q := (Fintype.equivFin (Σ k, ι k)).symm j
    have hratio (y : SncRes.src P p) :
        SncRes.coord P p y.1 j = y.1.1 ⟨q.1, (q.2, p q.1)⟩ / y.1.1 ⟨q.1, (p q.1, p q.1)⟩ := by
      have hstar : starRingEnd ℂ (SncRes.rep y.1 ⟨q.1, p q.1⟩) ≠ 0 := by
        simpa using y.2 q.1
      change affCoord p (SncRes.rep y.1) q = _
      rw [← SncRes.proj_rep y.1]
      simp only [SncRes.proj, affCoord]
      rw [div_div_div_cancel_right₀ (norm_ne y.1 q.1), mul_div_mul_right _ _ hstar]
    have hv (a : Σ k, ι k × ι k) : Continuous fun y : SncRes.src P p => y.1.1 a :=
      (continuous_apply a).comp (continuous_subtype_val.comp continuous_subtype_val)
    change Continuous (fun y : SncRes.src P p => SncRes.coord P p y.1 j)
    simp only [hratio]
    exact (hv ⟨q.1, (q.2, p q.1)⟩).div (hv ⟨q.1, (p q.1, p q.1)⟩)
      (fun y => (mem_src_iff y.1).1 y.2 q.1)
  have hQ (k) : IsMultiHomogIdeal (SncRes.compIdeal P D k) :=
    MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup K ι P D hP hD _ (SncRes.compIdeal_mem D k)
  choose s hst hsw using fun l =>
    SncRes.NearComp.exists_den_chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)
  have hg : ∀ k, ∃ g, eval (SncRes.coord P p x) g ≠ 0 ∧
      ((∃ l, σ l = some k) ∨ g ∈ SncRes.ideal (SncRes.compIdeal P D k) p) := by
    intro k
    by_cases hk : ∃ l, σ l = some k
    · exact ⟨1, by simp, Or.inl hk⟩
    · have hn : ¬ ∀ h ∈ SncRes.ideal (SncRes.compIdeal P D k) p,
          eval (SncRes.coord P p x) h = 0 := fun h => by
        obtain ⟨l, -, hl⟩ := hout k ((zero_iff (hQ k) x hx).2 h)
        exact hk ⟨l, hl⟩
      push Not at hn
      obtain ⟨g, hg, hgt⟩ := hn
      exact ⟨g, hgt, Or.inr hg⟩
  choose g hgt hgk using hg
  let F := (∏ l, s l) * ∏ k, g k
  have hFw : ∀ w, eval w F ≠ 0 ↔ (∀ l, eval w (s l) ≠ 0) ∧ ∀ k, eval w (g k) ≠ 0 := by
    intro w
    simp only [F, map_mul, map_prod, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, not_exists]
  refine ⟨SncRes.src P p ∩ SncRes.coord P p ⁻¹' {w | eval w F ≠ 0}, ?_,
    ⟨hx, (hFw _).2 ⟨hst, hgt⟩⟩, Set.inter_subset_left, fun k => ?_⟩
  · exact hcoord.isOpen_inter_preimage hopen
      (isOpen_ne_fun (MvPolynomial.continuous_eval F) continuous_const)
  · ext y
    constructor
    · rintro ⟨hc, ho⟩
      refine ⟨ho, ?_⟩
      have hz := (zero_iff (hQ k) y ho.1).1 hc
      rcases hgk k with ⟨l, hl⟩ | hk
      · refine ⟨l, hl, hz _ ?_⟩
        rw [hch l k hl]
        exact Ideal.mem_comap.2 (Ideal.subset_span rfl)
      · exact absurd (hz _ hk) (((hFw _).1 ho.2).2 k)
    · rintro ⟨ho, l, hl, hr⟩
      refine ⟨(zero_iff (hQ k) y ho.1).2 ?_, ho⟩
      rw [hch l k hl]
      exact hsw l _ ((zero_iff hP y ho.1).1 (SncRes.rep_mem y).2)
        (((hFw _).1 ho.2).1 l) hr
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_resolution_transition_polynomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → (∀ p : (k : K) → ι k, SncRes.coord P p '' SncRes.src P p = {t | ∀ h ∈ SncRes.ideal P p, eval t h = 0}) ∧ ∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), eval (SncRes.coord P p x) q ≠ 0 ∧ ∀ y ∈ SncRes.src P p ∩ SncRes.src P p', eval (SncRes.coord P p y) q ≠ 0 → ∀ l, SncRes.coord P p' y l * eval (SncRes.coord P p y) q = eval (SncRes.coord P p y) (F l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (cycBlockWt cyc_exists_blockComponent cyc_isHomogeneous_of_isMultiHomogIdeal)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

theorem mdeg_add (m n : (Σ k, ι k) →₀ ℕ) : mdeg (m + n) = mdeg m + mdeg n := by
  funext k
  simp [mdeg, Finset.sum_add_distrib]


open Classical in
def part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) : MvPolynomial (Σ k, ι k) ℂ :=
  ∑ m ∈ s.support.filter (fun m => mdeg m = b), monomial m (AddMonoidAlgebra.coeff s m)

open Classical in
theorem coeff_part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) (m : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (part b s) m = if mdeg m = b then AddMonoidAlgebra.coeff s m else 0 := by
  unfold part
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : mdeg m = b
  · by_cases hs : m ∈ s.support
    · simp [h, hs]
    · have : AddMonoidAlgebra.coeff s m = 0 := by simpa using hs
      simp [this]
  · simp [h]

open Classical in
theorem sum_part (s : MvPolynomial (Σ k, ι k) ℂ) :
    ∑ b ∈ s.support.image mdeg, part b s = s := by
  unfold part
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact s.support_sum_monomial_coeff

theorem isMultiHomog_part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) :
    IsMultiHomog (part b s) b := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_part] at hm
  by_contra hk
  refine hm (if_neg fun h => hk ?_)
  exact congrFun h k

theorem isMultiHomog_mul {s f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hs : IsMultiHomog s b) (hf : IsMultiHomog f a) : IsMultiHomog (s * f) (b + a) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul s f hm)
  have := congrFun (mdeg_add m₁ m₂) k
  simp only [mdeg, Pi.add_apply] at this
  rw [this, hs m₁ h₁ k, hf m₂ h₂ k]
  rfl

theorem coeff_mul_eq_zero {r f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hr : ∀ m ∈ r.support, mdeg m ≠ b) (hf : IsMultiHomog f a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : mdeg m = b + a) : AddMonoidAlgebra.coeff (r * f) m = 0 := by
  classical
  by_contra h
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul r f (mem_support_iff.2 h))
  refine hr m₁ h₁ (funext fun k => ?_)
  have e := congrFun hm k
  have e' := congrFun (mdeg_add m₁ m₂) k
  have e'' : mdeg m₂ k = a k := hf m₂ h₂ k
  simp only [Pi.add_apply] at e e'
  omega

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem part_mul_mem [DecidableEq K] {I : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hI : ∀ k, I.IsHomogeneous (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)))
    {s f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (h : s * f ∈ I)
    (b : K → ℕ) : part b s * f ∈ I := by
  classical
  obtain ⟨g, hgI, hg⟩ := cyc_exists_blockComponent hI (b + a) Finset.univ h
  have hgeq : g = part b s * f := by
    ext m
    rw [hg m]
    by_cases hm : mdeg m = b + a
    · have e : ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k :=
        fun k _ => congrFun hm k
      rw [if_pos e]
      have hr : ∀ m' ∈ (s - part b s).support, mdeg m' ≠ b := by
        intro m' hm' hb
        rw [mem_support_iff, MvPolynomial.coeff_sub, coeff_part, if_pos hb, sub_self] at hm'
        exact hm' rfl
      have e2 : s * f = part b s * f + (s - part b s) * f := by ring
      rw [e2, MvPolynomial.coeff_add, coeff_mul_eq_zero hr hf hm, add_zero]
    · have e : ¬ ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k :=
        fun h' => hm (funext fun k => h' k (Finset.mem_univ k))
      rw [if_neg e]
      by_contra hne
      exact hm (funext fun k => isMultiHomog_mul (isMultiHomog_part b s) hf m
        (mem_support_iff.2 (Ne.symm hne)) k)
  exact hgeq ▸ hgI

theorem isHomogeneous_pow {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (n : ℕ) :
    (I ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact (⊤ : HomogeneousIdeal 𝒜).isHomogeneous
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hI

theorem ren_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {p : (k : K) → ι k}
    {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ ReciprocityTheory.AnForm.R.chartIdeal S p) :
    renR (Σ k, ι k) g ∈ ideal S p := by
  unfold ideal
  rw [mem_map_renR_iff, RingEquiv.symm_apply_apply]
  exact hg

theorem lift_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (q : Σ k, ι k) :
    lift p q - renR (Σ k, ι k) (X q) ∈ ideal S p := by
  classical
  obtain ⟨k, i⟩ := q
  unfold lift
  split_ifs with h
  · simp only at h
    subst h
    have hm : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ ReciprocityTheory.AnForm.R.chartIdeal S p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    have h2 : renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ ideal S p := ren_mem hm
    have h3 := (ideal S p).neg_mem h2
    rw [map_sub, map_one, neg_sub] at h3
    exact h3
  · have : renR (Σ k, ι k) (X (⟨k, i⟩ : Σ k, ι k)) = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
      simp [renameEquiv_apply]
    rw [this, sub_self]
    exact zero_mem _

theorem deh_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (g : MvPolynomial (Σ k, ι k) ℂ) :
    bind₁ (lift p) g - renR (Σ k, ι k) g ∈ ideal S p := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    have e : renR (Σ k, ι k) (C c) = C c := by simp [renameEquiv_apply]
    rw [e, bind₁_C_right, sub_self]
    exact zero_mem _
  | add g h hg hh =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact add_mem hg hh
  | mul_X g q hg =>
    rw [map_mul, map_mul, bind₁_X_right]
    have e : bind₁ (lift p) g * lift p q - renR (Σ k, ι k) g * renR (Σ k, ι k) (X q) =
        (bind₁ (lift p) g - renR (Σ k, ι k) g) * lift p q +
          renR (Σ k, ι k) g * (lift p q - renR (Σ k, ι k) (X q)) := by ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (lift_sub_mem S p q))

theorem map_deh_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal.map (bind₁ (lift p) : _ →ₐ[ℂ] _) S ≤ ideal S p := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  have hm : renR (Σ k, ι k) g ∈ ideal S p := ren_mem (Ideal.mem_sup_left hg)
  rw [Ideal.mem_comap]
  have := add_mem (deh_sub_mem S p g) hm
  rwa [sub_add_cancel] at this

theorem relation_dehom : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (f s : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ), IsMultiHomogIdeal P →
    IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) →
    IsMultiHomog f a → s ∉ Q → s * f ∈ Q ^ n ⊔ P →
    ∃ s' ∉ SncRes.ideal Q p, s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p := by
  intro K _ ι _ P Q p f s a n hP hQ hQp hX hf hs hrel
  classical
  have hI : ∀ k, (Q ^ n ⊔ P).IsHomogeneous
      (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)) := fun k =>
    (isHomogeneous_pow _ (cyc_isHomogeneous_of_isMultiHomogIdeal hQ k) n).sup
      (cyc_isHomogeneous_of_isMultiHomogIdeal hP k)
  obtain ⟨b, hb⟩ : ∃ b, part b s ∉ Q := by
    by_contra hall
    push_neg at hall
    exact hs (sum_part s ▸ Ideal.sum_mem _ fun b _ => hall b)
  have hmem := part_mul_mem hI hf hrel b
  refine ⟨bind₁ (lift p) (part b s), ?_, ?_⟩
  · rw [((GlobalTheory.T.affine_chart_ideal_prime_and_saturated K ι Q p hQ hQp hX).2 _ b (isMultiHomog_part b s))]
    exact hb
  · have h1 := Ideal.mem_map_of_mem (bind₁ (lift p) : _ →ₐ[ℂ] _) hmem
    rw [map_mul, Ideal.map_sup, Ideal.map_pow] at h1
    exact (sup_le_sup (Ideal.pow_right_mono (map_deh_le Q p) n) (map_deh_le P p)) h1

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_cover_frames_value_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → (∀ τ, IsBlockDiag j (h τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', z ⟨k', m'⟩ = a * CovMap.LocImg.plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.img Cv F' F z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M'.blk z ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F' F (basePart M'.blk z) p.1 * h p.1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem minor_ne_zero_of_support {N : ℕ} {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) {I : Finset (Fin N)}
    (hs : ∀ k c, c ∈ I → k ∉ I → h k c = 0) : minorIJ h I I ≠ 0 := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (isUnit_iff_ne_zero.2 hd)
  have hH : (hᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * h).PosDef := by
    rw [Matrix.mul_one]
    exact Matrix.PosDef.conjTranspose_mul_self h (Matrix.mulVec_injective_of_isUnit hu)
  have hq := SchurCalc.minor_pos hH I
  rw [SchurCalc.minor_gram (G := 1) (fun k c hc hk => Matrix.one_apply_ne (fun e => hk (e ▸ hc))) hs] at hq
  intro e
  simp [e] at hq

theorem facOf_ne_zero (N j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h)
    (hd : h.det ≠ 0) : facOf N j a h i ≠ 0 := by
  unfold facOf
  split_ifs
  · exact minor_ne_zero_of_support hd (MinorCalc.support_wIdx hh)
  · exact one_ne_zero
  · exact minor_ne_zero_of_support hd (MinorCalc.support_omIdx hh)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem xiCoef_self {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a i : Fin N) :
    xiCoef τ a (τ, i) = xiCoef () a ((), i) := by
  simp [xiCoef]

theorem xiCoef_ne {Ψ : Type} [DecidableEq Ψ] {N : ℕ} {τ τ' : Ψ} (h : τ' ≠ τ) (a i : Fin N) :
    xiCoef τ a (τ', i) = 0 := by
  simp [xiCoef, h]

theorem xi_sum_potentials : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (a b ca cb : Fin N) (Gf hf : Ψ → Matrix (Fin N) (Fin N) ℂ) (u : Ψ × Fin N → ℝ) (t : ℂ) (G₂ : Matrix (Fin 2) (Fin 2) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (Gf τ) → (Gf τ).PosDef → IsBlockDiag j (hf τ) → (hf τ).det ≠ 0 → (∀ r s : Fin 2, G₂ r s = minorIJ ((hf τ)ᴴ * Gf τ * hf τ) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) / minorIJ ((hf τ)ᴴ * Gf τ * hf τ) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) → ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) = xiPot G₂ t - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (hf τ) i‖) + u (τ, i)) := by
  intro Ψ _ _ N j τ a b ca cb Gf hf u t G₂ hj hb hcase hca hcb hG hGp hh hdet hG₂
  obtain ⟨G₃, -, e3, key⟩ := norm_three_steps N j a b ca cb (Gf τ) (hf τ) hj hb hcase hca hcb hG hGp hh hdet
  have hGG : G₃ = G₂ := Matrix.ext fun r s => (e3 r s).trans (hG₂ r s).symm
  subst hGG
  have hsum : ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (blockPot j i (Gf τ) (hf τ * (1 + Matrix.single cb ca t)) - u (τ, i)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · simp
    · intro τ' _ hne
      simp [xiCoef_ne hne]
    · simp
  rw [hsum, ← key t, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xiCoef_self]
  simp only [facOf]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem gramPlane_posDef : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ w ∈ Un, (Gn w).PosDef := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp _ hF w hw
  unfold IsFibreData at hF
  obtain ⟨-, -, -, h4, h5, -, -⟩ := hF
  obtain ⟨hbp, hH⟩ := h4 w hw
  obtain ⟨hGbd, hGpd⟩ := BM.G_pos l τ (bp w) hbp
  obtain ⟨G₂, hG₂, hG₂eq, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.norm_three_steps N j a b ca cb (BM.G l τ (bp w)) (H τ w)
    M.j_le hb hab hca hcb hGbd hGpd (hH τ).1 (hH τ).2
  have hEq : Gn w = G₂ := Matrix.ext fun r s => by rw [h5 w hw r s, hG₂eq r s]
  rw [hEq]
  exact hG₂

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.flag_height_polynomial_weight_form : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) → hFlPoly Ψ N II = toWt (formPoly (antisymDegree Ψ N + 1) fun w => II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r)) ∧ degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w => ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flLines_polys | exact GlobalTheory.CompanionTheory.Ar.PB.flLines_polys | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flLines_polys <;> assumption)
end
