module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

def fundCo {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : ℝ :=
  f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0

theorem fundCo_sub {N : ℕ} (f g : Fin N → ℝ) (i : Fin N) : fundCo (f - g) i = fundCo f i - fundCo g i := by
  unfold fundCo
  split_ifs <;> simp <;> ring

theorem fundCo_smul {N : ℕ} (c : ℝ) (f : Fin N → ℝ) (i : Fin N) : fundCo (c • f) i = c * fundCo f i := by
  unfold fundCo
  split_ifs <;> simp <;> ring

private theorem abel_range (F B : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range M, (F i - F (i + 1)) * ∑ k ∈ Finset.range (i + 1), B k + F M * ∑ k ∈ Finset.range M, B k =
      ∑ k ∈ Finset.range M, F k * B k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => F k * B k), ← ih, Finset.sum_range_succ B M]
    ring

theorem sum_fundCo_mul_sum_Iic {N : ℕ} (f B : Fin N → ℝ) :
    ∑ i, fundCo f i * ∑ k ∈ Finset.Iic i, B k = ∑ k, f k * B k := by
  classical
  let F : ℕ → ℝ := fun j => if h : j < N then f ⟨j, h⟩ else 0
  let B' : ℕ → ℝ := fun j => if h : j < N then B ⟨j, h⟩ else 0
  have hF : ∀ i : Fin N, F i = f i := fun i => by simp [F, i.2]
  have hB : ∀ i : Fin N, B' i = B i := fun i => by simp [B', i.2]
  have hFN : F N = 0 := by simp [F]
  have hco : ∀ i : Fin N, fundCo f i = F i - F (i + 1) := fun i => by
    simp only [fundCo, hF]
    congr 1
  have hI : ∀ i : Fin N, ∑ k ∈ Finset.Iic i, B k = ∑ k ∈ Finset.range ((i : ℕ) + 1), B' k := by
    intro i
    symm
    refine Finset.sum_bij' (fun j hj => (⟨j, by have := Finset.mem_range.1 hj; have := i.2; omega⟩ : Fin N))
      (fun k _ => (k : ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Iic, Fin.le_def]
      have := Finset.mem_range.1 hj
      omega
    · intro k hk
      have : (k : ℕ) ≤ i := Fin.le_def.1 (Finset.mem_Iic.1 hk)
      exact Finset.mem_range.2 (by omega)
    · intro j hj; rfl
    · intro k hk; rfl
    · intro j hj
      have h1 : j < N := by have := Finset.mem_range.1 hj; have := i.2; omega
      simp [B', h1]
  have h := abel_range F B' N
  rw [hFN, zero_mul, add_zero] at h
  simp only [hco, hI]
  rw [Fin.sum_univ_eq_sum_range (fun i => (F i - F (i + 1)) * ∑ k ∈ Finset.range (i + 1), B' k) N, h,
    ← Fin.sum_univ_eq_sum_range (fun k => F k * B' k) N]
  exact Finset.sum_congr rfl fun k _ => by rw [hF, hB]

theorem aeval_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [CommRing S]
    {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) (t : K → S) (x : (Σ k, ι k) → S) :
    aeval (fun p => t p.1 * x p) g = (∏ k, t k ^ a k) * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (t p.1 * x p) ^ m p = (∏ k, t k ^ a k) * ∏ p, x p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem isMultiHomog_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι}
    {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k]

theorem aeval_eq_zero_of_mem {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have hc : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMap y).toRingHom = (aeval y).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap])
  have h0 : mConeMap y f = 0 := hf
  have := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0, map_zero] at this
  exact this.symm

theorem hasVal_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (h : HasVal y a s z v) : HasVal y a s (fun p => c p.1 * z p) (v * ∏ k, c k ^ a k) := by
  obtain ⟨dg, dh, g, k', hg, hk, hd, hy, h0, hv⟩ := h
  refine ⟨dg, dh, g, k', hg, hk, hd, hy, ?_, ?_⟩
  · rw [aeval_scale hk]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)) h0
  · rw [aeval_scale hg, aeval_scale hk, hv]
    have e : ∀ k, c k ^ dg k = c k ^ a k * c k ^ dh k := fun k => by
      rw [← zpow_natCast, hd k, zpow_add₀ (hc k), zpow_natCast, mul_comm]
    simp only [e, Finset.prod_mul_distrib]
    ring

theorem isSmoothHerm_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} [Fintype σ]
    {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a)) (n : σ → ℤ) : IsSmoothHerm (combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

private theorem hessC_congr_of_eventuallyEq' {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : f =ᶠ[𝓝 z] g) : ReciprocityTheory.AnForm.hessC f z = ReciprocityTheory.AnForm.hessC g z := by
  have h2 : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ g) z := (h.fderiv (𝕜 := ℝ)).fderiv_eq
  unfold ReciprocityTheory.AnForm.hessC
  rw [h2]

private theorem maDens_congr_of_hessC_eq {D : ℕ} {f g : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, f k =ᶠ[𝓝 z] g k) : ReciprocityTheory.AnForm.maDens f z = ReciprocityTheory.AnForm.maDens g z := by
  unfold ReciprocityTheory.AnForm.maDens
  rw [show (fun k => ReciprocityTheory.AnForm.hessC (f k) z) = (fun k => ReciprocityTheory.AnForm.hessC (g k) z) from
    funext fun k => hessC_congr_of_eventuallyEq' (h k)]

theorem paramDens_eq_normSq_mul_locDens {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) {V : Set (Fin e → ℂ)} {Φ : (Fin e → ℂ) → X} (P : Fin e → LocPot X)
    (j : Fin A.n) (hΦ : IsParam A V Φ) {z : Fin e → ℂ} (hzV : z ∈ V)
    (hz : Φ z ∈ (A.chart j).source) (hc : ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) :
    paramDens P Φ z = Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart j ∘ Φ) z).det *
      locDens A P j ((A.chart j ∘ Φ) z) := by
  have hcont : ContinuousAt Φ z := hΦ.2.1.continuousAt (hΦ.1.mem_nhds hzV)
  have hev : ∀ᶠ z' in 𝓝 z, Φ z' ∈ (A.chart j).source :=
    hcont.preimage_mem_nhds ((A.chart j).open_source.mem_nhds hz)
  have han : AnalyticAt ℂ (A.chart j ∘ Φ) z := hΦ.2.2.2 j z ⟨hzV, hz⟩
  have hinv : (A.chart j).symm ((A.chart j ∘ Φ) z) = Φ z := (A.chart j).left_inv hz
  have key := ReciprocityTheory.AnForm.A.maDens_comp (fun k => (P k).φ (Φ z) ∘ (A.chart j).symm)
    (A.chart j ∘ Φ) z han (fun k => hc k j hz)
  have h1 : paramDens P Φ z = ReciprocityTheory.AnForm.maDens
      (fun k => ((P k).φ (Φ z) ∘ (A.chart j).symm) ∘ (A.chart j ∘ Φ)) z := by
    unfold paramDens
    apply maDens_congr_of_hessC_eq
    intro k
    filter_upwards [hev] with z' hz'
    simp only [Function.comp_apply, (A.chart j).left_inv hz']
  have h2 : locDens A P j ((A.chart j ∘ Φ) z) = ReciprocityTheory.AnForm.maDens
      (fun k => (P k).φ (Φ z) ∘ (A.chart j).symm) ((A.chart j ∘ Φ) z) := by
    unfold ReciprocityTheory.AnForm.M.locDens
    rw [hinv]
    rfl
  rw [h1, key, h2, mul_comm]

theorem param_chart_changeOfVariables : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (j : Fin A.n), IsParam A V Φ → MeasurableSet B → B ⊆ V → (∀ z ∈ B, Φ z ∈ (A.chart j).source) → (∀ z ∈ B, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) → MeasurableSet ((A.chart j ∘ Φ) '' B) ∧ (IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A P j y) ((A.chart j ∘ Φ) '' B) ↔ IntegrableOn (fun z => g (Φ z) * paramDens P Φ z) B) ∧ ∫ y in (A.chart j ∘ Φ) '' B, g ((A.chart j).symm y) * locDens A P j y = ∫ z in B, g (Φ z) * paramDens P Φ z := by
  intro e X _ _ _ A V B Φ P g j hΦ hB hBV hsrc hc2
  have han : ∀ z ∈ B, AnalyticAt ℂ (A.chart j ∘ Φ) z := fun z hz => hΦ.2.2.2 j z ⟨hBV hz, hsrc z hz⟩
  have hτd : ∀ z ∈ B, HasFDerivWithinAt (A.chart j ∘ Φ)
      ((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ) B z := fun z hz =>
    ((han z hz).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn (A.chart j ∘ Φ) B := by
    intro x hx y hy hxy
    apply hΦ.2.2.1 (hBV hx) (hBV hy)
    have h := congrArg (A.chart j).symm hxy
    simpa only [Function.comp_apply, (A.chart j).left_inv (hsrc x hx),
      (A.chart j).left_inv (hsrc y hy)] using h
  have hdet : ∀ z ∈ B, |((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ).det| =
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart j ∘ Φ) z).det := by
    intro z hz
    rw [← ((han z hz).differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv,
      ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq _ _ (han z hz).differentiableAt]
    exact abs_of_nonneg (Complex.normSq_nonneg _)
  have hpt : Set.EqOn (fun z => |((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ).det| •
      (g ((A.chart j).symm ((A.chart j ∘ Φ) z)) * locDens A P j ((A.chart j ∘ Φ) z)))
      (fun z => g (Φ z) * paramDens P Φ z) B := by
    intro z hz
    simp only
    rw [hdet z hz, smul_eq_mul,
      paramDens_eq_normSq_mul_locDens A P j hΦ (hBV hz) (hsrc z hz) (hc2 z hz)]
    have hl : (A.chart j).symm ((A.chart j ∘ Φ) z) = Φ z := (A.chart j).left_inv (hsrc z hz)
    rw [hl]
    ring
  refine ⟨measurable_image_of_fderivWithin hB hτd hinj, ?_, ?_⟩
  · rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hB hτd hinj]
    exact integrableOn_congr_fun hpt hB
  · rw [integral_image_eq_integral_abs_det_fderiv_smul volume hB hτd hinj]
    exact setIntegral_congr_fun hB hpt

end GlobalTheory.CompanionTheory.Ar.PB
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

open GlobalTheory.CompanionTheory.Ar.FlagBun

def IsGenFam (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) : Prop :=
  (∀ s a, u s a a = 1) ∧ (∀ s a b, a < b → u s a b = 0) ∧
    AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) = ⊤

def revInv {G : Type} [Field G] {r : ℕ} (u : Matrix (Fin r) (Fin r) G) : Matrix (Fin r) (Fin r) G :=
  (u.transpose⁻¹).submatrix Fin.rev Fin.rev

theorem genU_isGenFam (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : IsGenFam Ω (GenField Ω r) (genU Ω r) := by
  have hdiag : ∀ s (a : Fin (r s)), genU Ω r s a a = 1 := fun s a => by
    simp [genU]
  have habove : ∀ s (a b : Fin (r s)), a < b → genU Ω r s a b = 0 := fun s a b h => by
    simp [genU, not_lt.2 h.le, h.ne]
  have hbelow : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
      genU Ω r q.1 q.2.1.1 q.2.1.2 =
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) :=
    fun q => by
      simp only [genU]
      exact dif_pos q.2.2
  refine ⟨hdiag, habove, ?_, ?_⟩
  · have hinj : Function.Injective
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) := by
      rw [IsScalarTower.coe_toAlgHom']
      exact IsFractionRing.injective _ _
    have hX := (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map' hinj
    have hfun : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        (IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r)) ∘ MvPolynomial.X := by
      funext q
      exact hbelow q
    rw [hfun]
    exact hX
  · rw [eq_top_iff]
    intro x _
    have hXmem : ∀ q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1},
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X (R := Ω) (σ := GenIx r) q) ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro q
      rw [← hbelow q]
      exact IntermediateField.subset_adjoin _ _ ⟨⟨q.1, q.2.1⟩, rfl⟩
    have hA : ∀ a : MvPolynomial (GenIx r) Ω,
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) a ∈
          IntermediateField.adjoin Ω
            (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) := by
      intro a
      induction a using MvPolynomial.induction_on
      · rename_i c
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ c
      · rename_i p q hp hq
        rw [map_add (f := _)]
        exact add_mem hp hq
      · rename_i p i hp
        rw [map_mul]
        exact mul_mem hp (hXmem i)
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (GenIx r) Ω) x
    exact div_mem (hA a) (hA b)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.row_product_first_derivative : ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ n : Fin 3 → ℝ,
    evalW n n (pderiv (some 0) (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * k - 1 then 1 else 0, 0] (if (r : ℕ) < 2 * k - 1 then 0 else 1))) =
    C (2 * (k : ℝ) - 1) * rename some (lin3 n ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.evalW_pderiv_prod_rowW | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.evalW_pderiv_prod_rowW | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.evalW_pderiv_prod_rowW <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.AnForm.A

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def tailCL (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailCL_coe (d : ℕ) : (⇑(tailCL d) : (Fin (d + 1) → ℂ) → (Fin d → ℂ)) = Fin.tail := by
  funext z i
  rfl

theorem jacC_tailCL (d : ℕ) (z : Fin (d + 1) → ℂ) (a : Fin d) (k : Fin (d + 1)) :
    jacC (⇑(tailCL d)) z a k = if a.succ = k then 1 else 0 := by
  have h := ContinuousLinearMap.fderiv (𝕜 := ℂ) (x := z) (tailCL d)
  simp only [jacC, h]
  simp [tailCL, Pi.single_apply, eq_comm]

theorem hessC_comp_tail (d : ℕ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p : ℂ)
    (hα : ContDiffAt ℝ 2 α y) :
    hessC (fun z : Fin (d + 1) → ℂ => α (Fin.tail z)) (Fin.cons p y) = blk 0 (hessC α y) := by
  have ht : (tailCL d) (Fin.cons p y : Fin (d + 1) → ℂ) = y := by
    rw [tailCL_coe]; exact Fin.tail_cons _ _
  have h := hessC_comp α (⇑(tailCL d)) (Fin.cons p y : Fin (d + 1) → ℂ)
    ((tailCL d).analyticAt _) (by rw [ht]; exact hα)
  have hfun : α ∘ ⇑(tailCL d) = fun z : Fin (d + 1) → ℂ => α (Fin.tail z) := by
    rw [tailCL_coe]; rfl
  rw [hfun, ht] at h
  rw [h]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  all_goals
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, jacC_tailCL, blk,
      Fin.succ_ne_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem hessC_row_fibre : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p e : ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (s v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p y) → ContDiffAt ℝ 2 α y → hessC f (Fin.cons p y) = blk e B →
    hessC (fun z : Fin (d + 1) → ℂ => s * f z + v * α (Fin.tail z)) (Fin.cons p y) =
    blk ((s : ℂ) * e) ((s : ℂ) • B + (v : ℂ) • hessC α y) := by
  intro d f α y p e B s v hf hα hB
  have ht : (Fin.tail (Fin.cons p y : Fin (d + 1) → ℂ) : Fin d → ℂ) = y := Fin.tail_cons _ _
  have htail : ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => α (Fin.tail z))
      (Fin.cons p y : Fin (d + 1) → ℂ) := by
    have hα' : ContDiffAt ℝ 2 α ((tailCL d) (Fin.cons p y : Fin (d + 1) → ℂ)) := by
      rw [tailCL_coe, ht]; exact hα
    have hl : ContDiffAt ℝ 2 (⇑((tailCL d).restrictScalars ℝ))
        (Fin.cons p y : Fin (d + 1) → ℂ) := ((tailCL d).restrictScalars ℝ).contDiff.contDiffAt
    have := ContDiffAt.comp (g := α) (f := ⇑((tailCL d).restrictScalars ℝ))
      (Fin.cons p y : Fin (d + 1) → ℂ) hα' hl
    have hfun : α ∘ ⇑((tailCL d).restrictScalars ℝ) = fun z : Fin (d + 1) → ℂ => α (Fin.tail z) := by
      funext z
      simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [tailCL_coe]
    rwa [hfun] at this
  rw [ReciprocityTheory.AnForm.M.hessC_add' (fun z => s * f z) (fun z => v * α (Fin.tail z)) _
    (contDiffAt_const.mul hf) (contDiffAt_const.mul htail),
    ReciprocityTheory.AnForm.M.hessC_const_mul' s f, ReciprocityTheory.AnForm.M.hessC_const_mul' v (fun z => α (Fin.tail z)), hB, hessC_comp_tail d α y p hα]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blk]

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.mobius_change_of_variables_pair : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ × ℂ → ℝ, ∫ p : ℂ × ℂ, (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2)) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.1, GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.2) = ∫ q : ℂ × ℂ, f q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.twist_isMultiHomogIdeal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), IsMultiHomogIdeal W → IsMultiHomogIdeal (twist p W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.horizontal_divSupp_twist_eq_image : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (P : Ideal (MRing ι)) (s : MRing ι), (∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) → {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} = twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.ringKrullDim_twist_succ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → NoRoot p W → (twist p W).IsPrime := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | exact GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.twLine_smooth_conjInvariant_glue : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main | exact GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main <;> assumption)
end
