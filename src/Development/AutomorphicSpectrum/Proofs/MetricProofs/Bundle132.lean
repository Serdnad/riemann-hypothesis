module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle126
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle131
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle009
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqR
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFundamentalSet
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle014
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqLimit
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle120
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle121
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle124
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt

theorem exists_rows_det_ne_zero {Ω : Type} [Field Ω] {n m : ℕ} (M : Matrix (Fin n) (Fin m) Ω)
    (B : Matrix (Fin m) (Fin n) Ω) (h : B * M = 1) :
    ∃ J : Fin m → Fin n, (M.submatrix J id).det ≠ 0 := by
  have hspan : Submodule.span Ω (Set.range fun j => M j) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : w = (w ᵥ* B) ᵥ* M := by rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
    rw [hw, Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨f, hf, -, hl⟩ := Submodule.exists_fun_fin_finrank_span_eq Ω (Set.range fun j => M j)
  have e : Module.finrank Ω (Submodule.span Ω (Set.range fun j => M j)) = m := by
    rw [hspan, finrank_top, Module.finrank_fin_fun]
  choose J hJ using fun i : Fin m => hf (Fin.cast e.symm i)
  refine ⟨J, ?_⟩
  have hl' : LinearIndependent Ω (M.submatrix J id).row := by
    have : (M.submatrix J id).row = f ∘ Fin.cast e.symm := by
      funext i
      exact hJ i
    rw [this]
    exact hl.comp _ (Fin.cast_injective _)
  exact ((Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 hl')).ne_zero

theorem exists_rows_castLE_det_ne_zero {Ω : Type} [Field Ω] {n m a : ℕ} (M : Matrix (Fin n) (Fin m) Ω)
    (B : Matrix (Fin m) (Fin n) Ω) (h : B * M = 1) (ha : a + 1 ≤ m) (hm : a + 1 = m) :
    ∃ J : Fin (a + 1) → Fin n, (M.submatrix J (Fin.castLE ha)).det ≠ 0 := by
  subst hm
  obtain ⟨J, hJ⟩ := exists_rows_det_ne_zero M B h
  exact ⟨J, hJ⟩

theorem step_full {Ψ : Type} {p q : ℕ} (K₀ : Type) (t : StepIx Ψ p q)
    (h : ∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r ≠ some (.inr t)) :
    (t.2 : ℕ) + 1 = rk Ψ p q t.1 := by
  apply GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.full_of_noBlock <;> assumption

theorem xb_block_ne : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type)
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), (∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0) →
    (∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * A s = 1) →
    ∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0 := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ hx hB k
  obtain ⟨k, hk⟩ := k
  rcases k with k | t
  · exact hx k
  · obtain ⟨B, hB⟩ := hB t.1
    exact exists_rows_castLE_det_ne_zero (A t.1) B hB t.2.2 (step_full K₀ t hk)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd

theorem compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (h : IsCompatChart A ψ) (V : Set X) (hV : IsOpen V) :
    IsCompatChart A (ψ.restrOpen V hV) := by
  apply ReciprocityTheory.AnForm.M.pa_compat_restr <;> assumption

theorem holoOn_comp {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (B : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A B pr) (S : Set Z) (g : Z → ℂ) (hg : B.HoloOn S g) :
    A.HoloOn (pr ⁻¹' S) (fun y => g (pr y)) := by
  rintro j z ⟨hzt, hzS⟩
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart j).symm z))
  have h1 : AnalyticAt ℂ (B.chart k ∘ pr ∘ (A.chart j).symm) z := hp.2 j k z ⟨hzt, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (B.chart k).symm) ((B.chart k ∘ pr ∘ (A.chart j).symm) z) := by
    refine hg k _ ⟨(B.chart k).map_source hk, ?_⟩
    have : (B.chart k).symm ((B.chart k) (pr ((A.chart j).symm z))) = pr ((A.chart j).symm z) :=
      (B.chart k).left_inv hk
    simpa [this] using hzS
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (pr ∘ (A.chart j).symm) z :=
    hp.1.continuousAt.comp ((A.chart j).continuousAt_symm hzt)
  filter_upwards [hc.preimage_mem_nhds ((B.chart k).open_source.mem_nhds hk)] with w hw
  have : (B.chart k).symm ((B.chart k) (pr ((A.chart j).symm w))) = pr ((A.chart j).symm w) :=
    (B.chart k).left_inv hw
  simp [this]

theorem snoc_inj {r n e : ℕ} (σb : Fin r → Option (Fin n)) (s : Fin n ↪ Fin e) (i₀ : Fin e)
    (hne : ∀ i, s i ≠ i₀) (hσ : ∀ k k' i, σb k = some i → σb k' = some i → k = k') (k k' : Fin (r + 1)) (i : Fin e)
    (h : (Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map s) (some i₀) : Fin (r + 1) → Option (Fin e)) k = some i)
    (h' : (Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map s) (some i₀) : Fin (r + 1) → Option (Fin e)) k' = some i) :
    k = k' := by
  induction k using Fin.lastCases with
  | last =>
    induction k' using Fin.lastCases with
    | last => rfl
    | cast l =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Option.some.injEq] at h h'
      obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 h'
      exact absurd (hb.trans h.symm) (hne b)
  | cast l =>
    induction k' using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Option.some.injEq] at h h'
      obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 h
      exact absurd (hb.trans h'.symm) (hne b)
    | cast l' =>
      simp only [Fin.snoc_castSucc] at h h'
      obtain ⟨b, hb, hbi⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨b', hb', hbi'⟩ := Option.map_eq_some_iff.1 h'
      have : b = b' := s.injective (hbi.trans hbi'.symm)
      subst this
      rw [hσ l l' b hb hb']

theorem mul_rearrange (A B a b c : ℂ) (h : A = B) : a * A * (b * c) = a * b * (B * c) := by
  subst h
  ring

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → BM.Rb.X) (hc : Continuous pr) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin BM.Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M BM.Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), HoloMap RW.A BM.Rb.A pr → ∀ c : ℝ, IsSNC RW.A (BM.L.pullback pr hc + secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (fun x y => BM.s (pr x) (pr y) * diagSec ψ i₀ u x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) (diagSet k₀ RW)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e BM τ a k₀ ca cb RW pr hc ψ kb σ i₀ V u hL hp c x
  obtain ⟨⟨F, H, hW⟩, hVo, hxV, hVs, hVU, huh, hu0, hdiag, -⟩ := hL x
  obtain ⟨hcomp, -, hne, hbase, -, -⟩ := hW
  obtain ⟨ψb, hψbc, hxb, hψbU, σb, hσi, hσW, ub, hubh, hub0, hs⟩ := BM.snc (pr x)
  obtain ⟨ψ', hψ'c, hsrc, hk1, hk2⟩ :=
    GlobalTheory.T.compatible_chart_product_projection_twisted e n RW.X BM.Rb.X RW.A BM.Rb.A pr (ψ x) (kb x) (σ x) ψb hcomp hψbc hbase
  have hsrc'' : (ψ'.restrOpen (V x) hVo).source = ψ'.source ∩ V x := ψ'.restrOpen_source (V x) hVo
  have hcoe : ∀ y, (ψ'.restrOpen (V x) hVo) y = ψ' y := fun y => rfl
  have hmem : ∀ y ∈ (ψ'.restrOpen (V x) hVo).source, y ∈ ψ'.source ∧ y ∈ V x ∧ pr y ∈ ψb.source := by
    intro y hy
    rw [hsrc''] at hy
    refine ⟨hy.1, hy.2, ?_⟩
    have := hy.1
    rw [hsrc] at this
    exact this.2
  refine ⟨ψ'.restrOpen (V x) hVo, compat_restr _ _ hψ'c _ hVo, ?_, ?_,
    Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map (σ x)) (some (i₀ x)),
    snoc_inj σb (σ x) (i₀ x) hne hσi, ?_, fun y => ub (pr y) * u x y, ?_, ?_, ?_⟩
  · rw [hsrc'', hsrc]
    exact ⟨⟨hVs hxV, hxb⟩, hxV⟩
  · intro y hy
    obtain ⟨-, hyV, hyb⟩ := hmem y hy
    exact ⟨hψbU hyb, hyV⟩
  · intro k
    induction k using Fin.lastCases with
    | last =>
      ext y
      simp only [Fin.snoc_last, Set.mem_inter_iff, Set.mem_setOf_eq, Option.some.injEq, exists_eq_left']
      constructor
      · rintro ⟨hd, hy⟩
        obtain ⟨hy', hyV, -⟩ := hmem y hy
        refine ⟨hy, ?_⟩
        rw [hcoe, hk2 y hy' _ hne]
        exact (hdiag y hyV).2 hd
      · rintro ⟨hy, h0⟩
        obtain ⟨hy', hyV, -⟩ := hmem y hy
        refine ⟨(hdiag y hyV).1 ?_, hy⟩
        rw [hcoe, hk2 y hy' _ hne] at h0
        exact h0
    | cast k =>
      ext y
      simp only [Fin.snoc_castSucc, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
      have hWk := Set.ext_iff.1 (hσW k) (pr y)
      constructor
      · rintro ⟨hw, hy⟩
        obtain ⟨hy', -, hyb⟩ := hmem y hy
        obtain ⟨-, i, hi, h0⟩ := hWk.1 ⟨hw, hyb⟩
        refine ⟨hy, σ x i, by rw [hi]; rfl, ?_⟩
        rw [hcoe, hk1 y hy']
        exact h0
      · rintro ⟨hy, i', hi', h0⟩
        obtain ⟨hy', -, hyb⟩ := hmem y hy
        obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hi'
        rw [hcoe, hk1 y hy'] at h0
        exact ⟨(hWk.2 ⟨hyb, i, hi, h0⟩).1, hy⟩
  · intro l z hz
    have h1 := holoOn_comp RW.A BM.Rb.A pr hp ψb.source ub hubh l z ⟨hz.1, (hmem _ hz.2).2.2⟩
    have h2 := huh l z ⟨hz.1, (hmem _ hz.2).2.1⟩
    exact h1.mul h2
  · intro y hy
    obtain ⟨-, hyV, hyb⟩ := hmem y hy
    exact mul_ne_zero (hub0 _ hyb) (hu0 _ hyV)
  · intro y hy
    obtain ⟨hy', hyV, hyb⟩ := hmem y hy
    have hi₀ : ψ' y (i₀ x) = ψ x y (i₀ x) := hk2 y hy' _ hne
    beta_reduce
    rw [Fin.prod_univ_castSucc, hs (pr y) hyb]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, pow_one, hcoe, diagSec, hi₀]
    refine mul_rearrange _ _ _ _ _ (Finset.prod_congr rfl fun k _ => ?_)
    cases h : σb k <;> simp [hk1 y hy']

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.isArithVar_of_snc_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model | exact GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model | (intros; apply GlobalTheory.CompanionTheory.Relay.isArithVar_of_snc_model <;> assumption)
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem _root_.GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  first | exact @LevelTowerAlt.orthogonal_family_adapted_basis | exact LevelTowerAlt.orthogonal_family_adapted_basis
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem _root_.GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  first | exact @LevelTowerAlt.label_degree_log_index | exact LevelTowerAlt.label_degree_log_index
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas

theorem first_minimum_cusp_weight_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ), 1 ≤ j' → ContinuousOn (fun t => (F.R t).lam1) (ballDom F.q) ∧ Measurable ((ballDom F.q).indicator fun t => (F.R t).cuspW F.σ) ∧ IsOpen (ballDom F.q) ∧ ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → (F.R t).lam1 = (F.R t').lam1 ∧ (F.R t).cuspW F.σ = (F.R t').cuspW F.σ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F hj
  have hO : IsOpen (ballDom F.q) := BallInverse.isOpen_ballDom F.q
  let U := ↥(ballDom F.q)
  let R : U → RiemLat E g Λ := fun t => F.R t.1
  have hP : ∀ v, Continuous fun x : U => (R x).P v := fun v =>
    continuousOn_iff_continuous_restrict.1 (F.hol.2 v).continuousOn
  have hH : Continuous fun x : U => (R x).Hm := GlobalTheory.T.continuous_hermitian_matrix_family E g Λ U R F.form (fun x => F.form_eq _) hP
  have hlam : Continuous fun x : U => (R x).lam1 := GlobalTheory.T.continuous_first_minimum_family E g Λ U R hP hH
  have hnz : ∀ I, Continuous fun x : U => (R x).nz F.σ I := fun I => GlobalTheory.T.continuous_cusp_norm_family E g Λ Ψ U R F.σ I hP hH
  have hbdd : ∀ x : U, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz F.σ I)} := by
    intro x
    have hr : (R x).HasRank F.σ j' := fun τ => (F.sig x.1 x.2 τ).1
    obtain ⟨-, -, h3, -, -⟩ := GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ (R x) F.σ j' F.cm hr hj
    refine ⟨(R x).cuspW F.σ, ?_⟩
    rintro y ⟨I, hI, rfl⟩
    exact (h3 I hI).1
  have hcw : Measurable fun x : U => (R x).cuspW F.σ :=
    GlobalTheory.T.measurable_cusp_weight_family E g Λ Ψ U R F.σ F.form (fun x => F.form_eq _) (fun I => (hnz I).measurable) hbdd
  refine ⟨continuousOn_iff_continuous_restrict.2 hlam, ?_, hO, ?_⟩
  · classical
    have e : (ballDom F.q).indicator (fun t => (F.R t).cuspW F.σ) =
        fun t => if h : t ∈ ballDom F.q then (R ⟨t, h⟩).cuspW F.σ else 0 := by
      funext t
      by_cases h : t ∈ ballDom F.q <;> simp [h, R]
    rw [e]
    exact Measurable.dite (s := ballDom F.q) hcw measurable_const hO.measurableSet
  · rintro t ht t' ht' ⟨γ, hγ, φ, hφ⟩
    have hf : ∀ x y, (F.R t').form (γ x) (γ y) = (F.R t).form x y := fun x y => by
      rw [F.form_eq, F.form_eq]
      exact hγ x y
    obtain ⟨h1, h2⟩ := GlobalTheory.T.isometry_preserves_hermitian_and_action E g Λ (F.R t) (F.R t') γ φ hf hφ
    have himg : φ '' Set.range (F.R t).P = Set.range (F.R t').P := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨γ x, hφ x⟩
      · rintro ⟨y, rfl⟩
        refine ⟨_, ⟨γ.symm y, rfl⟩, ?_⟩
        rw [← hφ, γ.apply_symm_apply]
    obtain ⟨a, b, -⟩ := GlobalTheory.T.cusp_weight_invariant_under_isometry E g Λ Ψ (F.R t) F.σ g Λ (F.R t') φ F.cm himg h1 h2
    exact ⟨b.symm, a.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.CompanionTheory.Relay.algebraic_square_xi_intersection : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ T : Fin (d + 1) → HermLine Q.ιW, (∀ j, IsSmoothHerm (T j)) → II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₀ (Fin.cons X₀ T)) - II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₁ (Fin.cons X₁ T)) = 2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  first | exact @PositivityTheory.Xgp.t_sq_R | exact PositivityTheory.Xgp.t_sq_R
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.exists_fundamental_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)), F.IsArith Γ → ∃ FF, F.IsFundSet Γ FF := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet | exact GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.exists_isFundSet <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence : Inputs → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ), MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH ∧ Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t)) (𝓝[>] 0) (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH)) := by
  intro hI d σ _ SY a₀ ε Q w
  classical
  have hCS : ConvergenceSignedStatement := hI.1.2.1
  have ht0 : 0 < Q.SW.t₀ := (Q.SW.reg none).1
  let mm : σ × Fin 2 → Option σ := fun i => if i.2 = 0 then some i.1 else if i.1 = a₀ then none else some i.1
  let c : σ × Fin 2 → ℝ := fun i => 1 / 2 * (ε i.1 : ℝ)
  have hph : ∀ x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.ph a (Q.q 0 x) + SY.ph a (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.ph (mm i) x := by
    intro x
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : Q.SW.ph (mm (a, 0)) x = SY.ph a (Q.q 0 x) := by simp [mm, Q.ph0]
    have e1 : Q.SW.ph (mm (a, 1)) x = SY.ph a (Q.q 1 x) := by
      by_cases ha : a = a₀
      · subst ha
        simp [mm, Q.ph1]
      · simp [mm, ha, Q.ph0]
        exact congrFun (Q.base_ph a ha) x
    rw [e0, e1]
    simp only [c]
    ring
  have hphT : ∀ t x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.phT (mm i) t x := by
    intro t x
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : Q.SW.phT (mm (a, 0)) t x = SY.phT a t (Q.q 0 x) := by simp [mm, Q.phase_some_eq_comp_first_projection]
    have e1 : Q.SW.phT (mm (a, 1)) t x = SY.phT a t (Q.q 1 x) := by
      by_cases ha : a = a₀
      · subst ha
        simp [mm, Q.phase_none_eq_comp_second_projection]
      · simp [mm, ha, Q.phase_some_eq_comp_first_projection]
        exact congrFun (Q.base_phT a ha t) x
    rw [e0, e1]
    simp only [c]
    ring
  have hgH : Q.gH = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.ph (mm i) x) := by
    funext x
    simp only [AnSq.gH]
    rw [hph]
    ring
  have hgT : ∀ t, Q.gT t = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) := by
    intro t
    funext x
    simp only [AnSq.gT]
    rw [hphT]
    ring
  obtain ⟨hsI, hsE, hsT⟩ := PositivityTheory.Xgp.sq_limit.singular_part hI Q w
  obtain ⟨hrI, hrT⟩ := PositivityTheory.Xgp.sq_limit.regular hCS Q.SW w mm c Q.cst ht0
  refine ⟨?_, ?_⟩
  · rw [hgH]
    exact PositivityTheory.Xgp.sq_limit.mIntegrable_add' _ _ hsI hrI
  · rw [hgH, PositivityTheory.Xgp.sq_limit.mInt_add' _ _ hsI hrI]
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v) + mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (fun x => Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) = mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t) := by
      filter_upwards [hsE, Ioo_mem_nhdsGT ht0] with t ht htt
      rw [hgT t]
      refine (PositivityTheory.Xgp.sq_limit.mInt_add' _ _ ht ?_).symm
      apply PositivityTheory.Xgp.sq_limit.mIntegrable_of_continuous
      · intro i
        exact ReciprocityTheory.AnForm.M.isPotentialAdd _ _ _ (Q.SW.sing (w i)).1 (ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ ((Q.SW.reg (w i)).2.2 t htt.1 htt.2.le).1)
      · exact continuous_const.add (continuous_finsetSum _ fun i _ => continuous_const.mul (ReciprocityTheory.AnForm.M.projLine_continuous_of_smooth _ ((Q.SW.reg (mm i)).2.2 t htt.1 htt.2.le).1))
    exact (hsT.add hrT).congr' hev
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.proportional_minors_block_triangular : ∀ (N j : ℕ) (i : Fin N) (h₁ h₂ : Matrix (Fin N) (Fin N) ℂ) (α β : ℂ), j ≤ N → IsBlockDiag j h₁ → IsBlockDiag j h₂ → h₁.det ≠ 0 → α ≠ 0 → β ≠ 0 → (∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i)) → ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → (h₁⁻¹ * h₂) r c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PlVanish.quot_vanish | exact GlobalTheory.CompanionTheory.Ar.PB.PlVanish.quot_vanish | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PlVanish.quot_vanish <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.regular_function_analytic_on_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (s : Ω) (e n : ℕ) (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → Rb.X) (w₀ : Fin e → ℂ), IsOpen Un → w₀ ∈ Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (Rb.A.chart k).source)) → RegAt x (mCoordIdeal (Rb.lift (bp w₀) (bp w₀))) s → AnalyticAt ℂ (fun w => valAt x s (Rb.lift (bp w) (bp w))) w₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan


theorem _root_.GlobalTheory.T.block_LU_factorization : ∀ (N j : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ G = L * U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LU.exists_lower_upper <;> assumption)
end

end

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem _root_.GlobalTheory.T.adapted_family_exists_on_eigenspace : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  first | exact @GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace | exact GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace | (intros; apply GlobalTheory.CompanionTheory.Relay.adapted_family_exists_on_eigenspace <;> assumption)

end
end

section

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem _root_.GlobalTheory.T.labelled_degree_eq_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index | exact GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index | (intros; apply GlobalTheory.CompanionTheory.Relay.labelled_degree_eq_log_index <;> assumption)

end
end
