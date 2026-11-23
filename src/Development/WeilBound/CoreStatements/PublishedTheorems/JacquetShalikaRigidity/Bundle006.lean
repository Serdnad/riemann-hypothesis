module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle395
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QuadraticTransferReal

theorem swap3 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ρ : Measure β) (ν : Measure γ) [SFinite μ] [SFinite ρ] [SFinite ν]
    (F : α → β → γ → ℝ≥0∞) (hF : Measurable fun p : α × β × γ => F p.1 p.2.1 p.2.2) :
    ∫⁻ g, ∫⁻ r, ∫⁻ h, F g r h ∂ν ∂ρ ∂μ = ∫⁻ r, ∫⁻ h, ∫⁻ g, F g r h ∂μ ∂ν ∂ρ := by
  have h1 : Measurable fun q : α × β => ∫⁻ h, F q.1 q.2 h ∂ν := by
    have : Measurable fun p : (α × β) × γ => F p.1.1 p.1.2 p.2 :=
      hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap (f := fun g r => ∫⁻ h, F g r h ∂ν) h1.aemeasurable]
  refine lintegral_congr fun r => ?_
  have h2 : Measurable fun q : α × γ => F q.1 r q.2 :=
    hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact lintegral_lintegral_swap (f := fun g h => F g r h) h2.aemeasurable

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem q1' (μ : Measure G) [μ.IsHaarMeasure] (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G)
    (β β₁ : G → ℝ≥0∞) (hinv : Measure.map (fun h => h⁻¹) ν = ν) (hH : ∀ᵐ h ∂ν, h ∈ H)
    (hβ : IsWt ν β) (hβ₁ : Measurable β₁) (h1 : ∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦH : ∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) :
    ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁ := by
  have hβm := hβ.1
  have hm : Measurable fun p : G × G × G => β p.1 * Φ p.1 * β₁ (p.2.1⁻¹ * p.2.2 * p.1) := by fun_prop
  have hm' : Measurable fun p : G × G × G => β₁ p.1 * (Φ (p.2.1 * p.1) * β (p.2.2⁻¹ * p.2.1 * p.1)) := by
    fun_prop
  have hint : ∀ x, ∫⁻ h, β (h⁻¹ * x) ∂ν = 1 := by
    intro x
    have := lintegral_map (f := fun h => β (h * x)) (g := fun h : G => h⁻¹) (μ := ν)
      (hβm.comp (measurable_mul_const x)) measurable_inv
    rw [hinv, hβ.2 x] at this
    exact this.symm
  have hR : Measurable fun g => ∫⁻ r, Φ (r * g) ∂ρ := by
    have : Measurable fun p : G × G => Φ (p.2 * p.1) := hΦ.comp (measurable_snd.mul measurable_fst)
    exact this.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hΦ, lintegral_withDensity_eq_lintegral_mul _ hβ₁ hR]
  calc ∫⁻ g, (β * Φ) g ∂μ
      = ∫⁻ g, ∫⁻ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν ∂ρ ∂μ := by
        refine lintegral_congr fun g => ?_
        have hr : Measurable fun r => ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          have : Measurable fun p : G × G => β₁ (p.1⁻¹ * p.2 * g) := by fun_prop
          exact this.lintegral_prod_right'
        have e : ∀ r, ∫⁻ h, β g * Φ g * β₁ (r⁻¹ * h * g) ∂ν = β g * Φ g * ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν := by
          intro r
          exact lintegral_const_mul _ (by fun_prop)
        simp only [e, Pi.mul_apply]
        rw [lintegral_const_mul _ hr, h1 g, mul_one]
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β g * Φ g * β₁ (r⁻¹ * h * g) ∂μ ∂ν ∂ρ :=
        swap3 μ ρ ν (fun g r h => β g * Φ g * β₁ (r⁻¹ * h * g)) hm
    _ = ∫⁻ r, ∫⁻ h, ∫⁻ g, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂μ ∂ν ∂ρ := by
        refine lintegral_congr fun r => lintegral_congr_ae ?_
        filter_upwards [hH] with h hh
        rw [← lintegral_mul_left_eq_self _ (h⁻¹ * r)]
        refine lintegral_congr fun g => ?_
        have e1 : r⁻¹ * h * (h⁻¹ * r * g) = g := by group
        have e2 : Φ (h⁻¹ * r * g) = Φ (r * g) := by
          have := hΦH h hh (h⁻¹ * (r * g))
          rw [mul_inv_cancel_left] at this
          rw [mul_assoc]
          exact this.symm
        simp only [e1, e2]
        ring
    _ = ∫⁻ g, ∫⁻ r, ∫⁻ h, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂ν ∂ρ ∂μ :=
        (swap3 μ ρ ν (fun g r h => β₁ g * (Φ (r * g) * β (h⁻¹ * r * g))) hm').symm
    _ = ∫⁻ g, (β₁ * fun g => ∫⁻ r, Φ (r * g) ∂ρ) g ∂μ := by
        refine lintegral_congr fun g => ?_
        have e : ∀ r, ∫⁻ h, β₁ g * (Φ (r * g) * β (h⁻¹ * r * g)) ∂ν = β₁ g * Φ (r * g) := by
          intro r
          simp_rw [← mul_assoc (β₁ g)]
          rw [lintegral_const_mul _ (by fun_prop)]
          simp_rw [mul_assoc _ r g]
          rw [hint, mul_one]
        simp only [e, Pi.mul_apply]
        exact lintegral_const_mul _ (hΦ.comp (measurable_mul_const g))

end

theorem real_transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (A : Measure X)
    (B : Measure Y) (m : Y → X) (F : X → ℝ) (hi : Integrable F A) (hiB : Integrable (fun y => F (m y)) B)
    (h₁ : ∫⁻ x, ENNReal.ofReal (F x) ∂A = ∫⁻ y, ENNReal.ofReal (F (m y)) ∂B)
    (h₂ : ∫⁻ x, ENNReal.ofReal (-F x) ∂A = ∫⁻ y, ENNReal.ofReal (-F (m y)) ∂B) :
    ∫ x, F x ∂A = ∫ y, F (m y) ∂B := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiB, h₁, h₂]

theorem transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (A : Measure X)
    (B : Measure Y) (m : Y → X) (hm : Measurable m) (Φ : X → ℂ) (hΦ : Measurable Φ) (P : (X → ℝ≥0∞) → Prop)
    (hP : ∀ f, Measurable f → P f → ∫⁻ x, f x ∂A = ∫⁻ y, f (m y) ∂B)
    (hn : P fun x => ‖Φ x‖ₑ) (hr₁ : P fun x => ENNReal.ofReal (Φ x).re)
    (hr₂ : P fun x => ENNReal.ofReal (-(Φ x).re)) (hi₁ : P fun x => ENNReal.ofReal (Φ x).im)
    (hi₂ : P fun x => ENNReal.ofReal (-(Φ x).im)) (hi : Integrable Φ A) :
    Integrable (fun y => Φ (m y)) B ∧ ∫ x, Φ x ∂A = ∫ y, Φ (m y) ∂B := by
  have hiB : Integrable (fun y => Φ (m y)) B := by
    refine ⟨(hΦ.comp hm).aestronglyMeasurable, ?_⟩
    have := hP _ (by fun_prop) hn
    rw [HasFiniteIntegral, ← this]
    exact hi.2
  refine ⟨hiB, ?_⟩
  apply Complex.ext
  · have a1 := integral_re hi
    have a2 := integral_re hiB
    simp only [RCLike.re_to_complex] at a1 a2
    rw [← a1, ← a2]
    exact real_transfer A B m (fun x => (Φ x).re) hi.re hiB.re
      (hP _ (by fun_prop) hr₁) (hP _ (by fun_prop) hr₂)
  · have a1 := integral_im hi
    have a2 := integral_im hiB
    simp only [RCLike.im_to_complex] at a1 a2
    rw [← a1, ← a2]
    exact real_transfer A B m (fun x => (Φ x).im) hi.im hiB.im
      (hP _ (by fun_prop) hi₁) (hP _ (by fun_prop) hi₂)

end QuadraticTransferReal

theorem closedSubgroup_cutoff_exists : Q2 := by
  intro G _ _ _ _ _ _ _ μ _ ν ρ _ _ H β β₁ hinv hH hβ hβ₁ h1 Φ hΦ hΦH hi
  have hm : Measurable fun p : G × G => p.2 * p.1 := measurable_snd.mul measurable_fst
  have key := QuadraticTransferReal.transfer (μ.withDensity β) ((μ.withDensity β₁).prod ρ) (fun p : G × G => p.2 * p.1) hm Φ hΦ
    (fun f => ∀ h ∈ H, ∀ g, f (h * g) = f g)
    (fun f hf hfH => by
      rw [QuadraticTransferReal.q1' μ ν ρ H β β₁ hinv hH hβ hβ₁ h1 f hf hfH, lintegral_prod (fun p : G × G => f (p.2 * p.1)) (hf.comp hm).aemeasurable])
    (fun h hh g => by simp only [hΦH h hh]) (fun h hh g => by simp only [hΦH h hh])
    (fun h hh g => by simp only [hΦH h hh]) (fun h hh g => by simp only [hΦH h hh])
    (fun h hh g => by simp only [hΦH h hh]) hi
  obtain ⟨hiB, he⟩ := key
  refine ⟨hiB.integral_prod_left, ?_⟩
  rw [he, integral_prod _ hiB]

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKLt2

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem lastRow_eq (hk : 1 ≤ k) (y : GA E k) (c : Fin k) :
    lastRow y c = y.val ⟨k - 1, by omega⟩ c := by
  unfold lastRow
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp only
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lastRow_mir (hk : 1 ≤ k) (p y : GA E k) (hp : Mir (k - 1) p) : lastRow (p * y) = lastRow y := by
  funext c
  rw [lastRow_eq hk, lastRow_eq hk, Units.val_mul, Matrix.mul_apply]
  have h1 : ∀ j, p.val ⟨k - 1, by omega⟩ j = (1 : Matrix (Fin k) (Fin k) (Ad E)) ⟨k - 1, by omega⟩ j :=
    fun j => hp _ _ (Or.inl le_rfl)
  simp only [h1, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp

omit [NumberField E] in
theorem isMir_emb {m : ℕ} (ιE : GL (Fin k) E →* GL (Fin m) E) (h : IsEmb ιE) (γ : GL (Fin k) E) :
    IsMir k (ιE γ) := by
  intro i c hic
  rw [h γ, embM, Matrix.of_apply, dite_eq_right (by omega)]

end PKLt2

theorem kernel_less_second_of : D0 → N0 → H0 → RowsInCompactSet → K1 → CornerEmbedding → TransformsEmbedding → FourierSeriesColumn → ShortRowsEmbedding → K6 → KLt2 := by
  intro hD0 hN0 hH0 hG5 hK1 hK5e hK5a hK5b hK5c hK6 E _ _ _ m k hk hkm ψ hψ S hS ι hι α α' φ' hsec U φ hprep
  obtain ⟨hDpos, hDmul, hDcont, hDrat, -⟩ := hD0 E k
  obtain ⟨hFgood, hpT, -, -, hsupp, hbd⟩ := hK5a E m k hk hkm ψ hψ ι hι φ hprep.good
  obtain ⟨C6, hC6c, hC6⟩ := hK6 E m k hk hkm ψ hψ S hS ι hι α (m ^ 3) U φ hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, hNlast⟩ := hN0 E k k hk le_rfl
  obtain ⟨hhtpos, -, -, -, hB5, -, -⟩ := hH0 E k
  obtain ⟨-, hdminpos, -⟩ := hK1 E m (by omega)
  obtain ⟨hιc, -, -, -, -, -, hιrat, -⟩ := (hK5e E m k hkm.le).2 ι hι
  obtain ⟨ιE, hιE⟩ := (hK5e E m k hkm.le).1 E
  have hrow : ∀ (g : GA E k) (ξ : RowT E k k),
      pT ψ k (m - k) (φ : GA E m → ℂ) (ι (ratGL E k (gam ξ) * g)) ≠ 0 →
      lastRow (ratGL E k (gam ξ) * g) ∈ C6 := by
    intro g ξ hne
    obtain ⟨p, hp, hw⟩ := hsupp _ hne
    have := hC6 _ hw
    rwa [PKLt2.lastRow_mir hk _ _ hp] at this
  have hfin : ∀ g : GA E k,
      {ξ : RowT E k k | colT ψ k (pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ))
        (ι (ratGL E k (gam ξ) * g)) ≠ 0}.Finite := by
    intro g
    exact ((hG5 E k hk C6 hC6c).1 g).subset fun ξ hξ => hrow g ξ (by rw [hpT]; exact hξ)
  have hsumF : ∀ g, sumF (fun g => pT ψ k (m - k) (φ : GA E m → ℂ) (ι g)) g =
      pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) := by
    intro g
    rw [hpT]
    exact (hK5b E m k hk hkm ψ hψ ι hι _ hFgood g).2 (hfin g)
  have hFb : ∀ x, ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) x‖ ≤ ‖φ‖ := fun x =>
    hbd (k + 1) x ‖φ‖ (by omega) (by omega) fun u _ => φ.norm_coe_le_norm _
  have hcpow : ∀ g : GA E k, ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖ = Dt g ^ (-(((m : ℝ) - k) / 2)) := by
    intro g
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hDpos g)]
    congr 1
    simp
  have hcont : Continuous fun g : GA E k => pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) *
      conj (φ' g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) := by
    refine ((hFgood.cont.comp hιc).mul (Complex.continuous_conj.comp φ'.continuous)).mul ?_
    exact (Complex.continuous_ofReal.comp hDcont).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)
  simp_rw [hsumF]
  refine ⟨hcont.measurable, measurable_zero, ?_, fun _ _ => rfl, fun _ _ => rfl, ⟨0, fun _ => by simp⟩, ?_, ?_⟩
  · intro γ g
    dsimp only
    rw [map_mul ι, hιrat ιE hιE γ, hFgood.left _ (PKLt2.isMir_emb ιE hιE γ), hsec.inv γ g, hDmul, hDrat, one_mul]
  · intro M
    obtain ⟨C₂, hC₂⟩ := hsec.dec (k * M)
    obtain ⟨B, hB⟩ := hB5 C6 hC6c
    refine ⟨‖φ‖ * max C₂ 0 * max B 0 ^ (k * M), fun g hg => ?_⟩
    have hD := hDpos g
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hnorm : ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖ ≤ 1 := by
      rw [hcpow]
      apply Real.rpow_le_one_of_one_le_of_nonpos hg
      have : (k : ℝ) < m := by exact_mod_cast hkm
      linarith
    have hnn : 0 ≤ max B 0 ^ (k * M) * (Dt g ^ M)⁻¹ := by positivity
    by_cases hz : pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) = 0
    · rw [hz, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _)) (by positivity))
        (by positivity)
    obtain ⟨ξ, hξ⟩ : ∃ ξ : RowT E k k, pT ψ k (m - k) (φ : GA E m → ℂ) (ι (ratGL E k (gam ξ) * g)) ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      apply hz
      rw [← hsumF g, sumF]
      simp only [hcon, tsum_zero]
    have hlr := hrow g ξ hξ
    rw [hNlast ξ g] at hlr
    have hht := hB g ξ.1 ξ.2.1 hlr
    have hp := hhtpos g ξ.1 ξ.2.1
    have hht2 : ht g ξ.1 ≤ max B 0 / Dt g ^ ((k : ℝ)⁻¹) := by
      unfold ht
      gcongr
      exact hht.trans (le_max_left _ _)
    have hDk : (Dt g ^ ((k : ℝ)⁻¹)) ^ (k * M) = Dt g ^ M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul,
        Real.rpow_natCast]
    have hpow : ht g ξ.1 ^ (k * M) ≤ max B 0 ^ (k * M) * (Dt g ^ M)⁻¹ := by
      calc ht g ξ.1 ^ (k * M) ≤ (max B 0 / Dt g ^ ((k : ℝ)⁻¹)) ^ (k * M) := pow_le_pow_left₀ hp.le hht2 _
        _ = _ := by rw [div_pow, hDk, div_eq_mul_inv]
    have hφ' : ‖φ' g‖ ≤ max C₂ 0 * (max B 0 ^ (k * M) * (Dt g ^ M)⁻¹) :=
      (hC₂ g ξ.1 ξ.2.1).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    calc ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ * ‖φ' g‖ * ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖
        ≤ ‖φ‖ * (max C₂ 0 * (max B 0 ^ (k * M) * (Dt g ^ M)⁻¹)) * 1 :=
          mul_le_mul (mul_le_mul (hFb _) hφ' (norm_nonneg _) (norm_nonneg _)) hnorm (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hφ'))
      _ = _ := by ring
  · obtain ⟨C5, hC5⟩ := hK5c E m k hk hkm ι hι
    obtain ⟨Cφ, hCφ⟩ := hprep.dec
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    have hkm' : (k : ℝ) < m := by exact_mod_cast hkm
    have hm0 : (m : ℝ) ≠ 0 := by linarith
    have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have he : (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ) = (m : ℝ) ^ 2 / ((m : ℝ) - 1) := by
      push_cast
      field_simp
      ring
    have hmle : (m : ℝ) ≤ (m : ℝ) ^ 2 / ((m : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hexp : 0 ≤ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ) + -(((m : ℝ) - k) / 2) := by
      rw [he]
      linarith
    refine ⟨max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖, fun g hg => ?_⟩
    have hD := hDpos g
    have hFs : ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ ≤ max Cφ 0 * (max C5 0 ^ (m ^ 3) *
        Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ))) := by
      refine hbd (k + 1) (ι g) _ (by omega) (by omega) fun u hu => ?_
      have hdm := (hC5 g u).2 hu
      have hpos := hdminpos (u * ι g)
      have hw0 : 0 ≤ wt (m ^ 3) (u * ι g) := pow_nonneg (le_min zero_le_one hpos.le) _
      calc ‖φ (u * ι g)‖ ≤ Cφ * wt (m ^ 3) (u * ι g) := hCφ _
        _ ≤ max Cφ 0 * wt (m ^ 3) (u * ι g) := mul_le_mul_of_nonneg_right (le_max_left _ _) hw0
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          unfold wt
          calc min 1 (dmin (u * ι g)) ^ (m ^ 3)
              ≤ (max C5 0 * Dt g ^ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹)) ^ (m ^ 3) :=
                pow_le_pow_left₀ (le_min zero_le_one hpos.le) ((min_le_right _ _).trans (hdm.trans
                  (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hD.le _)))) _
            _ = _ := by rw [mul_pow, ← Real.rpow_natCast (Dt g ^ _), ← Real.rpow_mul hD.le]
    have hrp : Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ)) * Dt g ^ (-(((m : ℝ) - k) / 2)) ≤ 1 := by
      rw [← Real.rpow_add hD]
      exact Real.rpow_le_one hD.le hg.le hexp
    have hφ'b : ‖φ' g‖ ≤ ‖φ'‖ := φ'.norm_coe_le_norm g
    have hA : 0 ≤ max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _)) (norm_nonneg _)
    rw [Pi.zero_apply, sub_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le, norm_mul, norm_mul,
      RCLike.norm_conj, hcpow, mul_comm _ (Dt g)]
    apply mul_le_mul_of_nonneg_left _ hD.le
    calc ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ * ‖φ' g‖ * Dt g ^ (-(((m : ℝ) - k) / 2))
        ≤ max Cφ 0 * (max C5 0 ^ (m ^ 3) * Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ))) *
            ‖φ'‖ * Dt g ^ (-(((m : ℝ) - k) / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hD.le _)
          exact mul_le_mul hFs hφ'b (norm_nonneg _) ((norm_nonneg _).trans hFs)
      _ = max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ * (Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ)) *
            Dt g ^ (-(((m : ℝ) - k) / 2))) := by ring
      _ ≤ max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ * 1 := mul_le_mul_of_nonneg_left hrp hA
      _ = _ := mul_one _

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem ksec_of : jumpWindows.G2c → jumpWindows.G5 → CuspDecayShortRowColumn → K9 → KSec := by
  intro hG2c hG5 hG1d hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS => ⟨(hS₀ S hS).1, fun α hα => ?_⟩⟩
  obtain ⟨φ, hφ, h, x, hh, hx, hsat, -, hone⟩ := (hS₀ S hS).2 α hα
  have hval : ∀ g, Rt E k h x g = φ.1 (g * h) := fun g => by rw [Rt_apply, hx]
  have hgood : Good ψ (k - 1) (x : GA E k → ℂ) := by
    rw [hx]; exact good_of_isCuspForm E k ψ φ (π.cusp φ hφ)
  refine ⟨φ, hφ, h, Rt E k h x, hval, ?_⟩
  refine ⟨(hG5 E k ψ hψ).2.2.1 x h hgood, ?_, ?_, ?_, ?_, ?_, hone⟩
  · intro γ g
    rw [hval, hval, mul_assoc]
    exact (π.cusp φ hφ).1.left γ (g * h)
  · intro t g
    rw [hval, hval, mul_assoc]
    exact hπ φ hφ t (g * h)
  · intro w
    obtain ⟨Y, -, hYst, hYmem⟩ := hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
    exact (hYmem _).1 (hYst h (hh w.1 w.2) x ((hYmem x).2 (hsat w)))
  · have e : (⇑(Rt E k h x) : GA E k → ℂ) = fun g => φ.1 (g * h) := funext hval
    rw [e]
    exact (hG1d E k hk π hπ φ hφ h).1
  · have := (hG1d E k hk π hπ φ hφ h).2
    simpa only [hval] using this

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace VectorMeasureTranspose

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def trM (g : GA E k) : GA E k :=
  ⟨(g.val)ᵀ, (g⁻¹.val)ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem det_trM (g : GA E k) : GeneralLinearGroup.det (trM g) = GeneralLinearGroup.det g := by
  exact Units.ext (Matrix.det_transpose g.val)

theorem Dt_trM (g : GA E k) : Dt (trM g) = Dt g := by
  unfold Dt
  rw [det_trM]

theorem vecMeasure_eq : vecMeasure E (Fin k) = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := rfl

theorem vecMul_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have hm : Measurable fun x : Fin k → Ad E => x ᵥ* g.val := GroundTheory.Automorphic.GJGlobal.Modulus.measurable_vecMul' g
  have e1 : ∫⁻ x, F x ∂((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E).map fun x : Fin k → Ad E => x ᵥ* g.val) =
      ∫⁻ x, F (x ᵥ* g.val) ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := lintegral_map hF hm
  have h := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  unfold Dt
  rw [vecMeasure_eq, ← e1, h, lintegral_smul_measure]
  try rw [smul_eq_mul]

theorem mulVec_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (g.val *ᵥ x) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have e : ∀ x : Fin k → Ad E, F (g.val *ᵥ x) = F (x ᵥ* (trM g).val) := fun x => by
    show F (g.val *ᵥ x) = F (x ᵥ* (g.val)ᵀ)
    rw [Matrix.vecMul_transpose]
  refine (lintegral_congr e).trans ?_
  rw [vecMul_eq (trM g) F hF, Dt_trM]

end VectorMeasureTranspose

theorem linear_change_variables_of : D0 → AdelicLinearChange := by
  intro _ E _ _ _ k g F hF
  exact ⟨VectorMeasureTranspose.mulVec_eq g F hF, VectorMeasureTranspose.vecMul_eq g F hF⟩

end PositivityTheory.AdelicQuotientData

end
end
