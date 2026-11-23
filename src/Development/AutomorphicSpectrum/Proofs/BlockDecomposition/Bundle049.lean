module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle004
public import Mathlib.Topology.Separation.Hausdorff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle003
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
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCell

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

lemma rp_mk (P : Subgroup G) (g : G) : ∃ p ∈ P, rp (QuotientGroup.mk g : G ⧸ P) = p * g⁻¹ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul P g
  refine ⟨(k : G)⁻¹, P.inv_mem k.2, ?_⟩
  have : Quotient.out (QuotientGroup.mk g : G ⧸ P) = g * k := hk
  simp [rp, this]

lemma rp_smul (P : Subgroup G) (x : G) (q : G ⧸ P) : ∃ p ∈ P, rp (x⁻¹ • q) = p * (rp q * x) := by
  obtain ⟨p, hp, e⟩ := rp_mk P (x⁻¹ * Quotient.out q)
  refine ⟨p, hp, ?_⟩
  have hq : (QuotientGroup.mk (x⁻¹ * Quotient.out q) : G ⧸ P) = x⁻¹ • q := by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [← hq, e]
  simp [rp]

lemma rp_mk_mem_iff {P : Subgroup G} {Ω : Set G} (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) (g : G) :
    rp (QuotientGroup.mk g : G ⧸ P) ∈ Ω ↔ g⁻¹ ∈ Ω := by
  obtain ⟨p, hp, e⟩ := rp_mk P g
  rw [e]
  refine ⟨fun H => ?_, hl p hp _⟩
  simpa using hl p⁻¹ (P.inv_mem hp) _ H

def coord {N : Type} [Zero N] {P : Subgroup G} (Ω : Set G) (τ : G → N) (q : G ⧸ P) : N :=
  open Classical in if rp q ∈ Ω then τ (rp q) else 0

lemma coord_of_mem {N : Type} [Zero N] {P : Subgroup G} {Ω : Set G} {τ : G → N} {q : G ⧸ P}
    (hq : rp q ∈ Ω) : coord Ω τ q = τ (rp q) := by
  simp [coord, hq]

lemma isOpen_bar [IsTopologicalGroup G] {N : Type} [TopologicalSpace N] {P : Subgroup G} {Ω : Set G}
    {τ : G → N} (hΩ : IsOpen Ω) (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x)
    (hτ : ContinuousOn τ Ω) {U : Set N} (hU : IsOpen U) :
    IsOpen {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} := by
  have hl' : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω := fun p hp x hx => (hl p hp x hx).1
  rw [← (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.isOpen_preimage]
  have : (QuotientGroup.mk : G → G ⧸ P) ⁻¹' {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U}
      = (fun g : G => g⁻¹) ⁻¹' (Ω ∩ τ ⁻¹' U) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [rp_mk_mem_iff hl' g]
    obtain ⟨p, hp, e⟩ := rp_mk P g
    refine and_congr_right fun hg => ?_
    rw [e, (hl p hp _ hg).2]
  rw [this]
  exact (hτ.isOpen_inter_preimage hΩ hU).preimage continuous_inv

lemma measurable_coord [IsTopologicalGroup G] {N : Type} [AddCommGroup N] [TopologicalSpace N]
    [MeasurableSpace N] [BorelSpace N] {P : Subgroup G} [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    {Ω : Set G} {τ : G → N} (hΩ : IsOpen Ω) (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x)
    (hτ : ContinuousOn τ Ω) : Measurable (coord Ω τ : G ⧸ P → N) := by
  refine measurable_of_isOpen fun U hU => ?_
  have hA := (isOpen_bar (P := P) hΩ hl hτ hU).measurableSet
  have hB : MeasurableSet {q : G ⧸ P | rp q ∈ Ω} := by
    have := (isOpen_bar (P := P) hΩ hl hτ (isOpen_univ (X := N))).measurableSet
    simpa using this
  by_cases h0 : (0 : N) ∈ U
  · have : (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} ∪ {q : G ⧸ P | rp q ∈ Ω}ᶜ := by
      ext q
      by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]
    rw [this]
    exact hA.union hB.compl
  · have : (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} := by
      ext q
      by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]
    rw [this]
    exact hA

theorem cellFormula_of_invM (hI : InvM) : CellFormula := by
  intro G _ _ _ _ _ _ P _ _ h mu hs ν hν N _ _ _ _ _ _ _ _ lam _ Ω τ w nb hc hInv hh hnull
  haveI : IsFiniteMeasure ν := hν.1
  have ρc : Continuous fun y => h (w * nb y) := hs.cont.comp (continuous_const.mul hc.nbCont)
  have ρpos : ∀ y, 0 < h (w * nb y) := fun y => hs.pos _
  let D : N → ℝ≥0 := fun y => (1 / h (w * nb y)).toNNReal
  have Dc : Continuous D :=
    continuous_real_toNNReal.comp (continuous_const.div ρc fun y => (ρpos y).ne')
  have Dm : Measurable D := Dc.measurable
  let T : G ⧸ P → N := coord Ω τ
  have Tm : Measurable T := measurable_coord hc.isOpen hc.left hc.cont
  let lam' : Measure N := (ν.map T).withDensity fun y => (D y : ℝ≥0∞)
  have hlin : ∀ φ : N → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ y ∂lam' = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν := by
    intro φ hφ
    have h1 : Measurable fun y => (D y : ℝ≥0∞) := Dm.coe_nnreal_ennreal
    rw [lintegral_withDensity_eq_lintegral_mul _ h1 hφ, lintegral_map (h1.mul hφ) Tm]
    rfl
  have hae : ∀ᵐ q ∂ν, rp q ∈ Ω := by
    rw [ae_iff]
    exact hnull
  have hshift : ∀ (a : N) (φ : N → ℝ≥0∞), Measurable φ →
      ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (a + T q) ∂ν = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν := by
    intro a φ hφ
    have hF : Measurable fun q => (D (T q) : ℝ≥0∞) * φ (T q) :=
      ((Dm.comp Tm).coe_nnreal_ennreal).mul (hφ.comp Tm)
    rw [← (hI G P h mu hs ν hν (nb a) (hInv a)).2 _ hF]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    obtain ⟨p, hp, e⟩ := rp_smul P (nb a) q
    have hr := hc.right a _ hq
    have hl := hc.left p hp _ hr.1
    have hmem : rp ((nb a)⁻¹ • q) ∈ Ω := e ▸ hl.1
    have e1 : T ((nb a)⁻¹ • q) = τ (rp q) + a := by
      change coord Ω τ _ = _
      rw [coord_of_mem hmem, e, hl.2, hr.2]
    have e0 : T q = τ (rp q) := coord_of_mem hq
    rw [e1, e0, add_comm a]
    have hq1 := hh a _ hq
    set y := τ (rp q)
    have p1 := ρpos y
    have p2 := ρpos (y + a)
    have p3 := hs.pos (rp q)
    have hD : (D y : ℝ≥0∞) = (D (y + a) : ℝ≥0∞) * ENNReal.ofReal (h (rp q * nb a) / h (rp q)) := by
      change ENNReal.ofReal _ = ENNReal.ofReal _ * _
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      linarith
    rw [hD]
    ring
  haveI hinv : lam'.IsAddLeftInvariant := by
    refine ⟨fun a => Measure.ext fun S hS => ?_⟩
    rw [Measure.map_apply (measurable_const_add a) hS]
    have hS' : MeasurableSet ((fun y => a + y) ⁻¹' S) := measurable_const_add a hS
    have hi : Measurable (S.indicator (1 : N → ℝ≥0∞)) := measurable_one.indicator hS
    have hi' : ((fun y => a + y) ⁻¹' S).indicator (1 : N → ℝ≥0∞)
        = fun y => S.indicator (1 : N → ℝ≥0∞) (a + y) := by
      ext y
      by_cases hy : a + y ∈ S
      · rw [Set.indicator_of_mem (show y ∈ (fun y => a + y) ⁻¹' S from hy), Set.indicator_of_mem hy]
        rfl
      · rw [Set.indicator_of_notMem (show y ∉ (fun y => a + y) ⁻¹' S from hy),
          Set.indicator_of_notMem hy]
    have hi2 : Measurable fun y => S.indicator (1 : N → ℝ≥0∞) (a + y) :=
      hi.comp (measurable_const_add a)
    rw [← lintegral_indicator_one hS', ← lintegral_indicator_one hS, hi', hlin _ hi2, hlin _ hi]
    exact hshift a _ hi
  haveI : IsLocallyFiniteMeasure lam' := IsLocallyFiniteMeasure.withDensity_coe Dc
  have e := Measure.isAddLeftInvariant_eq_smul lam' lam
  refine ⟨Measure.addHaarScalarFactor lam' lam, fun f hf hoc => ?_⟩
  rw [← e]
  have gc : Continuous fun y => f (w * nb y) := hf.1.comp (continuous_const.mul hc.nbCont)
  have ψc : Continuous fun y => D y • f (w * nb y) := Dc.smul gc
  have hcomp : (fun q => D (T q) • f (w * nb (T q))) =ᵐ[ν] fun q => f (rp q) / h (rp q) := by
    filter_upwards [hae] with q hq
    have e0 : T q = τ (rp q) := coord_of_mem hq
    rw [e0]
    have h1 := hoc _ hq
    set y := τ (rp q)
    have p1 := ρpos y
    have p3 := hs.pos (rp q)
    have hDy : ((D y : ℝ≥0) : ℝ) = 1 / h (w * nb y) := Real.coe_toNNReal _ (by positivity)
    have c1 : (h (w * nb y) : ℂ) ≠ 0 := by exact_mod_cast p1.ne'
    have c3 : (h (rp q) : ℂ) ≠ 0 := by exact_mod_cast p3.ne'
    rw [NNReal.smul_def, Complex.real_smul, hDy]
    push_cast
    field_simp
    linear_combination -h1
  obtain ⟨hint, hmu⟩ := hν.2 f hf
  constructor
  · refine (integrable_withDensity_iff_integrable_smul Dm).2 ?_
    refine (integrable_map_measure ψc.aestronglyMeasurable Tm.aemeasurable).2 ?_
    exact hint.congr hcomp.symm
  · rw [hmu]
    change _ = ∫ y, f (w * nb y) ∂((ν.map T).withDensity fun y => (D y : ℝ≥0∞))
    rw [integral_withDensity_eq_integral_smul Dm, integral_map Tm.aemeasurable ψc.aestronglyMeasurable]
    exact (integral_congr_ae hcomp).symm

end GlobalTheory.CompanionTheory.RswCell
end
end

section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCellInv

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

theorem mk_inv_mul' {P : Subgroup G} {p : G} (hp : p ∈ P) (g : G) :
    (QuotientGroup.mk (p * g)⁻¹ : G ⧸ P) = QuotientGroup.mk g⁻¹ := by
  rw [QuotientGroup.eq]
  simpa using hp

theorem mk_inv_rp' {P : Subgroup G} (q : G ⧸ P) : (QuotientGroup.mk (rp q)⁻¹ : G ⧸ P) = q := by
  simp [rp]

theorem rp_mk_inv {P : Subgroup G} (g : G) :
    ∃ p ∈ P, rp (QuotientGroup.mk g⁻¹ : G ⧸ P) = p * g := by
  have hmem : rp (QuotientGroup.mk g⁻¹ : G ⧸ P) * g⁻¹ ∈ P := by
    have := mk_inv_rp' (QuotientGroup.mk g⁻¹ : G ⧸ P)
    rw [QuotientGroup.eq] at this
    simpa using this
  exact ⟨_, hmem, by simp⟩

theorem mk_inv_rp_mul {P : Subgroup G} (q : G ⧸ P) (x : G) :
    (QuotientGroup.mk (rp q * x)⁻¹ : G ⧸ P) = x⁻¹ • q := by
  conv_rhs => rw [← mk_inv_rp' q]
  rw [mul_inv_rev]
  rfl

theorem density_rp {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} (S : Setup P h mu) (x g : G) :
    h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P) * x) / h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) =
      h (g * x) / h g := by
  obtain ⟨p, hp, e⟩ := rp_mk_inv (P := P) g
  rw [e]
  have h1 := (S.pos (p * g)).ne'
  have h2 := (S.pos g).ne'
  rw [div_eq_div_iff h1 h2]
  have := S.law p hp g (g * x)
  rw [mul_assoc]
  linarith

theorem sec_translate {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} [ContinuousMul G] (S : Setup P h mu)
    {f : G → ℂ} (hf : Sec P h f) (x : G) : Sec P h (fun g => f (g * x)) := by
  refine ⟨hf.1.comp (continuous_mul_const x), fun p hp g => ?_⟩
  have h1 := hf.2 p hp (g * x)
  have h2 : ((h (p * g) : ℂ)) * h (g * x) = h g * h (p * (g * x)) := by
    exact_mod_cast S.law p hp g (g * x)
  have h3 : (h (g * x) : ℂ) ≠ 0 := by exact_mod_cast (S.pos _).ne'
  apply mul_right_cancel₀ h3
  show f (p * g * x) * (h g : ℂ) * (h (g * x) : ℂ) = f (g * x) * (h (p * g) : ℂ) * (h (g * x) : ℂ)
  rw [mul_assoc p g x]
  linear_combination (h g : ℂ) * h1 - f (g * x) * h2

variable [IsTopologicalGroup G]

theorem sec_of_real {P : Subgroup G} {h : G → ℝ} (hc : Continuous h) {F : G ⧸ P → ℝ} (hF : Continuous F) :
    Sec P h (fun g => ((F (QuotientGroup.mk g⁻¹) : ℝ) : ℂ) * (h g : ℂ)) := by
  refine ⟨?_, fun p hp g => ?_⟩
  · have : Continuous fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P) :=
      QuotientGroup.continuous_mk.comp continuous_inv
    exact (Complex.continuous_ofReal.comp (hF.comp this)).mul (Complex.continuous_ofReal.comp hc)
  · simp only [mk_inv_mul' hp]
    ring

theorem continuous_density {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} (S : Setup P h mu) (x : G) :
    Continuous fun q : G ⧸ P => h (rp q * x) / h (rp q) := by
  have hq : IsQuotientMap fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P) :=
    (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.comp (Homeomorph.inv G).isQuotientMap
  rw [hq.continuous_iff]
  have : ((fun q : G ⧸ P => h (rp q * x) / h (rp q)) ∘ fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P)) =
      fun g => h (g * x) / h g := by
    funext g
    exact density_rp S x g
  rw [this]
  exact (S.cont.comp (continuous_mul_const x)).div S.cont fun g => (S.pos g).ne'

theorem continuous_smul_quot {P : Subgroup G} (x : G) : Continuous fun q : G ⧸ P => x • q := by
  rw [(QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_const_mul x)

theorem compact_quot' {P : Subgroup G}
    (hco : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ P, ∃ c ∈ C, g = q * c) : CompactSpace (G ⧸ P) := by
  obtain ⟨C, hC, hcov⟩ := hco
  have hK : IsCompact ((fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P)) '' C) :=
    hC.image (QuotientGroup.continuous_mk.comp continuous_inv)
  refine ⟨?_⟩
  convert hK using 1
  symm
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨q, hq, c, hc, hqc⟩ := hcov y⁻¹
  refine ⟨c, hc, ?_⟩
  have : y = (q * c)⁻¹ := by rw [← hqc, inv_inv]
  rw [this, QuotientGroup.eq]
  simpa using hq

theorem integral_translate {P : Subgroup G} [MeasurableSpace (G ⧸ P)] {h : G → ℝ} {mu : (G → ℂ) → ℂ}
    (S : Setup P h mu) {ν : Measure (G ⧸ P)} (hR : Repr P h mu ν) {x : G} (hx : Inv P h mu x)
    {F : G ⧸ P → ℝ} (hF : Continuous F) :
    ∫ q, h (rp q * x) / h (rp q) * F (x⁻¹ • q) ∂ν = ∫ q, F q ∂ν := by
  have hs := sec_of_real (P := P) S.cont hF
  have h1 := (hR.2 _ hs).2
  have h2 := (hR.2 _ (sec_translate S hs x)).2
  have h3 := hx _ hs
  rw [h1, h2] at h3
  have e1 : ∀ q : G ⧸ P, (((F (QuotientGroup.mk (rp q)⁻¹) : ℝ) : ℂ) * (h (rp q) : ℂ)) / (h (rp q) : ℂ) =
      ((F q : ℝ) : ℂ) := fun q => by
    have : (h (rp q) : ℂ) ≠ 0 := by exact_mod_cast (S.pos _).ne'
    rw [mk_inv_rp', mul_div_cancel_right₀ _ this]
  have e2 : ∀ q : G ⧸ P, (((F (QuotientGroup.mk (rp q * x)⁻¹) : ℝ) : ℂ) * (h (rp q * x) : ℂ)) / (h (rp q) : ℂ) =
      ((h (rp q * x) / h (rp q) * F (x⁻¹ • q) : ℝ) : ℂ) := fun q => by
    rw [mk_inv_rp_mul]
    push_cast
    ring
  simp only [e1, e2] at h3
  rw [integral_complex_ofReal, integral_complex_ofReal] at h3
  exact_mod_cast h3

theorem inv_measure [T2Space G] [SecondCountableTopology G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)]
    [BorelSpace (G ⧸ P)] (h : G → ℝ) (mu : (G → ℂ) → ℂ) (S : Setup P h mu) (ν : Measure (G ⧸ P))
    (hR : Repr P h mu ν) (x : G) (hx : Inv P h mu x) :
    (ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map (fun q => x⁻¹ • q) = ν := by
  have : IsClosed (P : Set G) := S.closed
  have : CompactSpace (G ⧸ P) := compact_quot' S.cocpt
  have : IsFiniteMeasure ν := hR.1
  have hj := continuous_density S x
  have hsm := continuous_smul_quot (P := P) x⁻¹
  have hjm : Measurable fun q : G ⧸ P => ENNReal.ofReal (h (rp q * x) / h (rp q)) :=
    ENNReal.measurable_ofReal.comp hj.measurable
  have hjnn : ∀ q : G ⧸ P, 0 ≤ h (rp q * x) / h (rp q) := fun q => (div_pos (S.pos _) (S.pos _)).le
  have hfin : IsFiniteMeasure (ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))) :=
    isFiniteMeasure_withDensity_ofReal
      (hj.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).2
  have hfin' : IsFiniteMeasure
      ((ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map (fun q => x⁻¹ • q)) :=
    Measure.isFiniteMeasure_map _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hsm.aemeasurable f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hjm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have := integral_translate S hR hx f.continuous
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [ENNReal.toReal_ofReal (hjnn q), smul_eq_mul]

theorem invM : InvM := by
  intro G _ _ _ _ _ _ P _ _ h mu S ν hR x hx
  refine ⟨continuous_density S x, fun F hF => ?_⟩
  have hsm := continuous_smul_quot (P := P) x⁻¹
  have hjm : Measurable fun q : G ⧸ P => ENNReal.ofReal (h (rp q * x) / h (rp q)) :=
    ENNReal.measurable_ofReal.comp (continuous_density S x).measurable
  have key : ∫⁻ q, F q ∂((ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map
      (fun q => x⁻¹ • q)) = ∫⁻ q, F q ∂ν := by rw [inv_measure P h mu S ν hR x hx]
  rw [lintegral_map hF hsm.measurable,
    lintegral_withDensity_eq_lintegral_mul ν hjm
      (show Measurable fun a => F (x⁻¹ • a) from hF.comp hsm.measurable)] at key
  rw [← key]
  refine lintegral_congr fun q => ?_
  simp only [Pi.mul_apply, mul_comm]

end GlobalTheory.CompanionTheory.RswCellInv

end
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem hs_eq_frobenius_sq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs A = ‖A‖ ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
  rfl

theorem hs_le_commutator {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ)
    (h : ∀ A : Matrix (Fin m) (Fin m) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Matrix (Fin m) (Fin m) ℂ, A *ᵥ v = 0 →
      Formalism.REAL.hs A ≤ c * Formalism.REAL.hs (A * X - X * A) := by
  let Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) :=
    { toFun := fun A => (A * X - X * A, A *ᵥ v)
      map_add' := fun A B => by
        ext1
        · simp only [Prod.fst_add, add_mul, mul_add]; abel
        · simp only [Prod.snd_add, Matrix.add_mulVec]
      map_smul' := fun a A => by
        ext1
        · simp [smul_sub]
        · simp [Matrix.smul_mulVec] }
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    have h1 : A * X - X * A = 0 := congrArg Prod.fst hA
    have h2 : A *ᵥ v = 0 := congrArg Prod.snd hA
    exact h A (sub_eq_zero.mp h1) h2
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith Φ hker
  refine ⟨(K : ℝ) ^ 2, by positivity, fun A hA => ?_⟩
  have hle : ‖A‖ ≤ K * ‖A * X - X * A‖ := by
    have h3 := hanti.le_mul_dist A 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h3
    have h4 : ‖Φ A‖ = ‖A * X - X * A‖ := by
      change ‖((A * X - X * A, A *ᵥ v) : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ))‖ = _
      rw [hA, Prod.norm_def]
      simp
    rwa [h4] at h3
  rw [hs_eq_frobenius_sq, hs_eq_frobenius_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

end GlobalTheory.CompanionTheory.RgHeFrame
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_coset_reps_open_in_compact : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (A L : AddSubgroup X), IsCompact (A : Set X) → IsOpen (L : Set X) → L ≤ A → ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_finite_coset_representatives : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main | exact GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main | (intros; apply GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main <;> assumption)
end

section

open MeasureTheory
open scoped NNReal ENNReal

theorem _root_.GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q), IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | exact GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | (intros; apply GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements <;> assumption)
end
