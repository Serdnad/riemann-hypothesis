module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
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
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotConj :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotConj := by
  intro hC hI G _ _ _ _ _ _ _ _ μG hμ H H' y hH hc hy μ μ' h1 h2 hm F hF hFH
  have hy' : ∀ z, z ∈ H' ↔ y * z * y⁻¹ ∈ H := fun z => by rw [hy]; simp [mul_assoc]
  have hH' : IsClosed (H' : Set G) := by
    have : (H' : Set G) = (fun z => y * z * y⁻¹) ⁻¹' H := Set.ext hy'
    rw [this]
    exact hH.preimage (by fun_prop)
  have hc' : ∀ a ∈ H', ∀ b ∈ H', Commute a b := fun a ha b hb => by
    have := (hc _ ((hy' a).1 ha) _ ((hy' b).1 hb)).eq
    have h : y * a * b = y * b * a := by simpa [← mul_assoc] using this
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  obtain ⟨s1, i1, -⟩ := hC G H hH hc μ h1
  obtain ⟨s2, i2, -⟩ := hC G H' hH' hc' μ' h2
  have key : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h : H, f (y⁻¹ * h * y) ∂μ = ∫⁻ h : H', f h ∂μ' := fun f hf => by
    rw [← lintegral_map hf (g := fun x : H => y⁻¹ * (x : G) * y) (by fun_prop), hm,
      lintegral_map hf (g := fun x : H' => (x : G)) measurable_subtype_coe]
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H' μ' fun g => ρ (y * g) := ⟨hρ.1.comp (measurable_const_mul y), fun g => by
      rw [← key (fun z => ρ (y * (z * g))) (hρ.1.comp (by fun_prop)), ← hρ.2 (y * g)]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [hI G μG hμ H μ s1 i1 F hF hFH ρ hρ, hI G μG hμ H' μ' s2 i2 (fun g => F (y * g)) (hF.comp (measurable_const_mul y)) (fun h hh g => by
      rw [← hFH _ ((hy' h).1 hh) (y * g)]; simp [mul_assoc]) _ hρ']
    exact integral_mul_left_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H' μ' ρ := fun ⟨ρ, hρ⟩ => hex ⟨fun g => ρ (y⁻¹ * g), hρ.1.comp (measurable_const_mul _), fun g => by
      rw [← hρ.2 (y⁻¹ * g), ← key (fun z => ρ (z * (y⁻¹ * g))) (hρ.1.comp (by fun_prop))]
      exact lintegral_congr fun h => by simp [mul_assoc]⟩
    rw [quotIntegral, quotIntegral, dite_eq_right hex, dite_eq_right hex']
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.convTest :
    UpperTheory.V.Z.Tf.Orb.ConvTest := by
  intro G _ _ _ _ _ _ _ _ μ hμ a b a1 a2 b1 b2
  constructor
  · have h : conv μ a b = fun x => ∫ y in tsupport a, a y * b (y⁻¹ * x) ∂μ := by
      funext x
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [h]
    haveI : FirstCountableTopology G := inferInstance
    exact continuous_parametric_integral_of_continuous (by fun_prop) a2
  · refine HasCompactSupport.intro (a2.isCompact.mul b2.isCompact) fun x hx => ?_
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    by_contra hne
    exact hx ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), y⁻¹ * x, subset_tsupport _ (right_ne_zero_of_mul hne), by simp⟩
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.haarComm :
    UpperTheory.V.Z.Tf.Orb.HaarComm := by
  intro G _ _ _ _ _ _ _ _ H hH hc μ hμ
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  refine ⟨inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular μ, ⟨fun g => ?_⟩⟩
  have : (fun h : H => h * g) = fun h => g * h := funext fun h => mul_comm h g
  rw [this]
  exact map_mul_left_eq_self μ g
end

section

noncomputable section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal Pointwise

namespace UpperTheory.V.Z.Tf.Orb

private theorem unfold_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μ : Measure H} [SFinite μ] [μ.IsInvInvariant]
    {ψ ρ : G → ℝ≥0∞} (hψ : Measurable ψ) (hρ : IsQuotNormaliser H μ ρ) :
    ∫⁻ g, ρ g * ∫⁻ h : H, ψ ((h : G) * g) ∂μ ∂μG = ∫⁻ g, ψ g ∂μG := by
  have : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  have e1 : ∫⁻ g, ρ g * ∫⁻ h : H, ψ ((h : G) * g) ∂μ ∂μG
      = ∫⁻ h : H, ∫⁻ g, ρ g * ψ ((h : G) * g) ∂μG ∂μ := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul]
      exact hψ.comp (measurable_subtype_coe.mul_const g)
    · exact ((hρ.1.comp measurable_snd).mul (hψ.comp hmulH)).aemeasurable
  have e2 : ∀ h : H, ∫⁻ g, ρ g * ψ ((h : G) * g) ∂μG =
      ∫⁻ g, ψ g * ρ (((h⁻¹ : H) : G) * g) ∂μG := by
    intro h
    rw [← lintegral_mul_left_eq_self _ ((h : G)⁻¹)]
    refine lintegral_congr fun g => ?_
    rw [mul_inv_cancel_left, Subgroup.coe_inv, mul_comm]
  rw [e1, lintegral_congr e2, ← lintegral_lintegral_swap]
  · refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul, lintegral_inv_eq_self (fun h : H => ρ ((h : G) * g)), hρ.2 g, mul_one]
    exact hρ.1.comp ((measurable_subtype_coe.comp measurable_inv).mul_const g)
  · have : Measurable fun p : G × H => ((p.2⁻¹ : H) : G) * p.1 :=
      (measurable_subtype_coe.comp (measurable_snd.inv)).mul measurable_fst
    exact ((hψ.comp measurable_fst).mul (hρ.1.comp this)).aemeasurable

theorem quotMass : QuotMass := by
  intro G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv ρ hρ
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : SFinite μ := inferInstance
  haveI : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  haveI : μ.IsMulRightInvariant := by
    have h := (inferInstance : μ.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at h
  have key : ∀ C : Set G, IsCompact C →
      IsClosed {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} ∧
        ∫⁻ g in {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}, ρ g ∂μG ≠ ∞ := by
    intro C hC
    have hcl : IsClosed {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} := by
      have e : {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} = (H : Set G) * C := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe, eq_comm]
      rw [e]
      exact hH.mul_right_of_isCompact hC
    refine ⟨hcl, ?_⟩
    obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
    have hD : IsCompact (V * C) := hV.mul hC
    have hDm : MeasurableSet (V * C) := hD.isClosed.measurableSet
    have hVm : MeasurableSet ((↑) ⁻¹' V : Set H) :=
      measurable_subtype_coe hV.isClosed.measurableSet
    have hm : μ ((↑) ⁻¹' V : Set H) ≠ 0 := by
      refine (Measure.measure_pos_of_mem_nhds μ (x := 1) ?_).ne'
      exact continuous_subtype_val.continuousAt.preimage_mem_nhds hV1
    have hψ : Measurable ((V * C).indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hDm
    have hE := unfold_eq (μG := μG) hψ hρ
    rw [lintegral_indicator_one hDm] at hE
    have hlow : ∀ g ∈ {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c},
        μ ((↑) ⁻¹' V : Set H) ≤ ∫⁻ h : H, (V * C).indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μ := by
      rintro g ⟨h0, hh0, c, hc, rfl⟩
      have := lintegral_mul_right_eq_self (μ := μ)
        (fun h : H => (V * C).indicator (1 : G → ℝ≥0∞) ((h : G) * c)) ⟨h0, hh0⟩
      simp only [Subgroup.coe_mul, mul_assoc] at this
      rw [this, ← lintegral_indicator_one hVm]
      refine lintegral_mono fun h => ?_
      by_cases hh : h ∈ ((↑) ⁻¹' V : Set H)
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (Set.mul_mem_mul (show (h : G) ∈ V from hh) hc)]
        rfl
      · rw [Set.indicator_of_notMem hh]
        exact zero_le
    have hle : (∫⁻ g in {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}, ρ g ∂μG) * μ ((↑) ⁻¹' V : Set H)
        ≤ μG (V * C) := by
      rw [← hE, ← lintegral_mul_const _ hρ.1]
      refine le_trans (setLIntegral_mono' hcl.measurableSet fun g hg => ?_)
        (setLIntegral_le_lintegral _ _)
      exact mul_le_mul_right (hlow g hg) _
    intro htop
    rw [htop, ENNReal.top_mul hm] at hle
    exact hD.measure_lt_top.not_ge hle
  refine ⟨?_, key⟩
  have hloc : ∀ n, ∀ᵐ g ∂μG, g ∈ compactCovering G n → ρ g ≠ ∞ := by
    intro n
    have hC := isCompact_compactCovering G n
    have h1 := ae_lt_top hρ.1 (key _ hC).2
    rw [ae_restrict_iff' (key _ hC).1.measurableSet] at h1
    filter_upwards [h1] with g hg hgC
    exact (hg ⟨1, H.one_mem, g, hgC, (one_mul g).symm⟩).ne
  filter_upwards [ae_all_iff.2 hloc] with g hg
  obtain ⟨n, hn⟩ := exists_mem_compactCovering g
  exact hg n hn

end UpperTheory.V.Z.Tf.Orb
end
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.absComm :
    UpperTheory.V.Z.Tf.Orb.QuotFubini → UpperTheory.V.Z.Tf.Orb.QuotRight → UpperTheory.V.Z.Tf.Orb.FinPres → UpperTheory.V.Z.Tf.Orb.AbsComm := by
  intro hF hR hP G _ _ _ _ _ _ _ _ μG hμG r1 r2 θ hθ l hl hθl δ hD μ hμ hi a b a1 a2 b1 b2
  have hcl : IsClosed (twCent θ δ : Set G) :=
    isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const
  haveI : LocallyCompactSpace (twCent θ δ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (twCent θ δ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (twCent θ δ) := inferInstance
  haveI : SigmaFinite μ := inferInstance
  have hmp := hP G μG hμG θ hθ l hl hθl
  have hθθ : ∀ x, (θ ^ (l - 1)) (θ x) = x := fun x => by
    rw [← pow_succ_apply, Nat.sub_add_cancel (Nat.pos_of_ne_zero hl), hθl]; rfl
  have hθθ' : ∀ x, θ ((θ ^ (l - 1)) x) = x := fun x => by
    rw [← pow_succ_apply', Nat.sub_add_cancel (Nat.pos_of_ne_zero hl), hθl]; rfl
  have hpc : ∀ m : ℕ, Continuous (θ ^ m : Monoid.End G) := fun m => by
    induction m with
    | zero => exact continuous_id
    | succ m ih => exact (ih.comp hθ).congr fun x => (pow_succ_apply θ m x).symm
  let e : G ≃ₜ G := ⟨⟨θ, (θ ^ (l - 1) : Monoid.End G), hθθ, hθθ'⟩, hθ, hpc _⟩
  have hinv : ∀ h ∈ twCent θ δ, ∀ g, twConj θ (h * g) δ = twConj θ g δ := fun h hh g => twConj_mul_left θ δ hh g
  have hct : Continuous fun g => twConj θ g δ := (continuous_inv.mul continuous_const).mul hθ
  obtain ⟨D1, d1, e1⟩ := hD _ (a2.isCompact.mul b2.isCompact)
  obtain ⟨D2, d2, e2⟩ := hD _ (b2.isCompact.mul (a2.isCompact.image hθ))
  have k1 := hF G μG hμG _ hcl μ hμ hi (fun y g => a y * b (y⁻¹ * twConj θ g δ))
    ((a1.comp continuous_fst).mul (b1.comp (continuous_fst.inv.mul (hct.comp continuous_snd))))
    (fun y h hh g => by simp only [hinv h hh]) ⟨_, D1, a2.isCompact, d1, fun y g hne =>
      ⟨subset_tsupport _ (left_ne_zero_of_mul hne), e1 g ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), _,
        subset_tsupport _ (right_ne_zero_of_mul hne), by simp⟩⟩⟩
  have k2 := hF G μG hμG _ hcl μ hμ hi (fun y g => a y * b (twConj θ g δ * (θ y)⁻¹))
    ((a1.comp continuous_fst).mul (b1.comp ((hct.comp continuous_snd).mul (hθ.comp continuous_fst).inv)))
    (fun y h hh g => by simp only [hinv h hh]) ⟨_, D2, a2.isCompact, d2, fun y g hne =>
      ⟨subset_tsupport _ (left_ne_zero_of_mul hne), e2 g ⟨_, subset_tsupport _ (right_ne_zero_of_mul hne), θ y,
        ⟨y, subset_tsupport _ (left_ne_zero_of_mul hne), rfl⟩, by simp⟩⟩⟩
  have k3 : ∀ x, conv μG b (fun x => a ((θ ^ (l - 1)) x)) x = ∫ y, a y * b (x * (θ y)⁻¹) ∂μG := fun x => by
    have s1 := hmp.integral_comp e.measurableEmbedding fun w => a ((θ ^ (l - 1)) w) * b (x * w⁻¹)
    simp only [hθθ] at s1
    rw [s1, ← integral_inv_eq_self, ← integral_mul_left_eq_self _ x⁻¹, conv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [mul_comm]
  rw [twOrbIntegralC, twOrbIntegralC]
  simp only [k3]
  rw [k2]
  refine k1.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))
  have k4 := hR G μG hμG r1 _ μ inferInstance hi (fun g => a y * b (y⁻¹ * twConj θ g δ))
    (continuous_const.mul (b1.comp (continuous_const.mul hct))).measurable (fun h hh g => by simp only [hinv h hh]) y⁻¹
  refine k4.symm.trans ?_
  congr 1
  funext g
  simp [twConj, mul_assoc]
end

section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.twCent :
    UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCent := by
  intro hE hG hC k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ _ n δ hδ
  have := (hG E n).2.2.1
  have hc := ((hE k E).2.2 n).2 σ
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨isClosed_eq (f := fun g : GL (Fin n) E => g⁻¹ * δ * sigmaGL σ g) ((continuous_inv.mul continuous_const).mul hc)
    continuous_const, fun a ha b hb => ?_⟩
  have h1 := congrArg Units.val (twCent_commute_twNorm _ hp δ ha)
  have h2 := congrArg Units.val (twCent_commute_twNorm _ hp δ hb)
  exact Units.ext (hC E n _ a.val b.val hδ h1 h2)
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbFin :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.OrbProper → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.NormEx → UpperTheory.V.Z.Tf.Orb.QuotInt → UpperTheory.V.Z.Tf.Orb.QuotPos → UpperTheory.V.Z.Tf.Orb.TwOrbFin := by
  intro hG hX hC hP hH hN hI hQ k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE φ hφ hc δ hδ μ hμ
  obtain ⟨g1, g2, g3, g4, -⟩ := hG E n
  obtain ⟨c1, c2⟩ := hC k E σ hσ n δ hδ
  obtain ⟨-, i2, i3⟩ := hH _ _ c1 c2 μ hμ
  have hs := ((hX k E).2.2 n).2 σ
  obtain ⟨ρ, hρ, -⟩ := hN _ g4 _ c1 μ hμ i3
  have hF : Continuous fun g => φ (twConj (sigmaGL σ) g δ) := hφ.comp ((continuous_inv.mul continuous_const).mul hs)
  have hinv : ∀ h ∈ PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ, ∀ g, φ (twConj (sigmaGL σ) (h * g) δ) = φ (twConj (sigmaGL σ) g δ) :=
    fun h hh g => by rw [twConj_mul_left _ _ hh]
  have hM : CptMod (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ) fun g => φ (twConj (sigmaGL σ) g δ) := by
    obtain ⟨D, hD, h⟩ := hP k E σ hσ n δ hδ _ hc
    exact ⟨D, hD, fun g hg => h g (subset_tsupport _ hg)⟩
  exact ⟨⟨ρ, hρ⟩, hI _ μE hμE _ c1 μ hμ i2 _ hF hinv hM,
    fun p q => hQ _ μE hμE _ c1 μ hμ i2 ⟨ρ, hρ⟩ _ hF hinv hM (fun g => p _) q⟩
end

section

open MeasureTheory PositivityTheory.Rg.Tf.Loc in
theorem UpperTheory.V.Z.Tf.Orb.quotRight :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotRight := by
  intro hI G _ _ _ _ _ _ _ _ μG hμG hR H μ hs hinv F hF hFH y
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H μ (fun g => ρ (g * y)) := by
      refine ⟨hρ.1.comp (measurable_mul_const y), fun g => ?_⟩
      simpa only [mul_assoc] using hρ.2 (g * y)
    rw [hI G μG hμG H μ hs hinv F hF hFH ρ hρ,
      hI G μG hμG H μ hs hinv (fun g => F (g * y)) (hF.comp (measurable_mul_const y))
        (fun h hh g => by rw [mul_assoc, hFH h hh]) _ hρ']
    exact integral_mul_right_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · simp only [quotIntegral, dif_neg hex]
end

section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.normEx :
    UpperTheory.V.Z.Tf.Orb.NormEx := by
  classical
  intro G _ _ _ _ _ _ _ _ ⟨K, hKo, hKc⟩ H hH μ hμ hr
  let r : G → G := fun g => (DoubleCoset.mk H K g).out
  have hr1 : ∀ g, ∃ h ∈ H, ∃ k ∈ K, r g = h * g * k := fun g => by
    obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul H K g
    exact ⟨h, hh, k, hk, e⟩
  have hr2 : ∀ h ∈ H, ∀ g, ∀ k ∈ K, r (h * g * k) = r g := fun h hh g k hk =>
    congrArg Quotient.out ((@DoubleCoset.eq _ _ H K _ _).2 ⟨h, hh, k, hk, rfl⟩).symm
  let A : G → Set H := fun x => {h | x⁻¹ * h * x ∈ K}
  have hAo : ∀ x, IsOpen (A x) := fun x => hKo.preimage (by fun_prop)
  have hAc : ∀ x, IsCompact (A x) := fun x => by
    have h1 : IsCompact ((fun z => x⁻¹ * z * x) ⁻¹' (K : Set G)) :=
      ((Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)).isCompact_preimage.2 hKc
    exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1
  have h0 : ∀ x, μ (A x) ≠ 0 := fun x => ((hAo x).measure_pos μ ⟨1, by simp [A, K.one_mem]⟩).ne'
  have ht : ∀ x, μ (A x) ≠ ∞ := fun x => (hAc x).measure_lt_top.ne
  let ρ : G → ℝ≥0∞ := fun g => if (r g)⁻¹ * g ∈ K then (μ (A (r g)))⁻¹ else 0
  have hk : ∀ g, ∀ k ∈ K, ρ (g * k) = ρ g := fun g k hk => by
    have : r (g * k) = r g := by simpa using hr2 1 H.one_mem g k hk
    simp only [ρ, this, ← mul_assoc, K.mul_mem_cancel_right hk]
  have hlc : IsLocallyConstant ρ := (IsLocallyConstant.iff_exists_open ρ).2 fun g =>
    ⟨(fun z => g⁻¹ * z) ⁻¹' K, hKo.preimage (by fun_prop), by simp [K.one_mem], fun z hz => by
      rw [← hk g _ hz, mul_inv_cancel_left]⟩
  refine ⟨ρ, ⟨hlc.continuous.measurable, fun g => ?_⟩, fun g => ?_⟩
  · obtain ⟨h₀, hh, k, hk', e⟩ := hr1 g
    have e1 : ∀ h : H, ρ (h * g) = (A (r g)).indicator (fun _ => (μ (A (r g)))⁻¹) (h * (⟨h₀, hh⟩ : H)⁻¹) := fun h => by
      have h1 : r (h * g) = r g := by simpa using hr2 h h.2 g 1 K.one_mem
      have h2 : (r g)⁻¹ * (h * g) ∈ K ↔ h * (⟨h₀, hh⟩ : H)⁻¹ ∈ A (r g) := by
        rw [← K.mul_mem_cancel_right hk']
        change _ ↔ (r g)⁻¹ * ((h : G) * h₀⁻¹) * r g ∈ K
        have : (r g)⁻¹ * ((h : G) * h₀⁻¹) * r g = (r g)⁻¹ * (h * g) * k := by
          nth_rewrite 2 [e]
          group
        rw [this]
      simp only [ρ, h1, Set.indicator, h2]
    rw [lintegral_congr e1, lintegral_mul_right_eq_self, lintegral_indicator_const (hAo _).measurableSet,
      ENNReal.inv_mul_cancel (h0 _) (ht _)]
  · simp only [ρ]
    split_ifs
    · exact ENNReal.inv_ne_top.2 (h0 _)
    · exact ENNReal.zero_ne_top
end

section

noncomputable section

open Module

namespace UpperTheory.V.Z.Tf.Orb

private theorem endComm {L V : Type} [Field L] [IsAlgClosed L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (f x y : Module.End L V) (hf : f.charpoly.Separable) (hx : Commute x f) (hy : Commute y f) : Commute x y := by
  have key : ∀ μ : L, ∀ v ∈ f.maxGenEigenspace μ, (x * y) v = (y * x) v := by
    intro μ v hv
    have h1 : finrank L (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hf μ
    obtain ⟨w, hw⟩ := finrank_le_one_iff.mp h1
    have mx := Module.End.mapsTo_maxGenEigenspace_of_comm hx.symm μ
    have my := Module.End.mapsTo_maxGenEigenspace_of_comm hy.symm μ
    obtain ⟨c, hc⟩ := hw ⟨v, hv⟩
    obtain ⟨a, ha⟩ := hw ⟨x w, mx w.2⟩
    obtain ⟨b, hb⟩ := hw ⟨y w, my w.2⟩
    have hc' : v = c • (w : V) := by simpa using (congrArg Subtype.val hc).symm
    have ha' : x w = a • (w : V) := by simpa using (congrArg Subtype.val ha).symm
    have hb' : y w = b • (w : V) := by simpa using (congrArg Subtype.val hb).symm
    simp only [hc', Module.End.mul_apply, map_smul, ha', hb', smul_smul, mul_comm a b]
  have htop := Module.End.iSup_maxGenEigenspace_eq_top f
  have : (⊤ : Submodule L V) ≤ LinearMap.eqLocus (x * y) (y * x) := by
    rw [← htop]
    exact iSup_le fun μ v hv => key μ v hv
  exact LinearMap.ext fun v => this Submodule.mem_top

theorem centComm : CentComm := by
  intro K _ n A X Y hA hX hY
  let L := AlgebraicClosure K
  let φ : Matrix (Fin n) (Fin n) K →+* Module.End L (Fin n → L) :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).toRingEquiv.toRingHom.comp (algebraMap K L).mapMatrix
  have hφ : Function.Injective φ :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).injective.comp
      (Matrix.map_injective (algebraMap K L).injective)
  have hch : (φ A).charpoly = A.charpoly.map (algebraMap K L) := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_toLin']
    rfl
  have h := endComm (φ A) (φ X) (φ Y) (hch ▸ hA.map) (hX.map φ) (hY.map φ)
  apply hφ
  rw [map_mul, map_mul]
  exact h

end UpperTheory.V.Z.Tf.Orb
end
end
