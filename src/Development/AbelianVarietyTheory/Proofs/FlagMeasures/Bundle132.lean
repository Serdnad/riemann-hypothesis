module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle007
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle028
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledIntegralOfDensityOne
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory Filter Set Formalism.MainNotions.S GlobalTheory.RightRegFund
open scoped ENNReal Pointwise

namespace GlobalTheory.LocalL2Isometry

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ]
  {D : Set G} {r : G → G}

private lemma card_le_of_translates_mem_mul_inv_tsum_indicator {C : Set G} (S : Finset Γ)
    (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) (x : G) :
    ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) ≤ S.card := by
  classical
  by_cases h : ∃ γ₀ : Γ, (γ₀ : G) * x ∈ C
  · obtain ⟨γ₀, h₀⟩ := h
    have hsupp : ∀ γ ∉ S.image (· * γ₀),
        C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) = 0 := by
      intro γ hγ
      by_contra hne
      have hγC : (γ : G) * x ∈ C := by
        by_contra hn
        exact hne (Set.indicator_of_notMem hn _)
      apply hγ
      refine Finset.mem_image.2 ⟨γ * γ₀⁻¹, hS _ ?_, by simp⟩
      refine Set.mem_mul.2 ⟨(γ : G) * x, hγC, ((γ₀ : G) * x)⁻¹, by simpa using h₀, ?_⟩
      simp [mul_assoc]
    rw [tsum_eq_sum hsupp]
    calc ∑ γ ∈ S.image (· * γ₀), C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)
        ≤ ∑ _γ ∈ S.image (· * γ₀), (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun γ _ => ?_
          by_cases hm : (γ : G) * x ∈ C <;> simp [hm]
      _ = ((S.image (· * γ₀)).card : ℝ≥0∞) := by simp
      _ ≤ S.card := by exact_mod_cast Finset.card_image_le
  · push_neg at h
    simp [h]

theorem lintegral_rep_le (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hC : MeasurableSet C)
    (S : Finset Γ) (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y in C, φ (r y) ∂μ ≤ S.card * ∫⁻ x in D, φ x ∂μ := by
  classical
  have hfix : ∀ᵐ x ∂μ.restrict D, ∀ γ : Γ, r ((γ : G) * x) = x := by
    filter_upwards [ae_restrict_of_ae (ae_good hD), ae_restrict_mem hDm] with x hx hxD γ
    rw [rep_mul hr hx γ]
    simpa using rep_eq hr hx (γ := 1) (by simpa using hxD)
  have hmeas : ∀ γ : Γ, AEMeasurable
      (fun x => C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x) (μ.restrict D) := fun γ =>
    (((measurable_const.indicator hC).comp (measurable_const_mul (γ : G))).mul hφ).aemeasurable
  calc ∫⁻ y in C, φ (r y) ∂μ = ∫⁻ y, C.indicator (fun y => φ (r y)) y ∂μ :=
        (lintegral_indicator hC _).symm
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun y => φ (r y)) (γ • x) ∂μ :=
        hD.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ x in D, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ := by
        refine tsum_congr fun γ => lintegral_congr_ae ?_
        filter_upwards [hfix] with x hx
        change C.indicator (fun y => φ (r y)) ((γ : G) * x) = _
        by_cases hm : (γ : G) * x ∈ C
        · simp [hm, hx γ]
        · simp [hm]
    _ = ∫⁻ x in D, ∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x) * φ x ∂μ :=
        (lintegral_tsum hmeas).symm
    _ = ∫⁻ x in D, (∑' γ : Γ, C.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * x)) * φ x ∂μ :=
        lintegral_congr fun x => ENNReal.tsum_mul_right
    _ ≤ ∫⁻ x in D, (S.card : ℝ≥0∞) * φ x ∂μ :=
        lintegral_mono fun x => by gcongr; exact card_le_of_translates_mem_mul_inv_tsum_indicator S hS x
    _ = S.card * ∫⁻ x in D, φ x ∂μ := lintegral_const_mul _ hφ

theorem integrableOn_rep (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {C : Set G} (hC : MeasurableSet C)
    (hCf : μ C ≠ ∞) (S : Finset Γ) (hS : ∀ γ : Γ, (γ : G) ∈ C * C⁻¹ → γ ∈ S) :
    ∃ M : ℝ, ∀ F : Lp ℂ 2 (μ.restrict D), IntegrableOn (fun y => F (r y)) C μ ∧
      ∫ y in C, ‖F (r y)‖ ∂μ ≤ M * ‖F‖ := by
  refine ⟨((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ)).toReal, fun F => ?_⟩
  haveI : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.2 hCf
  have hFm : Measurable (F : G → ℂ) := (Lp.stronglyMeasurable F).measurable
  have hgm : AEStronglyMeasurable (fun y => F (r y)) (μ.restrict C) :=
    (aestronglyMeasurable_comp_rep hD hDm hr (Lp.stronglyMeasurable F)).restrict
  have hcard : (S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.natCast_ne_top _)
  have hCr : μ C ^ (1 / 2 : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCf
  have h2 : eLpNorm (fun y => F (r y)) 2 (μ.restrict C) ≤
      (S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm F 2 (μ.restrict D) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hgm,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
        (Lp.stronglyMeasurable F).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    gcongr
    exact lintegral_rep_le hD hDm hr hC S hS (φ := fun x => ‖F x‖ₑ ^ (2 : ℝ)) (by fun_prop)
  have h1 : eLpNorm (fun y => F (r y)) 1 (μ.restrict C) ≤
      eLpNorm (fun y => F (r y)) 2 (μ.restrict C) * μ C ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hgm
    rw [Measure.restrict_apply_univ] at h
    convert h using 3
    norm_num
  have hL2 : MemLp (fun y => F (r y)) 2 (μ.restrict C) :=
    h2.trans_lt (ENNReal.mul_lt_top hcard.lt_top (Lp.eLpNorm_lt_top F))
  refine ⟨hL2.integrable (by norm_num), ?_⟩
  calc ∫ y in C, ‖F (r y)‖ ∂μ = (eLpNorm (fun y => F (r y)) 1 (μ.restrict C)).toReal := by
        rw [integral_norm_eq_lintegral_enorm hgm, eLpNorm_one_eq_lintegral_enorm hgm]
    _ ≤ ((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm F 2 (μ.restrict D) * μ C ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hcard (Lp.eLpNorm_ne_top F)) hCr)
          (h1.trans (by gcongr))
    _ = ((S.card : ℝ≥0∞) ^ (1 / 2 : ℝ) * μ C ^ (1 / 2 : ℝ)).toReal * ‖F‖ := by
        rw [Lp.norm_def, ← ENNReal.toReal_mul, mul_right_comm]

theorem ext_integrableOn : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ,
    ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧
      ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  intro B C hC
  obtain ⟨Γ, hΓ, hΓc, hfin, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain B.I
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology B.I
  haveI := hΓc
  haveI := hT2
  haveI := hsc
  have hD := hfd B.μf B.fund B.fund_spec
  haveI : (B.I.muA B.μf).IsMulLeftInvariant := ⟨(GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf).1⟩
  haveI : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  have hDm : MeasurableSet B.fund := B.fund_spec.1
  have hr : ∀ y, ∃ γ : Γ, B.I.rep B.fund y = (γ : B.I.GA) * y ∧ B.I.rep B.fund y ∈ B.fund := by
    intro y
    have h := B.fund_spec.2.1 y
    refine ⟨⟨h.choose, ?_⟩, ?_, ?_⟩
    · rw [← SetLike.mem_coe, hΓ]
      exact h.choose_spec.1
    · rw [AutInst.rep, dite_eq_left h]
    · rw [AutInst.rep, dite_eq_left h]
      exact h.choose_spec.2
  have hK : IsCompact (C * C⁻¹) := hC.mul hC.inv
  have hSfin : {γ : Γ | (γ : B.I.GA) ∈ C * C⁻¹}.Finite :=
    ((hfin _ hK).preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨hγ, by
      rw [← hΓ]
      exact γ.2⟩
  obtain ⟨M, hM⟩ := integrableOn_rep hD hDm hr hC.measurableSet hC.measure_lt_top.ne
    hSfin.toFinset fun γ hγ => hSfin.mem_toFinset.2 hγ
  exact ⟨M, fun F => hM F⟩

end GlobalTheory.LocalL2Isometry
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

noncomputable section

namespace GlobalTheory.AdelicLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem incl_mem_lamAf (L : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ L) :
    (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem exists_approx (L : Submodule (𝓞 E) (Fin n → E)) (g : ℕ) (hg : 1 ≤ g)
    (y : Fin n → E ⊗[F] Af F) (hy : y ∈ lamAf (F := F) L) :
    ∃ x ∈ L, ∃ z ∈ lamAf (F := F) L,
      y = (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + (g : E ⊗[F] Af F) • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, x.2, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, z, hz, rfl⟩ := ha
    obtain ⟨x', hx', z', hz', rfl⟩ := hb
    refine ⟨x + x', add_mem hx hx', z + z', add_mem hz hz', ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _)]
    ring
  | smul s a _ ha =>
    obtain ⟨x, hx, z, hz, rfl⟩ := ha
    obtain ⟨r, hr, w, hw, e⟩ := Formalism.UG.P.csSpan_approx (F := F) (E := E) Formalism.UG.P.csGlob_intAdApprox
      (g : 𝓞 F) (Nat.cast_ne_zero.2 (by omega)) s.2
    rw [GlobalTheory.AutInhab.levelafC_natCast] at e
    refine ⟨(⟨r, hr⟩ : 𝓞 E) • x, L.smul_mem _ hx,
      (⟨w, hw⟩ : IntAf F E) • (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + s • z,
      add_mem (Submodule.smul_mem _ _ (incl_mem_lamAf L hx)) (Submodule.smul_mem _ _ hz), ?_⟩
    funext i
    show (s : E ⊗[F] Af F) * (Formalism.UG.inclE (F := F) (Af F) (x i) + (g : E ⊗[F] Af F) * z i) =
      Formalism.UG.inclE (F := F) (Af F) (r * x i) + (g : E ⊗[F] Af F) *
        (w * Formalism.UG.inclE (F := F) (Af F) (x i) + (s : E ⊗[F] Af F) * z i)
    rw [map_mul]
    linear_combination Formalism.UG.inclE (F := F) (Af F) (x i) * e

theorem incl_mem_iff (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ lamAf (F := F) L ↔ x ∈ L := by
  refine ⟨fun h => ?_, incl_mem_lamAf L⟩
  rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) L (Module.Finite.iff_fg.2 hfg) hspan]
  show ((1⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.UG.latS (F := F) (Af F) (IntAf F E) L
  rw [inv_one, Units.val_one, one_mulVec]
  refine Submodule.span_mono ?_ h
  rintro _ ⟨y, rfl⟩
  exact ⟨y, y.2, rfl⟩

theorem span_lamAf (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span (E ⊗[F] Af F) (lamAf (F := F) L : Set (Fin n → E ⊗[F] Af F)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨m, hm, hy⟩ := GlobalTheory.AutInhab.lamAf_absorbs (F := F) L hspan y
  obtain ⟨u, hu⟩ := GlobalTheory.AutInhab.isUnit_natCast (F := F) (E := E) m hm
  have : y = ((u⁻¹ : (E ⊗[F] Af F)ˣ) : E ⊗[F] Af F) • ((m : E ⊗[F] Af F) • y) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

theorem adelicLattice_spec : ∀ (I : AutInst) (g : ℕ), 1 ≤ g → (∀ y ∈ I.Lf, ∃ x ∈ I.L, ∃ z ∈ I.Lf, y = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) + (g : (I.E ⊗[I.F] Af I.F)) • z) ∧ (∀ x : Fin I.n → I.E, (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) ∈ I.Lf ↔ x ∈ I.L) ∧ Submodule.span (I.E ⊗[I.F] Af I.F) (I.Lf : Set (Fin I.n → (I.E ⊗[I.F] Af I.F))) = ⊤ ∧ I.Lf.FG ∧ ∀ y : Fin I.n → (I.E ⊗[I.F] Af I.F), ∃ m : ℕ, 1 ≤ m ∧ (m : (I.E ⊗[I.F] Af I.F)) • y ∈ I.Lf :=
  fun I g hg => ⟨exists_approx I.L g hg, incl_mem_iff I.L I.L_fg I.L_span, span_lamAf I.L I.L_span,
    GlobalTheory.AutInhab.lamAf_fg I.L I.L_fg, GlobalTheory.AutInhab.lamAf_absorbs I.L I.L_span⟩

end GlobalTheory.AdelicLattice
end
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.UnipQuot

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_domain (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ C ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ D := by
  obtain ⟨ψ, hψm, hψi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated G
  have he := measurableEmbedding_embeddingReal (ℕ → Bool)
  set φ : G → ℝ := fun x => embeddingReal (ℕ → Bool) (ψ x) with hφ
  have hφm : Measurable φ := he.measurable.comp hψm
  have hφi : Function.Injective φ := he.injective.comp hψi
  have hCm : MeasurableSet C := hC.measurableSet
  refine ⟨C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)}, ?_, Set.inter_subset_left, ?_⟩
  · refine hCm.inter (MeasurableSet.iInter fun γ => ?_)
    have h1 : MeasurableSet {y : G | (γ : G) * y ∈ C} := (measurable_const_mul (γ : G)) hCm
    have h2 : MeasurableSet {y : G | φ y ≤ φ ((γ : G) * y)} :=
      measurableSet_le hφm (hφm.comp (measurable_const_mul (γ : G)))
    have : {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} =
        {y : G | (γ : G) * y ∈ C}ᶜ ∪ {y : G | φ y ≤ φ ((γ : G) * y)} := by
      ext y; simp [imp_iff_not_or]
    rw [this]; exact h1.compl.union h2
  · intro x
    have hK : IsCompact ((fun y => y * x⁻¹) '' C) := hC.image (continuous_mul_const _)
    have hF := hfin _ hK
    obtain ⟨γ₀, hγ₀, hγ₀C⟩ := hcov x
    have hne : ((fun y => y * x⁻¹) '' C ∩ (Γ : Set G)).Nonempty :=
      ⟨γ₀, ⟨γ₀ * x, hγ₀C, by simp⟩, hγ₀⟩
    obtain ⟨γ, ⟨⟨y, hy, hyγ⟩, hγΓ⟩, hmin⟩ := Set.exists_min_image _ (fun g => φ (g * x)) hF hne
    have hγx : γ * x ∈ C := by rw [← hyγ]; simpa using hy
    have hmem : (⟨γ, hγΓ⟩ : Γ) • x ∈
        C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} := by
      refine ⟨hγx, Set.mem_iInter.2 fun δ hδ => ?_⟩
      have hδ' : (δ : G) * (γ * x) ∈ C := hδ
      have := hmin ((δ : G) * γ) ⟨⟨_, hδ', by simp [mul_assoc]⟩, Γ.mul_mem δ.2 hγΓ⟩
      show φ (γ * x) ≤ φ ((δ : G) * (γ * x))
      simpa [mul_assoc] using this
    refine ⟨⟨γ, hγΓ⟩, hmem, fun δ hδ => ?_⟩
    have hδC : (δ : G) * x ∈ C := hδ.1
    have h1 : φ ((δ : G) * x) ≤ φ (γ * x) := by
      have := Set.mem_iInter.1 hδ.2 ⟨γ * (δ : G)⁻¹, Γ.mul_mem hγΓ (Γ.inv_mem δ.2)⟩
      have e : γ * (δ : G)⁻¹ * (δ • x) = γ * x := by
        show γ * (δ : G)⁻¹ * ((δ : G) * x) = γ * x
        simp [mul_assoc]
      simp only [Set.mem_ofPred_eq, e] at this
      exact this hγx
    have h2 : φ (γ * x) ≤ φ ((δ : G) * x) := hmin δ ⟨⟨_, hδC, by simp⟩, δ.2⟩
    exact Subtype.ext (mul_right_cancel (hφi (le_antisymm h1 h2)))

theorem exists_prob [LocallyCompactSpace G] (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) → ∀ g : G, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  obtain ⟨D, hDm, hDC, hD⟩ := exists_domain Γ hfin C hC hcov
  set μ : Measure G := Measure.haar
  have hfd : IsFundamentalDomain Γ D μ := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hfd' : ∀ g : G, IsFundamentalDomain Γ ((fun y => y * g) ⁻¹' D) μ := fun g =>
    IsFundamentalDomain.mk' ((measurable_mul_const g) hDm).nullMeasurableSet fun x => by
      have := hD (x * g)
      simpa [Subgroup.smul_def, mul_assoc] using this
  have h0 : μ D ≠ 0 := hfd.measure_ne_zero (NeZero.ne μ)
  have htop : μ D ≠ ⊤ := ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono hDC)
  have hinv : ∀ g : G, Measure.map (fun y => y * g) μ = μ := by
    intro g
    have : IsFiniteMeasureOnCompacts (Measure.map (fun y => y * g) μ) := ⟨fun K hK => by
      rw [Measure.map_apply (measurable_mul_const g) hK.measurableSet]
      exact ((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top⟩
    have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun y => y * g) μ) μ
    set c := (Measure.map (fun y => y * g) μ).haarScalarFactor μ
    have h1 : Measure.map (fun y => y * g) μ D = μ D := by
      rw [Measure.map_apply (measurable_mul_const g) hDm]
      exact (hfd' g).measure_eq hfd
    rw [h] at h1
    have h2 : (c : ENNReal) = 1 := by
      have : (c : ENNReal) * μ D = 1 * μ D := by simpa using h1
      exact (ENNReal.mul_left_inj h0 htop).1 this
    have h3 : c = 1 := by exact_mod_cast h2
    rw [h, h3, one_smul]
  refine ⟨(μ D)⁻¹ • μ.restrict D, ⟨?_⟩, ?_, ?_⟩
  · simp [ENNReal.inv_mul_cancel h0 htop]
  · have : Cᶜ ∩ D = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => h1 (hDC h2)
    rw [smul_apply, Measure.restrict_apply hC.measurableSet.compl, this]
    simp
  · intro f hf g
    rw [integral_smul_measure, integral_smul_measure]
    congr 1
    have hemb : MeasurableEmbedding (fun y : G => y * g) := measurableEmbedding_mulRight g
    have h1 := hemb.setIntegral_map (μ := μ) f ((fun y => y * g⁻¹) ⁻¹' D)
    have h2 : (fun y : G => y * g) ⁻¹' ((fun y => y * g⁻¹) ⁻¹' D) = D := by
      ext y; simp
    rw [hinv g, h2] at h1
    rw [← h1]
    exact (hfd' g⁻¹).setIntegral_eq hfd fun γ x => hf γ γ.2 x

theorem exists_prob_subgroup [LocallyCompactSpace G] (N Γ : Subgroup G) (hN : IsClosed (N : Set G))
    [Countable Γ] (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m ∈ N, ∃ γ ∈ Γ, γ ∈ N ∧ γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧ ν (N : Set G)ᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, γ ∈ N → ∀ y, f (γ * y) = f y) →
        ∀ g ∈ N, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  have hce : Topology.IsClosedEmbedding (Subtype.val : N → G) := hN.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace N := hce.locallyCompactSpace
  have : SecondCountableTopology N := hce.isEmbedding.secondCountableTopology
  have hemb : MeasurableEmbedding (Subtype.val : N → G) := hce.measurableEmbedding
  have : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ)) ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  obtain ⟨ν, hν, hνC, hνf⟩ := exists_prob (Γ.subgroupOf N) (fun K hK => by
      have := hfin _ (hK.image continuous_subtype_val)
      refine (this.preimage (f := (Subtype.val : N → G)) Subtype.val_injective.injOn).subset ?_
      rintro x ⟨hx, hx'⟩
      exact ⟨⟨x, hx, rfl⟩, hx'⟩)
    (Subtype.val ⁻¹' C) (hce.isCompact_preimage hC) (fun m => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov m m.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  refine ⟨ν.map Subtype.val, (by letI := hν; infer_instance), ?_, ?_, ?_⟩
  · rw [hemb.map_apply]; exact hνC
  · rw [hemb.map_apply]
    have : (Subtype.val : N → G) ⁻¹' (N : Set G)ᶜ = ∅ := by
      ext y; simp
    rw [this, measure_empty]
  · intro f hf g hg
    rw [hemb.integral_map, hemb.integral_map]
    exact hνf (fun y => f y) (fun γ hγ y => hf γ hγ γ.2 y) ⟨g, hg⟩

end General

theorem exists_quot_prob (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧
      ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  obtain ⟨h2, hlc, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨⟨N, hN⟩, hcl, -, -, C, hC, hCN, hcov⟩ := GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I W hW
  obtain ⟨Γ, hΓ, hΓc, hfin, -⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  have : BorelSpace I.GA := inferInstance
  have mN : ∀ x, x ∈ N ↔ x ∈ I.NA W := fun x => by rw [← hN]; rfl
  have mΓ : ∀ x, x ∈ Γ ↔ x ∈ I.GFset := fun x => by rw [← hΓ]; rfl
  obtain ⟨ν, hν, hνC, hνN, hf⟩ := exists_prob_subgroup N Γ (hN ▸ hcl) (hΓ ▸ hfin) C hC (fun m hm => by
    obtain ⟨γ, ⟨h1, h1'⟩, h3⟩ := hcov m ((mN m).1 hm)
    exact ⟨γ⁻¹, Γ.inv_mem ((mΓ γ).2 h1), N.inv_mem ((mN γ).2 h1'), h3⟩)
  refine ⟨ν, hν, ⟨inferInstance, IsProbabilityMeasure.ne_zero ν, hN ▸ hνN, ?_⟩, C, hC, hCN, hνC⟩
  intro f hfi g hg
  exact hf f (fun γ h1 h1' y => hfi γ ⟨(mΓ γ).1 h1, (mN γ).1 h1'⟩ y) g ((mN g).2 hg)

end GlobalTheory.UnipQuot
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.St

theorem siegelWeil_volumes : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J ∧ Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J := by
  intro hSW F E _ _ _ _ _ σ hσ n J hJ

  exact hSW F E σ hσ n J hJ

end GlobalTheory.St
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.coeff_eq_zero_of_lipschitz_unitary_flow_decay : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (U : ℝ → V →ₗ[ℂ] V) (C : ℝ) (v : V), (∀ x, 0 ≤ I x x) → U 0 = LinearMap.id → (∀ s t, U (s + t) = (U s).comp (U t)) → (∀ s x y, I (U s x) (U s y) = I x y) → (∀ s x, |s| ≤ 1 → (I (U s x - x) (U s x - x)).re ≤ C * s ^ 2 * (I x x).re) → (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖I v (U s v)‖ ≤ A * Real.exp (-(e * |s|))) → I v v = 0 := by
  first | exact @GlobalTheory.LipFlow.coeff_eq_zero | exact GlobalTheory.LipFlow.coeff_eq_zero | (intros; apply GlobalTheory.LipFlow.coeff_eq_zero <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.tendsto_rescaled_integral_of_ball_density_bounds : ∀ (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ν → (∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ → ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧ volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r)) → ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, Continuous φ → HasCompactSupport φ → Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x, φ x)) := by
  first | exact @GlobalTheory.tendsto_rescaled_integral_of_density_one | exact GlobalTheory.tendsto_rescaled_integral_of_density_one | (intros; apply GlobalTheory.tendsto_rescaled_integral_of_density_one <;> assumption)
end
