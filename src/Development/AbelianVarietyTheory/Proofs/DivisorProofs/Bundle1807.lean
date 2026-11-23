module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

theorem _root_.GlobalTheory.T.extremal_vectors_holomorphic_model_unique_up_to_phase : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), GlobalTheory.HolDict.HolShape M → ExtLine M := by
  first | exact @GlobalTheory.HolLowOnce.extLine_of_holShape | exact GlobalTheory.HolLowOnce.extLine_of_holShape | (intros; apply GlobalTheory.HolLowOnce.extLine_of_holShape <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.RepresentativeL2

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {𝓕 : Set G}

theorem meas_mk : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := measurable_quotient_mk''

theorem ae_up [μ.IsMulLeftInvariant] (h : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), p q) :
    ∀ᵐ x ∂μ, p (Quotient.mk _ x) := by
  have h1 := ae_of_ae_map (meas_mk (Γ := Γ)).aemeasurable hp
  rw [ae_iff, Measure.restrict_apply₀' h.nullMeasurableSet] at h1
  rw [ae_iff]
  refine h.measure_zero_of_invariant _ (fun g => ?_) h1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have : (Quotient.mk (QuotientGroup.rightRel Γ) (g⁻¹ • x)) = Quotient.mk _ x := by
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simp [Subgroup.smul_def]
  simp only [Set.mem_setOf_eq, this]

end General

theorem repr_properties : ∀ (D : D7) (V : HSp D), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → (∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ F, Repr V μ 𝓕 F φ) ∧ (∀ F ψ ψ', Continuous ψ → Continuous ψ' → Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F ψ' → ψ = ψ') ∧ (∀ F F' ψ, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ → F = F') ∧ (∀ F ψ g, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 (ρ g F) (rTr V g ψ)) ∧ (∀ F F' ψ ψ' (a : ℂ), Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → Repr V μ 𝓕 (a • F + F') (a • ψ + ψ')) ∧ ∀ F F' ψ ψ', Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → IntegrableOn (fun x => star (ψ x) * ψ' x) 𝓕 μ ∧ ⟪F, F'⟫_ℂ = ∫ x in 𝓕, star (ψ x) * ψ' x ∂μ := by
  intro D V μ 𝓕 ρ hp hr
  obtain ⟨-, -, -, hB, hT, -, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hp.haar
  haveI := hp.right
  have hm : Measurable (autMk V) := meas_mk
  haveI : IsFiniteMeasure (nuQ V μ 𝓕) := ⟨by
    rw [nuQ, Measure.map_apply hm MeasurableSet.univ]
    simpa [lt_top_iff_ne_top] using hp.fin⟩
  have up : ∀ {p : AutQ V → Prop}, (∀ᵐ q ∂(nuQ V μ 𝓕), p q) → ∀ᵐ x ∂μ, p (autMk V x) := fun h => ae_up hp.fd h
  refine ⟨fun φ hφ hinv ⟨C, hC⟩ => ?_, fun F ψ ψ' h h' e e' => ?_, fun F F' ψ e e' => ?_, fun F ψ g e => ?_,
    fun F F' ψ ψ' a e e' => ?_, fun F F' ψ ψ' e e' => ?_⟩
  · let f : AutQ V → ℂ := Quotient.lift φ fun a b hab => by
      have := hinv _ (QuotientGroup.rightRel_apply.1 hab) a
      rw [inv_mul_cancel_right] at this
      exact this.symm
    have hf : Measurable f := measurable_from_quotient.2 hφ.measurable
    have hL : MemLp f 2 (nuQ V μ 𝓕) :=
      MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun q => by
        induction q using Quotient.inductionOn with
        | h x => exact hC x)
    exact ⟨hL.toLp f, up hL.coeFn_toLp⟩
  · refine (h.ae_eq_iff_eq μ h').1 ?_
    filter_upwards [e, e'] with x h1 h2
    rw [← h1, h2]
  · refine Lp.ext ?_
    refine (ae_map_iff hm.aemeasurable
      ((Lp.stronglyMeasurable F).measurableSet_eq_fun (Lp.stronglyMeasurable F'))).2 (ae_restrict_of_ae ?_)
    filter_upwards [e, e'] with x h1 h2
    rw [h1, h2]
  · have e2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e
    filter_upwards [hr.val g F, e2] with x h1 h2
    rw [h1, h2]; rfl
  · filter_upwards [up (Lp.coeFn_add (a • F) F'), up (Lp.coeFn_smul a F), e, e'] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]; rfl
  · have hI : Integrable (fun q => ⟪F q, F' q⟫_ℂ) (nuQ V μ 𝓕) := L2.integrable_inner F F'
    have hae : (fun x => ⟪F (autMk V x), F' (autMk V x)⟫_ℂ) =ᵐ[μ.restrict 𝓕] fun x => star (ψ x) * ψ' x := by
      refine ae_restrict_of_ae ?_
      filter_upwards [e, e'] with x h1 h2
      rw [h1, h2]
      simp [mul_comm]
    refine ⟨((integrable_map_measure hI.aestronglyMeasurable hm.aemeasurable).1 hI).congr hae, ?_⟩
    rw [L2.inner_def, ← integral_congr_ae hae]
    exact integral_map hm.aemeasurable hI.aestronglyMeasurable

end GlobalTheory.HolDict.RepresentativeL2
end

section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise

namespace GlobalTheory.QuotRegular

section General

variable {G : Type} [Group G] (Γ : Subgroup G)

abbrev cl (g : G) : Quotient (QuotientGroup.rightRel Γ) := Quotient.mk _ g

theorem cl_mul (γ : Γ) (x : G) : cl Γ ((γ : G) * x) = cl Γ x := by
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  simp

def tr (g : G) : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ) :=
  Quotient.map' (fun x => x * g) fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h

theorem tr_cl (g x : G) : tr Γ g (cl Γ x) = cl Γ (x * g) := rfl

theorem tr_one : tr Γ 1 = id := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (cl Γ) (mul_one x)

theorem tr_mul (g h : G) : tr Γ (g * h) = tr Γ h ∘ tr Γ g := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (cl Γ) (mul_assoc x g h).symm

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem measurable_cl : Measurable (cl Γ) := measurable_quotient_mk''

theorem measurable_tr (g : G) : Measurable (tr Γ g) := by
  rw [measurable_from_quotient]
  exact (measurable_cl Γ).comp (measurable_mul_const g)

variable {Γ} {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ] {𝓕 : Set G}

theorem ae_of_ae_quot (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (cl Γ)), p q) : ∀ᵐ x ∂μ, p (cl Γ x) := by
  have h1 := ae_of_ae_map (measurable_cl Γ).aemeasurable hp
  rw [ae_restrict_iff'₀ h𝓕.nullMeasurableSet] at h1
  have h2 : ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ 𝓕 → p (cl Γ ((γ : G) * y)) :=
    ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h1
  filter_upwards [h2, h𝓕.ae_covers] with y hy hc
  obtain ⟨γ, hγ⟩ := hc
  simpa only [cl_mul] using hy γ hγ

variable [μ.IsMulRightInvariant]

theorem measurePreserving_tr (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) :
    MeasurePreserving (tr Γ g) ((μ.restrict 𝓕).map (cl Γ)) ((μ.restrict 𝓕).map (cl Γ)) := by
  refine ⟨measurable_tr Γ g, Measure.ext fun A hA => ?_⟩
  have hA' : MeasurableSet (cl Γ ⁻¹' A) := measurable_cl Γ hA
  rw [Measure.map_apply (measurable_tr Γ g) hA, Measure.map_apply (measurable_cl Γ) hA,
    Measure.map_apply (measurable_cl Γ) (measurable_tr Γ g hA), Measure.restrict_apply hA',
    Measure.restrict_apply (measurable_cl Γ (measurable_tr Γ g hA))]
  have hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => by
        change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
        rw [mul_assoc]
  have hinv : ∀ γ : Γ, (fun x => γ • x) ⁻¹' (cl Γ ⁻¹' A) = cl Γ ⁻¹' A := by
    intro γ
    ext x
    change cl Γ ((γ : G) * x) ∈ A ↔ cl Γ x ∈ A
    rw [cl_mul]
  rw [← hD'.measure_set_eq h𝓕 hA' hinv, ← measure_preimage_mul_right μ g (_ ∩ (fun x => x * g⁻¹) ⁻¹' 𝓕)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, tr_cl, mul_inv_cancel_right]

theorem measure_symmDiff_le (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {A : Set (Quotient (QuotientGroup.rightRel Γ))}
    (hA : MeasurableSet A) (g g₀ : G) :
    ((μ.restrict 𝓕).map (cl Γ)) ((tr Γ g ⁻¹' A) ∆ (tr Γ g₀ ⁻¹' A)) ≤
      μ (((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆ ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕))) := by
  set S := ((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆ ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) with hS
  have hU : μ.restrict 𝓕 (⋃ γ : Γ, γ • S) ≤ μ S := by
    rw [h𝓕.measure_eq_tsum S]
    refine (measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))
    rw [Measure.restrict_apply₀' h𝓕.nullMeasurableSet]
  rw [Measure.map_apply (measurable_cl Γ) ((measurable_tr Γ g hA).symmDiff (measurable_tr Γ g₀ hA))]
  refine le_trans (measure_mono_ae ?_) hU
  have key : ∀ a b x : G, (∃ γ : Γ, γ • (x * a) ∈ 𝓕) → cl Γ (x * a) ∈ A → cl Γ (x * b) ∉ A →
      ∃ γ : Γ, (γ : G) * x * a ∈ cl Γ ⁻¹' A ∩ 𝓕 ∧ (γ : G) * x * b ∉ cl Γ ⁻¹' A ∩ 𝓕 := by
    rintro a b x ⟨γ, hγ⟩ h2 h3
    refine ⟨γ, ?_, fun h => h3 ?_⟩
    · rw [mul_assoc]
      exact ⟨by rw [mem_preimage, cl_mul]; exact h2, hγ⟩
    · have := h.1
      rwa [mem_preimage, mul_assoc, cl_mul] at this
  filter_upwards [ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h𝓕.ae_covers),
    ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h𝓕.ae_covers)] with x e1 e2 hx
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨γ, k1, k2⟩ := key g g₀ x e1 a b
    exact mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩
  · obtain ⟨γ, k1, k2⟩ := key g₀ g x e2 a b
    exact mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩

def reg (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    G →* (Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ)) →L[ℂ] Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) where
  toFun g := (Lp.compMeasurePreservingₗᵢ ℂ (tr Γ g) (measurePreserving_tr h𝓕 g)).toContinuousLinearMap
  map_one' := by
    refine ContinuousLinearMap.ext fun F => Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 1)).trans ?_
    rw [tr_one]
    rfl
  map_mul' g h := by
    refine ContinuousLinearMap.ext fun F => Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 (g * h))).trans ?_
    refine EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (tr Γ h) (measurePreserving_tr h𝓕 h) F) (measurePreserving_tr h𝓕 g)).symm
    rw [tr_mul]
    exact ((measurePreserving_tr h𝓕 g).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 h))).symm

theorem reg_apply (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    reg h𝓕 g F = Lp.compMeasurePreserving (tr Γ g) (measurePreserving_tr h𝓕 g) F := rfl

theorem reg_val (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    ∀ᵐ x ∂μ, reg h𝓕 g F (cl Γ x) = F (cl Γ (x * g)) :=
  ae_of_ae_quot h𝓕 (p := fun q => reg h𝓕 g F q = F (tr Γ g q))
    (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 g))

theorem norm_reg (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    ‖reg h𝓕 g F‖ = ‖F‖ := Lp.norm_compMeasurePreserving F (measurePreserving_tr h𝓕 g)

theorem continuous_reg [LocallyCompactSpace G] [SecondCountableTopology G] [IsFiniteMeasureOnCompacts μ]
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    Continuous fun g => reg h𝓕 g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => reg h𝓕 g F)
    ?_ ?_ ?_ F
  · intro c A hA hμA
    rw [Lp.simpleFunc.coe_indicatorConst]
    simp only [reg_apply, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set ENNReal.ofNat_ne_top fun g₀ => ?_
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆
        ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)))) (𝓝 g₀) (𝓝 0) :=
      tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
        (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
        (measurePreserving_mul_right μ g₀)
        ((measurable_cl Γ hA).nullMeasurableSet.inter h𝓕.nullMeasurableSet)
        (by
          rw [Measure.map_apply (measurable_cl Γ) hA, Measure.restrict_apply (measurable_cl Γ hA)] at hμA
          exact hμA.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      fun g => measure_symmDiff_le h𝓕 hA g g₀
  · intro f g hf hg _ h1 h2
    simp only [map_add (f := _)]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => reg h𝓕 g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_reg, ← dist_eq_norm, dist_comm]
    exact h

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.HolDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isReg : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    FinPair V μ 𝓕 → ∃ ρ, IsReg V μ 𝓕 ρ := by
  intro D V μ 𝓕 h
  obtain ⟨h1, h2, -, h4, h5, -, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := h.haar
  have := h.right
  exact ⟨reg h.fd, reg_val h.fd, norm_reg h.fd, continuous_reg h.fd⟩

end GlobalTheory.QuotRegular
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_one_eventually_ge : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → M.IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a + a') (m * b + b') 1 := by
  intro hA k _ X _ p D hD P a b a' b' M α hRep hAmp hSP hSI ε hε
  obtain ⟨t₀, ht⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hA k X p D hD P a b a' b' M α hRep hAmp hSP hSI
  exact GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge X.functionField
    (fun m : ℕ => P.H (m * a + a') (m * b + b')) (fun m : ℕ => P.Bl (m * a + a') (m * b + b')) (D + 1)
    (Nat.succ_pos D) (fun m => GlobalTheory.VolBr.Pair.isBallFam k X p P _ _)
    (fun m R => GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hD P _ _ R) _ _ t₀ ht ε hε

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.TwistSmall

theorem mem_regular_sections_second_bundle_indep_first {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (P : Pair p) (L' : HermLB p) (r : L'.B.ι → X.functionFieldˣ) (hr : IsRatSec L'.B r)
    {s : X.functionField} (hs : s ∈ P.H 0 1) :
    s ∈ (⟨L', P.A, r, P.r', hr, P.hr'⟩ : Pair p).H 0 1 := by
  intro x i j _ hj
  have hx : x ∈ (⨆ i, P.L.B.U i) := by rw [P.L.isLB.cover]; trivial
  obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  simpa [Pair.loc] using hs x i' j hi' hj

theorem le_dual_pow_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (N : HermLB p) (s : X.functionField), IsAmpleLB P.A.B → s ∈ P.H 0 1 → s ≠ 0 →
    ∃ c₁ : ℕ, ∀ c, c₁ ≤ c → 0 < c → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Le (((shiftA P u).A.pow c).dual) N := by
  intro k _ X _ p D hX P N s hA hs hs0
  obtain ⟨rN, hrN⟩ := exists_isRatSec N.isLB
  let Q : Pair p := ⟨N, P.A, rN, P.r', hrN, P.hr'⟩
  obtain ⟨c₁, g, _, hg0, hg, -⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX Q hA 1 Empty (fun e => e.elim)
  refine ⟨c₁, fun c hc hc0 => ?_⟩
  have hsQ : s ∈ Q.H 0 1 := mem_regular_sections_second_bundle_indep_first P N rN hrN hs
  obtain ⟨hpow, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 s hsQ (c - c₁)
  obtain ⟨hf, -⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q 1 c₁ _ _ g (s ^ (c - c₁)) hg hpow
  have e1 : (1 : ℤ) + ((c - c₁ : ℕ) : ℤ) * 0 = 1 := by ring
  have e2 : (c₁ : ℤ) + ((c - c₁ : ℕ) : ℤ) * 1 = c := by push_cast [Nat.cast_sub hc]; ring
  rw [e1, e2] at hf
  obtain ⟨w, _, hw⟩ := GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX Q 1 c _ hf
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc0
  refine ⟨w / c, fun u hu => ?_⟩
  obtain ⟨-, hBl, -⟩ := GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p Q u
  have hwu : w ≤ (c : ℤ) * u := by
    have := (div_le_iff₀ hcpos).1 hu
    push_cast; linarith
  have hmem : g * s ^ (c - c₁) ∈ (shiftA Q u).Bl 1 c 1 := by
    rw [hBl, one_mul]
    exact ⟨hw.1, fun σ y => (hw.2 σ y).trans (Real.exp_le_exp.2 hwu)⟩
  have hne : g * s ^ (c - c₁) ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ hs0)
  have hrepN := (Pair.rep_base k X p (shiftA Q u)).1
  have hrepA := (Pair.rep_base k X p (shiftA Q u)).2.1
  have hpowA := Pair.rep_pow k X p (shiftA Q u) 0 1 _ c hrepA
  have hdual := Pair.rep_dual k X p (shiftA Q u) _ _ _ hpowA
  have e3 : (1 : ℤ) - -((c : ℤ) * 0) = 1 := by ring
  have e4 : (0 : ℤ) - -((c : ℤ) * 1) = c := by ring
  have hmem' : g * s ^ (c - c₁) ∈ (shiftA Q u).Bl (1 - -((c : ℤ) * 0)) (0 - -((c : ℤ) * 1)) 1 := by
    rw [e3, e4]; exact hmem
  exact GlobalTheory.T.hermLBLeBySmallSection_of_rep k X p (shiftA Q u) 1 0 _ _ N _ _ hrepN hdual hne hmem'

end GlobalTheory.HSNef.TwistSmall
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_twist_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N c : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N (-c) R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a e : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a e σ y f :=
    fun a e σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hsH, hsn⟩ := hG.s_mem
  obtain ⟨hpH, hpn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P (-1) b t htH N
  obtain ⟨hqH, hqn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hsH c
  have e1 : (N : ℤ) + N * -1 + c * 0 = 0 := by ring
  have e2 : -(c : ℤ) + N * b + c * 1 = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N (-c) R, f * t ^ N * s ^ c ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH1, hn1⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N (-c) (N * -1) (N * b) f (t ^ N) hfH hpH
    obtain ⟨hH, hn⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P (N + N * -1) (-c + N * b) (c * 0) (c * 1) (f * t ^ N) (s ^ c) hH1 hqH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hn1 σ y, hpn σ y, hqn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    have h2 : P.nu 0 1 σ y s ^ c ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (hsn σ y)
    have h3 : P.nu N (-c) σ y f * P.nu (-1) b σ y t ^ N ≤ R :=
      (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
    exact (mul_le_of_le_one_right (mul_nonneg (nu_nonneg _ _ _ _ _) (pow_nonneg (nu_nonneg _ _ _ _ _) _)) h2).trans h3
  have hinj : Set.InjOn (fun f => f * t ^ N * s ^ c) (P.Bl N (-c) R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) (mul_right_cancel₀ (pow_ne_zero c hG.s_ne) h)
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N (-c) R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, Regime P D → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N (-c) (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX P b s t hG c hR
  obtain ⟨α, β, hαβ⟩ := hR
  have hb : (0 : ℝ) < b := by exact_mod_cast hG.pos
  have hlim := hαβ (3 / b) (by positivity)
  have hsub : Tendsto (fun N : ℕ => b * N) atTop atTop :=
    tendsto_id.const_mul_atTop' hG.pos
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      P.lc 0 ((b * N : ℕ) : ℤ) (Real.exp (3 / b * ((b * N : ℕ) : ℝ))) / ((b * N : ℕ) : ℝ) ^ (D + 1) < C :=
    ⟨_, (hlim.comp hsub).eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C * (b : ℝ) ^ (D + 1), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have e1 : 3 / (b : ℝ) * ((b * N : ℕ) : ℝ) = 3 * N := by push_cast; field_simp
  have e2 : ((b * N : ℕ) : ℤ) = (N : ℤ) * b := by push_cast; ring
  have hpos : (0 : ℝ) < ((b * N : ℕ) : ℝ) ^ (D + 1) := by push_cast; positivity
  rw [e1, e2, div_lt_iff₀ hpos] at hN
  calc P.lc N (-c) (Real.exp (3 * N)) ≤ P.lc 0 ((N : ℤ) * b) (Real.exp (3 * N)) :=
        lc_twist_le_of_good P hG N c _ (GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 0 _ _)
    _ ≤ C * ((b * N : ℕ) : ℝ) ^ (D + 1) := hN.le
    _ = C * (b : ℝ) ^ (D + 1) * (N : ℝ) ^ (D + 1) := by push_cast; ring

end GlobalTheory.HSNef
end
