module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle322
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle328
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.HaarCoords

theorem haar_coords : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure ∧ lB.IsAddHaarMeasure ∧ lC.IsAddHaarMeasure ∧ SFinite μ ∧ SFinite lB ∧ SFinite lC ∧ Measurable (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∧ ∃ ν₀ : Measure (flagN d), ν₀.IsHaarMeasure ∧ ν₀.map Subtype.val = (μ.prod (lB.prod lC)).map (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d
  obtain ⟨iU1, iU2, iU3⟩ := GlobalTheory.UnitU.topology D ρ
  obtain ⟨-, familyMassSecondLine, iM3, iM4, -⟩ := lattice_Mx D ρ S₀.rank
  obtain ⟨-, indexCSecond, iC3, iC4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨iN1, iN2, iN3, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have hcl : IsClosed ((skewA D ρ : Set (Mx D ρ ρ))) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : T2Space (skewA D ρ) := inferInstance
  let μ : Measure (UX D ρ) := Measure.haar
  let lB : Measure (Mx D ρ S₀.rank) := Measure.addHaar
  let lC : Measure (skewA D ρ) := Measure.addHaar
  haveI : SigmaFinite μ := Measure.sigmaFinite_haarMeasure
  haveI : SFinite μ := MeasureTheory.instSFiniteOfSigmaFinite
  obtain ⟨e, he⟩ := GlobalTheory.MixPer.flagCoord_homeo D S S₀ ρ d
  have hΦ : (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
      Subtype.val ∘ e := funext fun p => (he p).symm
  have hem : Measurable e := e.continuous.measurable
  refine ⟨μ, lB, lC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hΦ]; exact (continuous_subtype_val.comp e.continuous).measurable
  refine ⟨(μ.prod (lB.prod lC)).map e, ?_, ?_⟩
  · haveI := Measure.IsFiniteMeasureOnCompacts.map (μ.prod (lB.prod lC)) e
    haveI : ((μ.prod (lB.prod lC)).map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
    suffices h : ((μ.prod (lB.prod lC)).map e).IsMulLeftInvariant from ⟨⟩
    refine ⟨fun g => ?_⟩
    obtain ⟨p₀, hp₀⟩ := e.surjective g
    have hg : (g : GA D S) = d.levi p₀.1.1 * (d.nB p₀.2.1 * d.nC p₀.2.2) := by rw [← hp₀, he]
    obtain ⟨⟨u', hu'⟩, b', c'⟩ := p₀
    obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.HaarCoords.transl_nB_preserves D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance b'
    obtain ⟨Tc, hTc, hTc'⟩ := GlobalTheory.HaarCoords.transl_nC D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance c'
    let Ta : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) :=
      Prod.map (fun u => ⟨u', hu'⟩ * u) id
    have hTa : MeasurePreserving Ta (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) :=
      (measurePreserving_mul_left μ _).prod (MeasurePreserving.id _)
    have hT := hTa.comp (hTb.comp hTc)
    have key : (fun x => g * x) ∘ e = e ∘ (Ta ∘ Tb ∘ Tc) := by
      funext p
      apply Subtype.ext
      have h3 : ∀ q, d.levi (Ta q).1.1 * (d.nB (Ta q).2.1 * d.nC (Ta q).2.2) =
          d.levi u' * (d.levi q.1.1 * (d.nB q.2.1 * d.nC q.2.2)) := fun q => by
        simp only [Ta, Prod.map_fst, Prod.map_snd, id, Subgroup.coe_mul, map_mul, mul_assoc]
      simp only [Function.comp_apply, Subgroup.coe_mul, he]
      rw [h3, hTb', hTc', hg]
      simp only [mul_assoc]
    rw [Measure.map_map (measurable_const_mul g) hem, key, ← Measure.map_map hem hT.measurable, hT.map_eq]
  · rw [Measure.map_map continuous_subtype_val.measurable hem, hΦ]

end GlobalTheory.HaarCoords

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_homeomorph_wittFlagCoordinates : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ e : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) ≃ₜ flagN d, ∀ p, (e p : GA D S) = d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2) := by
  first | exact @GlobalTheory.MixPer.flagCoord_homeo | exact GlobalTheory.MixPer.flagCoord_homeo | (intros; apply GlobalTheory.MixPer.flagCoord_homeo <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.PlaceCut

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem glue_mul {e : R} (he : e * e = e) (a b c d : Matrix ι ι A) :
    (e • a + (1 - e) • b) * (e • c + (1 - e) • d) = e • (a * c) + (1 - e) • (b * d) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, h2, mul_one, sub_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add]

omit [Fintype ι] [DecidableEq ι] in
theorem glue_self (e : R) (a : Matrix ι ι A) : e • a + (1 - e) • a = a := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem exists_glue (c : A →ₐ[R] A) (J : Matrix ι ι A) {e : R} (he : e * e = e) (g h : GlobalTheory.WeilM.UG c J) :
    ∃ p : GlobalTheory.WeilM.UG c J, (p.1.1 : Matrix ι ι A) = e • g.1.1 + (1 - e) • h.1.1 ∧
      ((p⁻¹).1.1 : Matrix ι ι A) = e • (g⁻¹).1.1 + (1 - e) • (h⁻¹).1.1 := by
  let q : GL ι A :=
    { val := e • g.1.1 + (1 - e) • h.1.1
      inv := e • g.1.2 + (1 - e) • h.1.2
      val_inv := by rw [glue_mul he, g.1.3, h.1.3, glue_self]
      inv_val := by rw [glue_mul he, g.1.4, h.1.4, glue_self] }
  have hq : q ∈ GlobalTheory.WeilM.UG c J := by
    have hg : (g.1.1)ᵀ * J * (g.1.1).map c = J := g.2
    have hh : (h.1.1)ᵀ * J * (h.1.1).map c = J := h.2
    show (e • g.1.1 + (1 - e) • h.1.1)ᵀ * J * (e • g.1.1 + (1 - e) • h.1.1).map c = J
    have m : (e • g.1.1 + (1 - e) • h.1.1).map c = e • (g.1.1).map c + (1 - e) • (h.1.1).map c := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul]
    rw [m, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
    have k := glue_mul he (g.1.1)ᵀ (h.1.1)ᵀ J J
    rw [glue_self] at k
    rw [k, glue_mul he, hg, hh, glue_self]
  exact ⟨⟨q, hq⟩, rfl, rfl⟩

end Alg

theorem exists_idem {F : Type} [Field F] [NumberField F] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) :
    ∃ e : AF F, e * e = e ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F e = 0 ∧ (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w e = 1) ∧
      (∀ w ∉ S, GlobalTheory.AdelicU.evFin F w e = 0) ∧
      ∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u * e = 0 := by
  classical
  let b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v 1
  have hb1 : ∀ w ∈ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 1 := by
    intro w hw

    rw [map_sum, Finset.sum_eq_single_of_mem w hw, GlobalTheory.AdelicU.evalV_singleFin_self]
    intro v _ hv
    exact GlobalTheory.AdelicU.evalV_singleFin_ne hv.symm 1
  have hb0 : ∀ w ∉ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 0 := by
    intro w hw

    rw [map_sum]
    refine Finset.sum_eq_zero fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne ?_ 1
    rintro rfl
    exact hw hv
  refine ⟨((0 : Ainf F), b), ?_, ?_, hb1, hb0, ?_⟩
  · refine Prod.ext (by change (0 : Ainf F) * 0 = 0; exact mul_zero _) ?_
    change b * b = b
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w ∈ S
    · rw [hb1 w hw, mul_one]
    · rw [hb0 w hw, mul_zero]
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  · intro u hu
    refine Prod.ext (by change u.1 * 0 = 0; exact mul_zero _) ?_
    change u.2 * b = 0
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul, map_zero]
    by_cases hw : w ∈ S
    · have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu w hw
      rw [this, zero_mul]
    · rw [hb0 w hw, mul_zero]

theorem exists_cut : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  intro F E _ _ _ _ _ σ n X g S
  obtain ⟨e, he, heI, he1, he0, heu⟩ := exists_idem S
  obtain ⟨gS, hS, -⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he g 1
  obtain ⟨k, hk, hk'⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he 1 g
  have hS2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS = e • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g + (1 - e) • 1 := hS
  have hk2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := hk
  have hk3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ := by
    rw [inv_one] at hk'
    exact hk'
  have hoff : ∀ (u : AF F) (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), u * e = 0 →
      u • (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (1 - e) • M) = u • M := by
    intro u M hu
    rw [smul_add, smul_smul, smul_smul, mul_sub, hu, mul_one, sub_zero, zero_smul, zero_add]
  refine ⟨gS, k, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k
    rw [hS2, hk2, glue_mul he, Matrix.mul_one, Matrix.one_mul, glue_self]
  · intro u hu
    rw [hS2, smul_sub, smul_add, smul_smul, smul_smul, mul_sub, heu u hu, mul_one, sub_zero, zero_smul, zero_add,
      sub_self]
  · intro w hw u hu
    have h1 : (1 - e) * u = 0 := hu (1 - e) (by rw [map_sub, map_one, he1 w hw, sub_self])
    have h2 : u * (1 - e) = 0 := by rw [mul_comm, h1]
    have h3 : u * e = u := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2.symm
    rw [hk2, smul_sub, smul_add, smul_smul, smul_smul, h2, h3, zero_smul, add_zero, sub_self]
  · intro u hu
    have h1 : e * u = 0 := hu e heI
    rw [hk2, smul_sub, smul_sub, hoff u _ (by rw [mul_comm, h1])]
  · intro w hw z hz
    have key : ∀ M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
        (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + (1 - e) • M) *ᵥ z = M *ᵥ z := by
      intro M
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, -, y, -, rfl⟩ := hz
        have h1 : e * a = 0 := ha e (he0 w hw)
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
          hoff a M (by rw [mul_comm, h1])]
      | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy]
      | neg x _ hx => rw [Matrix.mulVec_neg, Matrix.mulVec_neg, hx]
    rw [hk2, hk3]
    exact ⟨key _, key _⟩

end GlobalTheory.PlaceCut
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsFullLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  first
  | exact @GlobalTheory.LatAlmostAll.exists_finset_keeps
  | intro F E _ _ _ _ _ σ n X hL g
    exact GlobalTheory.LatAlmostAll.exists_finset_keeps σ X hL.toIsLattice g
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceStable

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem symplO_of_place {p : Place D} {x y : WO S T} (hx : wAt p x = x) (hy : wAt p y = 0) : symplO S T x y = 0 := by
  rw [← hx, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p, ← wAt_eq_smul, hy,
    GlobalTheory.SplitScalar.symplO_zero_right]

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p]

theorem wAt_wAt_ne {p q : Place D} (h : q ≠ p) (w : WO S T) : wAt q (wAt p w) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 q p h, zero_smul]

theorem heisO_swap {u w : WO S T} (h : symplO S T u w = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w (heisO ψ S T u f) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, h, AddChar.map_zero_eq_one, one_smul]

theorem isLatVac_map {Λ : AddSubgroup (WO S T)} {A : (WO S T → ℂ) → WO S T → ℂ} {f : WO S T → ℂ}
    (h : ∀ u ∈ Λ, heisO ψ S T u (A f) = A (heisO ψ S T u f)) (hf : IsLatVac (heisO ψ S T) Λ f) :
    IsLatVac (heisO ψ S T) Λ (A f) :=
  ⟨fun u hu => by rw [h _ (Λ.nsmul_mem hu 2), hf.1 u hu], fun e he u hu hh => by rw [h u hu, hf.2 e he u hu hh]⟩

theorem latO_empty {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {P : FinPl D → Prop}
    (hP : ∀ v, ¬ P v) {u : WO S T} (hu : u ∈ latO S T LS LT P) : u = 0 := by
  have h : latO S T LS LT P ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨α, -, h0, a, -, s, -, t, -, rfl⟩
    have hα : α = 0 := RestrictedProduct.ext _ _ fun v => h0 v (hP v)
    subst hα
    refine AddSubgroup.mem_bot.2 (Matrix.ext fun i j => ?_)
    exact TensorProduct.zero_tmul _ _
  exact AddSubgroup.mem_bot.1 (h hu)

theorem wAt_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    wAt (.inr τ) (lineAt θ τ z t : WO S T) = lineAt θ τ z t := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, h1, h2⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨-, -, -, -, h3, -, h4⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  refine funext fun i => funext fun j => ?_
  show idem D (.inr τ) * lineAt θ τ z t i j = lineAt θ τ z t i j
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [← sub_eq_zero, ← RingHom.map_sub]
    refine GlobalTheory.FockCompare.ThetaCont.infPart_eq_zero hσ _ fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul]
    by_cases h : τ' = τ
    · subst h
      rw [(h4 θ hθ τ').1, one_mul, sub_self]
    · have h5 : θ τ' (infPart D (lineAt θ τ z t i j)) = 0 := by
        have := h2 t τ'
        rw [if_neg h] at this
        exact congrFun (congrFun this i) j
      rw [h5, mul_zero, sub_self]
  · have h5 : finPart D (lineAt θ τ z t i j) = 0 := congrFun (congrFun (h1 t) i) j
    rw [RingHom.map_mul, h5, mul_zero]

theorem dRho_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T w g) =
      heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [heisO, ← deriv_const_mul_field]
  congr 1
  funext t
  rw [heisO_swap (symplO_of_place (wAt_lineAt hθ τ z t) hw)]
  rfl

theorem isFockVacAt_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ} {f : WO S T → ℂ}
    (hf : IsFockVacAt (heisO ψ S T) θ τ J f) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T w f) := by
  intro z
  have h := congrArg (GlobalTheory.SplitScalar.heisL ψ S T w) (hf z)
  rw [annih, map_add (f := _), map_smul, map_zero] at h
  rw [annih, dRho_heisO hθ hw, dRho_heisO hθ hw]
  exact h

theorem heis_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (q : Place D) (w : WO S T), wAt q w = 0 → VacAt ψ θ S T sS sT ΛS ΛT q f → VacAt ψ θ S T sS sT ΛS ΛT q (heisO ψ S T w f)) ∧ ∀ (p : Place D), IsLocal ψ θ S T sS sT ΛS ΛT p f → (∀ w : WO S T, IsLocal ψ θ S T sS sT ΛS ΛT p (heisO ψ S T (wAt p w) f)) ∧ (∀ (c : ℂ) g, IsLocal ψ θ S T sS sT ΛS ΛT p g → IsLocal ψ θ S T sS sT ΛS ΛT p (c • f + g)) ∧ ∀ τ : D.what₂.Tau, p = .inr τ → ∀ z, IsLocal ψ θ S T sS sT ΛS ΛT p (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT hψ hθ f hf
  refine ⟨fun q w hw hv => ?_, fun p hp => ⟨fun w => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _, ?_, fun τ hτ => ?_⟩,
    fun c g hg => ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul c hf) hg.1, ?_, fun τ hτ z => ?_⟩,
    fun τ hτ z => ⟨GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hf, ?_, fun τ' hτ' z' => ?_⟩⟩⟩
  · cases q with
    | inl v =>
      refine isLatVac_map (fun u hu => heisO_swap (symplO_of_place ?_ hw) f) hv
      have h := (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inl v)).2.1
      exact (sub_eq_zero.1 (latO_empty (fun v' h' => h'.2 (by rw [h'.1])) h)).symm
    | inr τ => exact isFockVacAt_heisO hθ hw hv
  · refine isLatVac_map (fun u hu => (heisO_swap (symplO_of_place (wAt_wAt p w) ?_) f).symm) hp.2.1
    exact (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).2.2 fun _ h => h
  · exact isFockVacAt_heisO hθ (wAt_wAt_ne hτ w) (hp.2.2 τ hτ)
  · have key : ∀ u, heisO ψ S T u f = f → heisO ψ S T u g = g → heisO ψ S T u (c • f + g) = c • f + g := fun u h1 h2 => by
      rw [← GlobalTheory.SplitScalar.heisL_apply, map_add (f := _), map_smul, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, h1, h2]
    exact ⟨fun u hu => key _ (hp.2.1.1 u hu) (hg.2.1.1 u hu),
      fun e he u hu hh => key _ (hp.2.1.2 e he u hu hh) (hg.2.1.2 e he u hu hh)⟩
  · have h1 := hp.2.2 τ hτ z
    have h2 := hg.2.2 τ hτ z
    have hc := GlobalTheory.WeilVacMove.isTheta_smul c hf
    rw [annih] at h1 h2 ⊢
    rw [GlobalTheory.FockIndep.dRho_add hψ hθ _ _ hc hg.1, GlobalTheory.FockIndep.dRho_add hψ hθ _ _ hc hg.1,
      GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ c hf, GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ c hf, smul_add, smul_comm,
      add_add_add_comm, ← smul_add, h1, h2, smul_zero, add_zero]
  · refine isLatVac_map (fun u hu => (dRho_heisO hθ ?_ z f).symm) hp.2.1
    exact (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inr τ)).2.2 fun _ _ => Sum.inl_ne_inr
  · have hne : τ' ≠ τ := fun h => hτ' (by rw [h, hτ])
    have hc : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' y (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' y f) := fun y => by
      rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ' y τ z hf, GlobalTheory.FockIndep.omDir, if_neg hne, Complex.ofReal_zero, mul_zero,
        zero_smul, zero_add]
    have ht := fun y => GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ' y hf
    have h1 := hp.2.2 τ' hτ' z'
    have h0 := GlobalTheory.FockIndep.dRho_smul hψ hθ τ z 0 hf
    rw [zero_smul, zero_smul] at h0
    rw [annih] at h1 ⊢
    rw [hc, hc, ← GlobalTheory.FockIndep.dRho_smul hψ hθ τ z _ (ht _),
      ← GlobalTheory.FockIndep.dRho_add hψ hθ τ z (ht _) (GlobalTheory.WeilVacMove.isTheta_smul _ (ht _)), h1, h0]

end GlobalTheory.PlaceStable

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mixedModelTerm_derivAlong_rational_pairing : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ x y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 (derAlong ψ θ V W C x G) y = (2 * Real.pi * Complex.I * (ratPair W y x : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTerm.DerLaw.term_derAlong | exact GlobalTheory.MixedTerm.DerLaw.term_derAlong | (intros; apply GlobalTheory.MixedTerm.DerLaw.term_derAlong <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.boundedAutomorphicRightTranslation_unitarisable_bounded : ∀ (D : D7) (V : HSp D), IsUnitarisable (bddRep V) ∧ ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∀ f₂ : bddAut V, ∃ ℓ : bddAut V →ₗ[ℂ] ℂ, (∀ f : bddAut V, ℓ f = l2 ν 𝓕 (f : GA D V → ℂ) f₂) ∧ ∀ f : bddAut V, ∃ C : ℝ, ∀ g, ‖ℓ (bddRep V g f)‖ ≤ C := by
  first | exact @GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded | exact GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded | (intros; apply GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.conjugatedLevelElement_keeps_standardLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔ Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m)))) := by
  first | exact @GlobalTheory.RowVertexInv.moved_keeps_std | exact GlobalTheory.RowVertexInv.moved_keeps_std | (intros; apply GlobalTheory.RowVertexInv.moved_keeps_std <;> assumption)
end
