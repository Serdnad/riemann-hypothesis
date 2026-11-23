module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle531
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle002
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TwistRatio

theorem exists_smul_of_isTwistPull : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) (m : ℕ), 1 ≤ m →
    ∀ (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
      (α α' : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp K)) P.A).left, (snd (baseOver (Sp K)) P.A ^ m).left]
        ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (s₁ s₁' : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), α.IsGen → α'.IsGen →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α' th s₁' →
    ∃ c : K, (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁' : EA P (𝟙 (Sp K)) (m ^ 2)) = c • SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁ := by
  intro K _ _ _ P m hm th α α' s₁ s₁' hα hα' h h'
  have hG := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨a, ha⟩ := H1.exists_const P.L P.isLB (fst (baseOver (Sp K)) P.A).left
    (BoxTheta.surj_fst hG P.isAb _)
    (LB.mulGen P.L _ _ _ _ α' (LB.invGen P.L _ _ α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα' (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, DVR.SecOps.sec_ext fun j => ?_⟩
  refine sec_ext_val P.isLB (fun y J hJ => ?_) j
  have e1 := VVRank.sv_of_isTwistPull P.A h' (𝟙 _) y hJ
  have e0 := VVRank.sv_of_isTwistPull P.A h (𝟙 _) y hJ
  have ev := ha _ (𝟙 _) y J hJ
  rw [val_mul hJ, val_inv] at ev
  have es := SecMod.value_smul hJ (𝟙 _) c (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁)
  refine e1.trans (Eq.trans ?_ es.symm)
  have eg : gs (𝟙 _) y ⊤ (scal (fst (baseOver (Sp K)) P.A).left c) =
      gs (𝟙 _ ≫ (fst (baseOver (Sp K)) P.A).left) y ⊤
        ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv) c) :=
    gs_pull _ _ y ⊤ trivial _
  have eu : (val α' (𝟙 _) y J).val =
      (val α' (𝟙 _) y J * (val α (𝟙 _) y J)⁻¹).val * (val α (𝟙 _) y J).val := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  change _ = _ * VVRank.sv P.A s₁ (𝟙 _) y J
  rw [e0, eg, ← ev, eu, _root_.mul_assoc]

end GlobalTheory.TwistRatio
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DoublingEvLaw

theorem elim_dot {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem star_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    star (schr ψ (w.1, -w.2) φ) = schr ψ w (star φ) := by
  funext x
  simp only [schr, Pi.star_apply, star_mul', dotProduct_neg, mul_neg, ← neg_add, AddChar.map_neg_eq_inv]
  rw [Complex.inv_eq_conj (hψ _), Complex.star_def, Complex.conj_conj]

variable {F : Type} [Field F] [NumberField F]

theorem sliceL {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (b : κ' → AF F) : (fun x => Φ (Sum.elim x b)) ∈ schA F κ := by
  have e1 : (fun x => Φ (Sum.elim x b)) = fun x => Φ (GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') b x) :=
    funext fun x => congrArg Φ (funext fun k => by cases k <;> rfl)
  rw [e1]
  exact GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.sumComm κ κ') b hΦ

theorem sliceR {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (a : κ → AF F) : (fun x => Φ (Sum.elim a x)) ∈ schA F κ' :=
  GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (∀ x, ‖ψ x‖ = 1) →
    ∀ (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
      (A₁ B₁ A₂ B₂ : κ → AF F) (a b : κ₁ → AF F),
      (∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) →
      ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
        schr ψ (Sum.elim a a, Sum.elim b (-b)) (evDbl T φ) := by
  intro F _ _ ψ hψ κ κ₁ _ _ T A₁ B₁ A₂ B₂ a b h1 h2 h3 φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a, -b) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := star_schr' ψ hψ (a, -b) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := sliceL hΨ (s ∘ Sum.inr + a)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b) - ⅟(2 : AF F) * (a ⬝ᵥ b)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b (-b) = (s ∘ Sum.inl) ⬝ᵥ b - (s ∘ Sum.inr) ⬝ᵥ b := by
    rw [← Sum.elim_comp_inl_inr s, elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_eq_add_neg]
  rw [hs]
  ring

end GlobalTheory.DoublingEvLaw
end
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.L2RightPartial

theorem partR_lintegral_sq_eq_const_mul_of_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ T hT hmem μ hμ
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C, hC⟩ := hT μ₂ inferInstance

  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : (κ ⊕ κ' → AF F) ≃ₜ+ (κ → AF F) × (κ' → AF F) :=
    { e.toEquiv with
      map_add' := fun _ _ => rfl
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  haveI : (μ.map eA).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ eA
  set c := (μ.map eA).addHaarScalarFactor (μ₁.prod μ₂)
  have hprod : μ.map eA = c • μ₁.prod μ₂ := Measure.isAddLeftInvariant_eq_smul _ _

  have key : ∀ g : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable g →
      ∫⁻ z, g z ∂μ = c * ∫⁻ a, ∫⁻ b, g (Sum.elim a b) ∂μ₂ ∂μ₁ := by
    intro g hg
    have h1 : ∫⁻ z, g z ∂μ = ∫⁻ p, g (e.symm p) ∂(μ.map eA) := by
      rw [show μ.map eA = μ.map e.toMeasurableEquiv from rfl, lintegral_map_equiv]
      refine lintegral_congr fun z => ?_
      exact congrArg g (e.symm_apply_apply z).symm
    rw [h1, hprod, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
      lintegral_prod (fun p => g (e.symm p)) (hg.comp e.symm.continuous.measurable).aemeasurable]
    rfl
  have hmeas : ∀ Φ ∈ schA F (κ ⊕ κ'), Measurable fun z => ‖Φ z‖ₑ ^ 2 := fun Φ hΦ =>
    ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ).measurable.enorm).pow_const 2
  refine ⟨C, fun Φ hΦ => ?_⟩
  have hslice : ∀ a : κ → AF F, (fun x => Φ (Sum.elim a x)) ∈ schA F κ' := fun a =>
    GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ
  have hin : ∀ a : κ → AF F, ∫⁻ b, ‖partR T Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ =
      C * ∫⁻ b, ‖Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ := fun a => hC _ (hslice a)
  have hm2 : Measurable fun a : κ → AF F => ∫⁻ b, ‖Φ (Sum.elim a b)‖ₑ ^ 2 ∂μ₂ :=
    ((hmeas Φ hΦ).comp e.symm.continuous.measurable).lintegral_prod_right'
  rw [key _ (hmeas _ (hmem Φ hΦ)), key _ (hmeas Φ hΦ)]
  simp_rw [hin]
  rw [lintegral_const_mul _ hm2, mul_left_comm]

end GlobalTheory.DblEval.L2RightPartial

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section
namespace GlobalTheory.DblEval.PartLStr

theorem mul_blocks_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {κ κ' : Type} {a : (κ → X) → ℂ} {b : (κ' → X) → ℂ}
    (ha : a ∈ SB (κ → X)) (hb : b ∈ SB (κ' → X)) :
    (fun z : κ ⊕ κ' → X => a (z ∘ Sum.inl) * b (z ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → X) := by
  have hc : Continuous fun p : (κ → X) × (κ' → X) => Sum.elim p.1 p.2 :=
    continuous_pi fun k => by
      cases k
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]
  refine ⟨(ha.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inl) (by fun_prop)).mul
    (hb.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inr) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((ha.2.isCompact.prod hb.2.isCompact).image hc) fun z hz => ?_
  by_cases h1 : z ∘ Sum.inl ∈ tsupport a
  · by_cases h2 : z ∘ Sum.inr ∈ tsupport b
    · exact absurd ⟨(z ∘ Sum.inl, z ∘ Sum.inr), ⟨h1, h2⟩, Sum.elim_comp_inl_inr z⟩ hz
    · simp only [image_eq_zero_of_notMem_tsupport h2, mul_zero]
  · simp only [image_eq_zero_of_notMem_tsupport h1, zero_mul]

theorem glue_sumComm {R κ κ' : Type} (a : κ' → R) (x : κ → R) :
    GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') a x = Sum.elim x a := by
  funext k; cases k <;> rfl

theorem exists_partL_pureA : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ']
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e →
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ₁ ⊕ κ' → Af F),
      ∀ f : SInf F (κ ⊕ κ'), partL e (pureA F f g) = pureA F (P f) g₁ := by
  intro F _ _ κ κ₁ κ' _ _ _ e he
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨ei, ev, hSB, hstd, hpure⟩ := he
  let eq₀ : (κ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.sumArrowLequivProdArrow κ κ' ℝ _).toContinuousLinearEquiv
  let eq₁ : (κ₁ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ₁ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.sumArrowLequivProdArrow κ₁ κ' ℝ _).toContinuousLinearEquiv
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.schwartz_operator_parametric_extension (V' := κ' → mixedEmbedding.mixedSpace F) ei
  let P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ') := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₁).comp
    (P₀.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₀.symm))
  have hP : ∀ (f : SInf F (κ ⊕ κ')) (y : κ₁ → mixedEmbedding.mixedSpace F) (x' : κ' → mixedEmbedding.mixedSpace F)
      (h : SInf F κ), (∀ x, h x = f (Sum.elim x x')) → P f (Sum.elim y x') = ei h y := by
    intro f y x' h hh
    have h1 : eq₁ (Sum.elim y x') = (y, x') := rfl
    simp only [P, ContinuousLinearMap.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h1]
    exact hP₀ _ x' h (fun x => (hh x).trans rfl) y
  refine ⟨P, fun g hg => ?_⟩
  have hE : ∀ (z : AF F) (v : Pl (F := F)), evFin F v z = evalV F v z.2 := fun _ _ => rfl
  obtain ⟨m, a, b, ha, hb, hab⟩ := GlobalTheory.T.schwartz_bruhat_sum_split_tensor g hg
  choose n φ hφSB hφstd hφ using fun k => GlobalTheory.T.adelic_schwartz_function_factorizable_sum (a k) (ha k)
  let g₁ : (κ₁ ⊕ κ' → Af F) → ℂ := ∑ k, ∑ j : Fin (n k), fun z =>
    (∏ᶠ v, ev v (φ k j v) fun i => evalV F v (z (Sum.inl i))) * b k (z ∘ Sum.inr)
  have hev : ∀ k j, ∀ᶠ v in cofinite, ev v (φ k j v) = stdInd F κ₁ v := fun k j => by
    filter_upwards [hstd, hφstd k j] with v h1 h2
    rw [h2, h1]
  refine ⟨g₁, Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ =>
    mul_blocks_mem_SB (GlobalTheory.AdelicCoordSB.finprod_mem_SB F κ₁ _ (fun v => hSB v _ (hφSB k j v)) (hev k j)) (hb k), ?_⟩
  intro f
  funext y
  obtain ⟨T, hT⟩ := GlobalTheory.ThK.Adapt.exists_slice (κ := κ ⊕ κ') (κ₁ := κ) (Equiv.sumComm κ κ')
    (fun i => evI F (y (Sum.inr i)))
  have hh : ∀ x, T f x = f (Sum.elim x fun i => evI F (y (Sum.inr i))) := fun x => by
    rw [hT, glue_sumComm]
  have hslice : (fun x : κ → AF F => pureA F f g (Sum.elim x (y ∘ Sum.inr))) =
      ∑ k, ∑ j : Fin (n k), b k (fun i => (y (Sum.inr i)).2) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) (φ k j) := by
    funext x
    have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (Sum.elim x (y ∘ Sum.inr) i).1) =
        Sum.elim (fun i => evI F (x i)) fun i => evI F (y (Sum.inr i)) := by
      funext i; cases i <;> rfl
    have e2 : (fun i => (Sum.elim x (y ∘ Sum.inr) i).2) = Sum.elim (fun i => (x i).2) fun i => (y (Sum.inr i)).2 := by
      funext i; cases i <;> rfl
    simp only [pureA, e1, e2, hab, hφ, ← hh, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hE]
    ring
  have ey : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) =
      Sum.elim (fun i => evI F (y (Sum.inl i))) fun i => evI F (y (Sum.inr i)) := by
    funext i; cases i <;> rfl
  show e (fun x => pureA F f g (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl) = pureA F (P f) g₁ y
  rw [hslice]

  simp only [map_sum, map_smul, hpure (T f) _ (hφSB _ _) (hφstd _ _), pureA, ey,
  hP f _ _ (T f) hh, g₁, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hE, Function.comp_def]
  ring
end GlobalTheory.DblEval.PartLStr

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertLagInd

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {κ : Type} [Fintype κ]

theorem invOf_two_mem (h : (2 : 𝓞 F) ∉ v.asIdeal) : ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [invOf_eq_inv, map_inv₀, h2]

theorem schr_box_apply (ψ : AddChar (Fv F v) ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v))
    (x : κ → Fv F v) :
    schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) (boxFun φ₁ φ₂) (Sum.elim x x) =
      ψ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * (φ₁ (x + w.1) * φ₂ x) := by
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  congr 2
  all_goals (congr 1; funext i; simp)

end GlobalTheory.InertLagInd

namespace GlobalTheory.InertLagInd

theorem diagW_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  intro F _ _ v κ _ ψ hψ h2 μ hμ
  classical
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨S, hS⟩ : ∃ S : Set (κ → Fv F v), S = {x | ∀ k, x k ∈ v.adicCompletionIntegers F} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ S ↔ ∀ k, x k ∈ v.adicCompletionIntegers F := fun x => by subst hS; rfl
  have hpi : S = Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x; simp [hmem]
  have hSo : IsOpen S := by
    rw [hpi]; exact isOpen_set_pi Set.finite_univ (fun _ _ => Valued.isOpen_integer _)
  have hSc : IsCompact S := by
    rw [hpi]; exact isCompact_univ_pi (fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
  have h0S : (0 : κ → Fv F v) ∈ S := (hmem 0).2 fun k => zero_mem _
  have hadd : ∀ {a}, a ∈ S → ∀ x, (x + a ∈ S ↔ x ∈ S) := fun {a} ha x => by
    rw [hmem, hmem]
    rw [hmem] at ha
    exact ⟨fun h k => by simpa using sub_mem (h k) (ha k), fun h k => add_mem (h k) (ha k)⟩
  have hind : ∀ {a}, a ∈ S → ∀ x, S.indicator (1 : (κ → Fv F v) → ℂ) (x + a) = S.indicator 1 x := fun ha x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hadd ha x).2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hadd ha x).1 hx)]
  have hψ1 : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    rw [psiAt_apply]; simpa using (hψ 1).2 (one_mem _) y hy
  have hφ : S.indicator (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
    rw [hS]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨S.indicator 1, hφ, ((μ.real S : ℝ) : ℂ), ?_, S ×ˢ S, hSo.prod hSo, hSc.prod hSc, ⟨h0S, h0S⟩, ?_⟩
  · have h1 : μ S ≠ 0 := hSo.measure_ne_zero μ ⟨0, h0S⟩
    have h2' : μ S ≠ ⊤ := hSc.measure_lt_top.ne
    exact Complex.ofReal_ne_zero.2 (by rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨h1, h2'⟩)
  intro w
  simp only [diagW, schr_box_apply]
  by_cases hw1 : w.1 ∈ S
  · by_cases hw2 : w.2 ∈ S
    · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨hw1, hw2⟩)]
      have key : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) = S.indicator (1 : (κ → Fv F v) → ℂ) x := by
        intro x
        rw [hind hw1 x]
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, hψ1]
          · simp
          · rw [hmem] at hx hw1 hw2
            exact add_mem (sum_mem fun i _ => mul_mem (hx i) (hw2 i))
              (mul_mem (invOf_two_mem h2) (sum_mem fun i _ => mul_mem (hw1 i) (hw2 i)))
        · simp [Set.indicator_of_notMem hx]
      simp_rw [key]
      rw [show S.indicator (1 : (κ → Fv F v) → ℂ) = S.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hSo.measurableSet]
      simp
    · rw [Set.indicator_of_notMem (fun h => hw2 (Set.mem_prod.1 h).2)]
      obtain ⟨i, hi⟩ : ∃ i, w.2 i ∉ v.adicCompletionIntegers F := by
        by_contra h; push_neg at h; exact hw2 ((hmem _).2 h)
      obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (w.2 i * y) ≠ 1 := by
        by_contra h; push_neg at h; exact hi ((hψ _).1 h)
      have ha : Pi.single i y ∈ S := (hmem _).2 fun k => by
        rw [Pi.single_apply]; split_ifs
        · exact hy
        · exact zero_mem _
      set g : (κ → Fv F v) → ℂ := fun x => psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) with hg
      have hshift : ∀ x, g (x + Pi.single i y) = psiAt ψ v (w.2 i * y) * g x := by
        intro x
        simp only [hg]
        rw [add_right_comm, hind ha, hind ha, add_dotProduct, single_dotProduct,
          show x ⬝ᵥ w.2 + y * w.2 i + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) =
            w.2 i * y + (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) by ring, AddChar.map_add_eq_mul]
        ring
      have hI : ∫ x, g x ∂μ = psiAt ψ v (w.2 i * y) * ∫ x, g x ∂μ := by
        rw [← integral_const_mul, ← integral_add_right_eq_self _ (Pi.single i y)]
        simp only [hshift]
      rw [psiAt_apply] at hI
      have : (1 - psiLoc ψ v (w.2 i * y)) * ∫ x, g x ∂μ = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)
  · rw [Set.indicator_of_notMem (fun h => hw1 (Set.mem_prod.1 h).1)]
    have hz : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
        (S.indicator (1 : (κ → Fv F v) → ℂ) (x + w.1) * S.indicator 1 x) = 0 := by
      intro x
      by_cases hx : x ∈ S
      · have : x + w.1 ∉ S := fun h => hw1 (by rw [add_comm] at h; exact (hadd hx w.1).1 h)
        simp [Set.indicator_of_notMem this]
      · simp [Set.indicator_of_notMem hx]
    simp_rw [hz]
    exact integral_zero _ _

end GlobalTheory.InertLagInd
end
end
