module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalPointsUnitaryGroup
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP

@[expose] public section

section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

open scoped ComplexConjugate

namespace GlobalTheory.SecForm

theorem coordVec_expand {n : ℕ} (w : V n) : w = ∑ a, w a • coordVec a := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem sesq_sum_left {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (x : ι → V n) (y : V n) : α (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i * α (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hα.smul_left 0 0 y
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_left, hα.smul_left, ih, smul_eq_mul]

theorem sesq_sum_right {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (x : V n) (y : ι → V n) : α x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, conj (c i) * α x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hα.smul_right 0 x 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_right, hα.smul_right, ih, smul_eq_mul]

theorem sesq_expand {n : ℕ} {α : V n → V n → ℂ} (hα : IsSesq α) (x y : V n) :
    α x y = ∑ a, ∑ b, α (coordVec a) (coordVec b) * (x a * conj (y b)) := by
  calc α x y = α (∑ a, x a • coordVec a) (∑ b, y b • coordVec b) := by
        rw [← coordVec_expand x, ← coordVec_expand y]
    _ = _ := by
        rw [sesq_sum_left (α := α) hα]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sesq_sum_right (α := α) hα, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

theorem pull_ofValues : ∀ {n : ℕ} (L : V n →L[ℂ] V n) (α : V n → V n → ℂ), IsSesq α → pull L (ofValues α : Alt n) = ofValues (fun ξ η => α (L ξ) (L η)) := by
  intro n L α hα

  simp only [ofValues, sesq_expand hα (L _), AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym, map_sum,
  map_smul, map_mul, (pull_dz L _).1, (pull_dz L _).2, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul,
  Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]

end GlobalTheory.SecForm
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.LineForm

theorem chain_sum_coordVec {n : ℕ} (w : V n) : w = ∑ b, w b • coordVec b := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem del_dbar_comp_holo_pull : ∀ (m n : ℕ) (τ : V m → V n) (c : V n → ℂ) (v : V m),
    DifferentiableAt ℂ τ v → DifferentiableAt ℝ c (τ v) →
    (∑ a, del (fun x => c (τ x)) v (coordVec a) • dz a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, del c (τ v) (coordVec a) • dz a) ∧
    (∑ a, dbar (fun x => c (τ x)) v (coordVec a) • dzb a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, dbar c (τ v) (coordVec a) • dzb a) := by
  intro m n τ c v hτ hc
  constructor

  · simp only [del_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]

    simp only [map_sum, map_smul, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]

  · simp only [dbar_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).2, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]

    simp only [map_sum, map_smulₛₗ, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]

end GlobalTheory.LineForm
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuInfType

theorem char_eq_zpow (χ : ℂˣ →* ℂˣ) (hc : Continuous χ) (hu : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (hp : ∀ z : ℂˣ, (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χ z = 1) :
    ∃ n : ℤ, ∀ z : ℂˣ, (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ n := by
  have hmem : ∀ z, (χ (Circle.toUnits z) : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hu _
  let f : Circle →* Circle :=
    { toFun := fun z => (⟨(χ (Circle.toUnits z) : ℂ), hmem z⟩ : Circle)
      map_one' := Circle.ext (by simp)
      map_mul' := fun a b => Circle.ext (by
        change ((χ (Circle.toUnits (a * b))) : ℂ) = (χ (Circle.toUnits a) : ℂ) * (χ (Circle.toUnits b) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcu : Continuous (Circle.toUnits : Circle → ℂˣ) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · exact continuous_subtype_val
    · have : (fun x : Circle => ((Circle.toUnits x)⁻¹ : ℂˣ).val) = fun x : Circle => (x : ℂ)⁻¹ := by
        funext x; simp
      rw [this]
      exact (continuous_subtype_val).inv₀ fun x => Circle.coe_ne_zero x
  have hf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact Units.continuous_val.comp (hc.comp hcu)
  obtain ⟨n, hn⟩ := GlobalTheory.circle_hom_eq_zpow f hf
  refine ⟨n, fun z => ?_⟩
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hn0 : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have hw : (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
    simp [Submonoid.unitSphere, mem_sphere_zero_iff_norm, norm_div, hz0]
  let w : Circle := (⟨_, hw⟩ : Circle)
  let r : ℂˣ := Units.mk0 (‖(z : ℂ)‖ : ℂ) hn0
  have hzr : z = Circle.toUnits w * r := Units.ext (by
    change (z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) * (‖(z : ℂ)‖ : ℂ)
    field_simp)
  have hr : χ r = 1 := hp r (by simp [r])
  have h1 := congrArg (fun c : Circle => (c : ℂ)) (hn w)
  have hχ : χ z = χ (Circle.toUnits w) := by rw [hzr, map_mul, hr, mul_one]
  rw [hχ]
  change ((f w : Circle) : ℂ) = _
  rw [h1, Circle.coe_zpow]

end GlobalTheory.MuInfType

noncomputable section

open ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.MuInfType

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def single (v : InfinitePlace E) : ℂˣ →* (Cinf E)ˣ := Units.map (MonoidHom.mulSingle (fun _ : InfinitePlace E => ℂ) v)

theorem continuous_single (v : InfinitePlace E) : Continuous (single v) :=
  Continuous.units_map _ (by
    show Continuous (fun z : ℂ => (Pi.mulSingle v z : InfinitePlace E → ℂ))
    exact continuous_mulSingle (A := fun _ : InfinitePlace E => ℂ) v)


variable (E) in
abbrev below (v : InfinitePlace E) : InfinitePlace (maximalRealSubfield E) := v.comap (algebraMap (maximalRealSubfield E) E)

def iota (v : InfinitePlace E) : (below E v).Completion →+* ℂ :=
  (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).toRingHom.comp
    (AbsoluteValue.Completion.map (below E v).1 v.1)

theorem ideleMap_infIdele (v : InfinitePlace E) (x : ((below E v).Completion)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) =
      infId E (single v (Units.map (iota v).toMonoidHom x)) := by
  classical
  refine Units.ext (ad_ext ?_ ?_)
  · funext w
    have h1 : ∀ u : (Cinf E)ˣ, pInf E (infId E u).val = u.val := fun u => by
      change (infEq E).symm (1 - infEq E 1 + infEq E u.val) = _
      simp
    rw [h1]
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
      (AbsoluteValue.Completion.map (below E w).1 w.1
        (Pi.mulSingle (below E v) ((x : (below E v).Completion)) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
    by_cases h : w = v
    · subst h
      rw [Pi.mulSingle_eq_same]
      simp [single, iota]
    · have h' : w.comap (algebraMap (maximalRealSubfield E) E) ≠ below E v := fun e =>
        h ((IsCMField.equivInfinitePlace E).injective e)
      rw [Pi.mulSingle_eq_of_ne h']
      simp [single, Pi.mulSingle_eq_of_ne h]
  · change pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) : Ad E) =
      pFin E (infId E _).val
    refine (map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)).trans ?_
    change (1 : Af E) = 1 - 0 + 0
    simp

theorem iota_real (v : InfinitePlace E) (s : ℝ) :
    iota v ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s) = s := by
  let ψ : ℝ →+* ℂ := (iota v).comp
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.toRingHom
  have hψ : Continuous ψ :=
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
      (AbsoluteValue.Completion.continuous_map (below E v).1 v.1)).comp
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.continuous
  have := map_real_smul ψ hψ s 1
  simpa [ψ] using this

end GlobalTheory.MuInfType

end

noncomputable section

open ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.MuInfType

theorem infType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E), μ.IsUnitary →
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    ∃ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) ∧
      ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v := by
  intro E _ _ _ μ hU hη
  let χv : InfinitePlace E → ℂˣ →* ℂˣ := fun v => (chiInf μ).comp (single v)
  have hcont : ∀ v, Continuous (χv v) := fun v => (continuous_chiInf μ).comp (continuous_single v)
  have hunit : ∀ v z, ‖(χv v z : ℂ)‖ = 1 := fun v z => hU _
  have hval : ∀ v (x : ((below E v).Completion)ˣ),
      χv v (Units.map (iota v).toMonoidHom x) = (GlobalTheory.GalOfCusp.quadChar E).1 (infIdele _ (below E v) x) := by
    intro v x
    change μ.1 (infId E (single v _)) = _
    rw [← ideleMap_infIdele, hη]
  have hneg : ∀ v, χv v (-1) = -1 := by
    intro v
    have e : Units.map (iota v).toMonoidHom (-1) = -1 := Units.ext (by simp)
    have h := hval v (-1)
    rw [e] at h
    rw [h]
    exact GlobalTheory.GalOfCusp.quadChar_locInf E (below E v)
  have hpos : ∀ v (z : ℂˣ), (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χv v z = 1 := by
    intro v z hz
    set s : ℝ := Real.sqrt ‖(z : ℂ)‖ with hs
    have hs0 : s ≠ 0 := by
      rw [hs]
      exact (Real.sqrt_pos.2 (norm_pos_iff.2 z.ne_zero)).ne'
    have hx0 : (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s ≠ 0 := by
      simpa using hs0
    let x : ((below E v).Completion)ˣ := Units.mk0 _ hx0
    have hx : Units.map (iota v).toMonoidHom x ^ 2 = z := Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, x,
        Units.val_mk0, iota_real]
      rw [← Complex.ofReal_pow, hs, Real.sq_sqrt (norm_nonneg _), hz])
    rw [← hx, map_pow, hval]
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E _)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  choose e he using fun v => GlobalTheory.MuInfType.char_eq_zpow (χv v) (hcont v) (hunit v) (hpos v)
  refine ⟨e, fun v => ?_, fun z => ?_⟩
  · have h := he v (-1)
    rw [hneg] at h
    simp only [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, div_one] at h
    rcases Int.even_or_odd (e v) with h' | h'
    · rw [h'.neg_one_zpow] at h
      norm_num at h
    · exact h'
  · let zv : InfinitePlace E → ℂˣ := fun v => Units.map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) v) z
    have hz : z = ∏ v, single v (zv v) := Units.ext (by
      rw [Units.coe_prod]
      simp only [single, zv, Units.coe_map, MonoidHom.coe_coe, MonoidHom.mulSingle_apply, Pi.evalMonoidHom_apply]
      exact (Finset.univ_prod_mulSingle z.val).symm)
    conv_lhs => rw [hz]
    rw [map_prod, Units.coe_prod]
    exact Finset.prod_congr rfl fun v _ => he v (zv v)

end GlobalTheory.MuInfType

end
end

section

open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.ConjDualTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ}

theorem opTriv_thetaOp (o : Op E m) : opTriv (thetaOp o) = opTriv o := by
  cases o <;> rfl

theorem act_mulChi_oneFn (ψ : HChar E) (o : Op E m) :
    act o (mulChi m ψ (oneFn E m)) = (((opMul ψ o : ℂˣ) : ℂ) * opTriv o + opAdd ψ o) • mulChi m ψ (oneFn E m) := by
  rw [act_mulChi, act_oneFn, smul_smul, ← add_smul, map_smul]

theorem pull_oneFn : GlobalTheory.ThetaPull.pull E m (oneFn E m) = oneFn E m := Subtype.ext rfl

theorem scalar_thetaOp (χ : HChar E) (o : Op E m) :
    ((opMul χ (thetaOp o) : ℂˣ) : ℂ) * opTriv o + opAdd χ (thetaOp o) =
      ((opMul (GlobalTheory.ThetaPull.thetaChar χ) o : ℂˣ) : ℂ) * opTriv o + opAdd (GlobalTheory.ThetaPull.thetaChar χ) o := by
  have h1 := GlobalTheory.ThetaPull.act_pull o (mulChi m χ (oneFn E m))
  simp only [act_mulChi_oneFn, map_smul, GlobalTheory.ThetaPull.pull_mulChi, pull_oneFn, opTriv_thetaOp] at h1
  have hF : mulChi m (GlobalTheory.ThetaPull.thetaChar χ) (oneFn E m) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 oneFn_ne_zero
  exact (smul_left_injective ℂ hF h1).symm

theorem isConjDualBy_twist_thetaChar : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ} {π : GlobalTheory.CuspRep.CuspSub E m}, π.IsCsd → ∀ χ : Formalism.L2.Host.HChar E, GlobalTheory.GalOfCusp.IsConjDualBy (π.twist χ) (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹) := by
  intro E _ _ _ m π hπ χ
  refine GlobalTheory.GalOfCusp.isConjDualBy_twist hπ fun o => ?_
  have e : χ * (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹)⁻¹ = GlobalTheory.ThetaPull.thetaChar χ := by
    rw [mul_inv_rev, inv_inv, mul_comm (GlobalTheory.ThetaPull.thetaChar χ), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [e]
  have h := scalar_thetaOp χ o
  cases o with
  | fin k => exact ⟨Units.ext (by simpa [opTriv, opAdd, thetaOp] using h), rfl⟩
  | cpt k => exact ⟨Units.ext (by simpa [opTriv, opAdd, thetaOp] using h), rfl⟩
  | lie X => exact ⟨rfl, by simpa [opTriv, opMul, thetaOp] using h⟩

end GlobalTheory.ConjDualTwist

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.UnitaryBC

namespace GlobalTheory.PolChar

theorem exists_compNorm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {χ : Formalism.L2.Host.HChar E} {u : ℝ},
    χ.IsAbsPow u → ∃ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E),
      GlobalTheory.GalOfCusp.compNorm E ψ = χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹ ∧
        ∀ v : InfinitePlace (maximalRealSubfield E), ψ.locInf v (-1) = 1 := by
  intro E _ _ _ χ u h
  refine ⟨resReal χ, Subtype.ext (MonoidHom.ext fun x => ?_), resReal_locInf_neg_one h⟩
  change χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
    χ.1 x * ((χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹)⁻¹
  rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, ideleConj_eq, inv_inv]

end GlobalTheory.PolChar
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_ample_kernel_finite_subgroupScheme : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : LB A.left) (H : Over (Sp K)) (_ : GrpObj H) (j : H ⟶ A), L.IsLB ∧ IsProjBy A.hom ∧ (∃ t : LB.Gen (Theta A L), t.IsGen) ∧ IsMonHom j ∧ IsClosedImmersion j.left ∧ IsFinite H.hom ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  first | exact @GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel | exact GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel | (intros; apply GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel <;> assumption)
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolomorphicRootNormBound

theorem vNormSq_lt_of_root :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam → IsHolChamber ε lam → ∀ a b : Fin n, ε a = true → ε b = false → vNormSq ε (lowK ε lam - root a b) < vNormSq ε (lowK ε lam) := by
  intro n ε lam hanti hch a b ha hb
  have hA1 : CompanionTheory.D.DSIC.A1 ε = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [CompanionTheory.D.DSIC.A1, Finset.mem_filter] at hi
    exact absurd (hch.lt hanti i.2.1 i.2.2) (not_lt.2 hi.2.le)
  let i : CompanionTheory.D.DSIC.NC ε := ⟨(a, b), ha, hb⟩
  have hne : ({i} : Finset (CompanionTheory.D.DSIC.NC ε)) ≠ CompanionTheory.D.DSIC.A1 ε := by
    rw [hA1]; exact Finset.singleton_ne_empty i
  have h := CompanionTheory.D.DSIC.hNormLt n ε lam hanti {i} hne
  have hgam : CompanionTheory.D.DSIC.gam ε lam = lowK ε lam := by
    funext c
    simp [CompanionTheory.D.DSIC.gam, hA1, CompanionTheory.D.DSIC.wtA]
    rfl
  have hw : CompanionTheory.D.DSIC.wtA ({i} : Finset (CompanionTheory.D.DSIC.NC ε)) = root a b := by
    funext c
    simp only [CompanionTheory.D.DSIC.wtA, Finset.filter_singleton, root, Pi.sub_apply, Pi.single_apply, i]
    by_cases h1 : a = c <;> by_cases h2 : b = c <;> simp [h1, h2, eq_comm]
  rw [hgam, hw] at h
  exact h

end GlobalTheory.HolomorphicRootNormBound
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (X : Set (AF F ⊗[F] E)), IsCompact X → IsClosed (SUSupp σ J ε) → (∀ g ∈ SUSupp σ J ε, ∀ i j, ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ X) → IsCompact (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppCompact.isCompact_SUSupp | exact GlobalTheory.SUSuppCompact.isCompact_SUSupp | (intros; apply GlobalTheory.SUSuppCompact.isCompact_SUSupp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  first | exact @GlobalTheory.SUTrunc.mem_closure_supp | exact GlobalTheory.SUTrunc.mem_closure_supp | (intros; apply GlobalTheory.SUTrunc.mem_closure_supp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_closure_rational_points_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ h ∈ SUSupp σ J η, h ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j)} := by
  first | exact @GlobalTheory.SUWeakApprox.weak_approx_SU | exact GlobalTheory.SUWeakApprox.weak_approx_SU | (intros; apply GlobalTheory.SUWeakApprox.weak_approx_SU <;> assumption)
end
