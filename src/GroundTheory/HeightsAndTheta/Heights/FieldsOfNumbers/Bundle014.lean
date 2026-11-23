module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.HilbEventuallyPolyQualified
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle007
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbDegreeBound
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMultEqualsCoeff
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPolyOfDiffs
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPrimeFiltration
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Sub.Prod
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
import Mathlib.RingTheory.LocalProperties.Reduced
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem GradedFinite.full : GradedFinite.Statement.{u} := GradedFinite.proof

theorem HilbExactDivide.full : HilbExactDivide.Statement.{u} :=
  HilbExactDivide.proof GradedFinite.full

theorem PolyOfDiffs.full : PolyOfDiffs.Statement := PolyOfDiffs.proof

theorem HilbEventuallyPoly.full : HilbEventuallyPoly.Statement.{u} :=
  HilbEventuallyPoly.of_exactDivide_polyOfDiffs HilbExactDivide.full PolyOfDiffs.full

theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof HilbExactDivide.full

theorem EventuallyPolyUnique.full : EventuallyPolyUnique.Statement := EventuallyPolyUnique.proof

theorem EventuallyPolyShift.full : EventuallyPolyShift.Statement := EventuallyPolyShift.proof

theorem HilbIrrelevantZero.full : HilbIrrelevantZero.Statement.{u} := HilbIrrelevantZero.proof

theorem RelevantPrimeDimGe.full : RelevantPrimeDimGe.Statement.{u} := RelevantPrimeDimGe.proof

theorem HilbDegreeBound.full : HilbDegreeBound.Statement.{u} :=
  HilbDegreeBound.proof HilbEventuallyPoly.full HilbExactDivide.full PolyOfDiffs.full
    PrimeFiltration.full EventuallyPolyUnique.full EventuallyPolyShift.full
    HilbIrrelevantZero.full RelevantPrimeDimGe.full

theorem MixedDiffConst.full : MixedDiffConst.Statement.{u} :=
  MixedDiffConst.proof HilbDegreeBound.full HilbEventuallyPoly.full

theorem IntNumSymm.full : IntNumSymm.Statement := IntNumSymm.proof

theorem IntNumAdd.full : IntNumAdd.Statement.{u} := IntNumAdd.proof MixedDiffConst.full

theorem IntNumZeroSlot.full : IntNumZeroSlot.Statement.{u} :=
  IntNumZeroSlot.proof MixedDiffConst.full HilbEventuallyPoly.full HilbDegreeBound.full

theorem IntNumBase.full : IntNumBase.Statement.{u} := IntNumBase.proof MixedDiffConst.full

theorem MultEqualsCoeff.full : MultEqualsCoeff.Statement.{u} :=
  MultEqualsCoeff.proof PrimeFiltration.full MixedDiffConst.full RelevantPrimeDimGe.full

theorem CutRegular.full : CutRegular.Statement.{u} :=
  CutRegular.proof HilbExactDivide.full MultEqualsCoeff.full IntNumSymm.full

theorem CutRational.full : CutRational.Statement.{u} :=
  CutRational.proof CutRegular.full IntNumAdd.full

theorem ExistsForm.full : ExistsForm.Statement.{u} := ExistsForm.proof

theorem DivCycleSupport.full : DivCycleSupport.Statement.{u} := DivCycleSupport.proof

theorem IntNumUnique.full : IntNumUnique.Statement.{u} :=
  IntNumUnique.proof CutRational.full IntNumBase.full ExistsForm.full DivCycleSupport.full

theorem ProjectionFormulaContracted.full : ProjectionFormulaContracted.Statement.{u} :=
  PFContracted.proof MixedDiffConst.full CutRational.full

theorem ProjectionFormulaDegree.of_divPushForward (h : DivPushForward.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} :=
  ProjectionFormulaDegree.proof CutRational.full IntNumBase.full ProjectionFormulaContracted.full h

theorem RenameHilbFn.full : RenameHilbFn.Statement.{u} := RenameHilbFn.proof

theorem RenameIntNum.full : RenameIntNum.Statement.{u} := RenameIntNum.proof RenameHilbFn.full

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocLocal.proof (h : DegZeroLocQuot.Statement.{u}) : DegZeroLocLocal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have hWp : W.IsPrime := hW.isPrime
  have hne : ∀ g : MRing ι F, g ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hrep : ∀ x : degZeroLoc P {W}, ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ P ∧ g ∉ W ∧
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) := fun x => by
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hx⟩ := h F K ι P {W}
      (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) x x.2
    exact ⟨b, f, g, hf, hg, hgP, hgW W (Set.mem_singleton W), hx⟩

  have hnon : ∀ (x : degZeroLoc P {W}) (f g : MRing ι F), g ∉ W → f ∈ W →
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → ¬ IsUnit x := by
    intro x f g hgW hfW hx hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := hrep y
    have hgP : g ∉ P := fun hg => hgW (hPW hg)
    have h1 : ((x * y : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = 1 := by
      rw [hy]; rfl
    rw [Subalgebra.coe_mul, hx, hy', div_mul_div_comm,
      div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul,
      ← map_mul, ← map_mul] at h1
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h1)
    have h3 : g * g' ∈ W := by
      have := W.sub_mem (W.mul_mem_right f' hfW) (hPW h2)
      rwa [sub_sub_cancel] at this
    rcases hWp.mem_or_mem h3 with h4 | h4
    exacts [hgW h4, hg'W h4]

  have hunit : ∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
      IsMultiHomog g b → g ∉ P → f ∉ W →
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → IsUnit x := by
    intro x b f g hf hg hgP hfW hx
    have hfP : f ∉ P := fun h' => hfW (hPW h')
    have hmem := div_mem_degZeroLoc P {W} hg hf hfP
      (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hfW)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, hx, div_mul_div_comm, mul_comm (algebraMap _ _ _),
      div_self (mul_ne_zero (hne g hgP) (hne f hfP))]
  have : Nontrivial (degZeroLoc P {W}) :=
    ⟨⟨0, 1, fun e => zero_ne_one (congrArg Subtype.val e)⟩⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a c ha hc
  obtain ⟨b, f, g, hf, hg, hgP, hgW, hx⟩ := hrep a
  obtain ⟨b', f', g', hf', hg', hg'P, hg'W, hy⟩ := hrep c
  have hfW : f ∈ W := by
    by_contra hfW
    exact (mem_nonunits_iff.mp ha) (hunit a b f g hf hg hgP hfW hx)
  have hf'W : f' ∈ W := by
    by_contra hf'W
    exact (mem_nonunits_iff.mp hc) (hunit c b' f' g' hf' hg' hg'P hf'W hy)
  refine mem_nonunits_iff.mpr (hnon (a + c) (f * g' + g * f') (g * g') (fun h5 => ?_)
    (W.add_mem (W.mul_mem_right g' hfW) (W.mul_mem_left g hf'W)) ?_)
  · rcases hWp.mem_or_mem h5 with h6 | h6
    exacts [hgW h6, hg'W h6]
  · rw [Subalgebra.coe_add, hx, hy, div_add_div _ _ (hne g hgP) (hne g' hg'P)]
    set_option synthInstance.maxHeartbeats 200000 in
      simp only [map_add, map_mul]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocFrac.proof : DegZeroLocFrac.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro x hx

  let E : IntermediateField F (FractionRing (MRing ι F ⧸ P)) :=
    { carrier := {x | ∃ y ∈ degZeroLoc P 𝒲, ∃ z ∈ degZeroLoc P 𝒲, z ≠ 0 ∧ x = y / z}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, z₁, hz₁, hz₁0, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, hz₂0, rfl⟩
        exact ⟨y₁ * y₂, Subalgebra.mul_mem _ hy₁ hy₂, z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂,
          mul_ne_zero hz₁0 hz₂0, by rw [div_mul_div_comm]⟩
      add_mem' := by
        rintro _ _ ⟨y₁, hy₁, z₁, hz₁, hz₁0, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, hz₂0, rfl⟩
        exact ⟨y₁ * z₂ + z₁ * y₂,
          Subalgebra.add_mem _ (Subalgebra.mul_mem _ hy₁ hz₂) (Subalgebra.mul_mem _ hz₁ hy₂),
          z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_ne_zero hz₁0 hz₂0,
          by rw [div_add_div _ _ hz₁0 hz₂0]⟩
      algebraMap_mem' := fun c => ⟨algebraMap F _ c, Subalgebra.algebraMap_mem _ c, 1,
        Subalgebra.one_mem _, one_ne_zero, (div_one _).symm⟩
      inv_mem' := by
        rintro _ ⟨y, hy, z, hz, hz0, rfl⟩
        by_cases hy0 : y = 0
        · exact ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, by simp [hy0]⟩
        · exact ⟨z, hz, y, hy, hy0, by rw [inv_div]⟩ }
  suffices hle : homFracDegZero P ≤ E from hle hx
  unfold homFracDegZero
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨b, f, g, hf, hg, hgP, rfl⟩

  obtain ⟨e, h, hh, hbe, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have hW' := h𝒲P W (h𝒲.mem_toFinset.mp hW)
        exact ⟨hW'.isPrime, hW'.multiHomog, hW'.relevant⟩) b
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W ∈ 𝒲, h ∉ W := fun W hW =>
    hhS W (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW))

  obtain ⟨m, hm, hmP⟩ := exists_form_not_mem_of_isRelevant (H := P) hP.relevant (e - b)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hbe] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hbe] at this
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    div_ne_zero (hq0 _ fun h' => (hP.isPrime.mem_or_mem h').elim hgP hmP) (hq0 _ hhP), ?_⟩
  simp only [map_mul]
  rw [div_div_div_cancel_right₀ (hq0 _ hhP), mul_div_mul_right _ _ (hq0 _ hmP)]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]


omit [DecidableEq K] in
theorem chartMonomial_add (u : ∀ k, ι k) (a c : K → ℕ) :
    (chartMonomial u (a + c) : MRing ι F) = chartMonomial u a * chartMonomial u c := by
  simp only [chartMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (c : K → ℕ) :
    IsMultiHomog (chartMonomial u c : MRing ι F) c := by
  show IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, u k⟩ : MRing ι F) ^ c k) c
  have h := IsWeightedHomogeneous.prod (R := F) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ c k) (fun k => c k • blockWeight ι ⟨k, u k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (c k))
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]

theorem finsuppProd_chartVar (u : ∀ k, ι k) (e : (Σ k, ι k) →₀ ℕ) :
    (e.prod fun v n => (X ⟨v.1, u v.1⟩ : MRing ι F) ^ n) =
      chartMonomial u (Finsupp.weight (blockWeight ι) e) := by
  induction e using Finsupp.induction_linear with
  | zero => simp [chartMonomial]
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add (f := _),
      chartMonomial_add]
  | single v n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single]
    simp only [chartMonomial]
    rw [Finset.prod_eq_single v.1]
    · simp [blockWeight]
    · intro k _ hk
      simp [blockWeight, hk]
    · simp

theorem chartMap_monomial_mul (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) (e : (Σ k, ι k) →₀ ℕ) (c : F) :
    chartMap P u (monomial e c) *
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
          (Ideal.Quotient.mk P (chartMonomial u (Finsupp.weight (blockWeight ι) e))) =
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (monomial e c)) := by
  have hy : ∀ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ≠ 0 := fun k => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  rw [← finsuppProd_chartVar, chartMap, aeval_monomial, monomial_eq]
  simp only [map_mul, map_finsuppProd, map_pow]
  rw [mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hy v.1))]

theorem MChartHomog.proof : MChartHomog.Statement.{u} := by
  intro F _ K _ _ ι u p
  classical
  obtain ⟨b, hle⟩ : ∃ b : K → ℕ, ∀ e ∈ p.support, Finsupp.weight (blockWeight ι) e ≤ b :=
    ⟨fun k => p.support.sup fun e => Finsupp.weight (blockWeight ι) e k, fun e he k =>
      Finset.le_sup (f := fun e => Finsupp.weight (blockWeight ι) e k) he⟩
  refine ⟨b, ∑ e ∈ p.support,
    monomial e (AddMonoidAlgebra.coeff p e) * chartMonomial u (b - Finsupp.weight (blockWeight ι) e), ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    have := (isWeightedHomogeneous_monomial (blockWeight ι) e (AddMonoidAlgebra.coeff p e) rfl).mul
      (chartMonomial_isMultiHomog (F := F) u (b - Finsupp.weight (blockWeight ι) e))
    rwa [add_tsub_cancel_of_le (hle e he)] at this
  · intro P _ hu
    have hY : ∀ c, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u c)) ≠ 0 := fun c => by
      simp only [chartMonomial, map_prod, map_pow]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    rw [eq_div_iff (hY b)]
    conv_lhs => rw [p.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have key : (chartMonomial u b : MRing ι F) = chartMonomial u (Finsupp.weight (blockWeight ι) e) *
        chartMonomial u (b - Finsupp.weight (blockWeight ι) e) := by
      rw [← chartMonomial_add, add_tsub_cancel_of_le (hle e he)]
    rw [key, map_mul, map_mul, map_mul, map_mul, ← mul_assoc, chartMap_monomial_mul P u hu]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem prod_pow_blockWeight {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {M : Type*}
    [CommMonoid M] (w : K → M) (e : (Σ k, ι k) →₀ ℕ) :
    ∏ k, w k ^ (Finsupp.weight (blockWeight ι) e k) = e.prod fun v n => w v.1 ^ n := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_eq_single v.1]
  · simp [blockWeight]
  · intro k _ hk
    simp [blockWeight, Pi.single_eq_of_ne hk]
  · simp

theorem MChartDehomog.proof : MChartDehomog.Statement := by
  intro F _ K _ _ ι P _ u hu f b hf
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  let w : K → L := fun k => φ (X ⟨k, u k⟩)
  have hw : ∀ k, w k ≠ 0 := fun k => by
    simp only [w, φ, RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  have hD : φ (chartMonomial u b) = ∏ k, w k ^ b k := by
    simp [chartMonomial, w, map_prod, map_pow]
  have hC : ∀ c : F, φ (C c) = algebraMap F L c := fun c => by
    simp only [φ, RingHom.comp_apply]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk F, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hmono : ∀ e ∈ f.support, chartMap P u (monomial e (AddMonoidAlgebra.coeff f e)) * ∏ k, w k ^ b k =
      φ (monomial e (AddMonoidAlgebra.coeff f e)) := by
    intro e he
    have hwe : Finsupp.weight (blockWeight ι) e = b := hf (mem_support_iff.mp he)
    rw [← hwe, prod_pow_blockWeight, chartMap, aeval_monomial, mul_assoc, ← Finsupp.prod_mul,
      monomial_eq, map_mul, hC, Finsupp.prod, Finsupp.prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    change (φ (X v) / w v.1) ^ e v * w v.1 ^ e v = φ (X v ^ e v)
    rw [← mul_pow, div_mul_cancel₀ _ (hw v.1), map_pow]
  change chartMap P u f = φ f / φ (chartMonomial u b)
  rw [hD, eq_div_iff (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k))]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hmono

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
