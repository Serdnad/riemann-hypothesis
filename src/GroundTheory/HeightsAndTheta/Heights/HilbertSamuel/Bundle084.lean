module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle069
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenericFibre.proof : GenericFibre.Statement := by
  intro Ω _ _ κ _ x D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (coordIdeal ℤ x).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x → m = 0 := by
    intro m hm
    have h1 : m ∈ (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) := hm
    rw [show (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (coordIdeal ℤ x) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (coordIdeal ℤ x) =
      (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    simp only [Fintype.card_unit] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (D + 1) _ ?_
    rw [hform]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PullFormsGeneric

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)


omit [CharZero Ω] in
theorem aeval_scale {g : MRing ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) (y : (Σ k, ι k) → Ω) (t : K → Ω) :
    aeval (fun p => y p * t p.1) g = aeval y g * ∏ k, t k ^ d k := by
  have h := congrArg (MvPolynomial.eval t) (ProjLine.mConeMap_eq_of_isMultiHomog y hg)
  rw [map_mul, eval_C, map_prod] at h
  simp only [map_pow, eval_X] at h
  rw [← h, mConeMap, aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp

theorem blockFnField_eq_top {y : (Σ k, ι k) → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hB : Birational y) : blockFnField y = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB x
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have ht : ∏ k, t k ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
  have hw : ∀ p, y p * t p.1 ∈ blockFnField y := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, by simp [t, div_eq_mul_inv]⟩
  have hx : x = aeval (fun p => y p * t p.1) g / aeval (fun p => y p * t p.1) h := by
    rw [aeval_scale hg, aeval_scale hh, hgh, mul_div_mul_right _ _ ht, mul_div_cancel_right₀ _ hh0]
  rw [hx]
  exact div_mem (aeval_mem _ _ hw g) (aeval_mem _ _ hw h)

theorem trdeg_eq {y : (Σ k, ι k) → Ω} {D : ℕ} (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (hB : Birational y) : Algebra.trdeg ℚ Ω = D := by
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = D := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have hE : blockFnField y ≃ₐ[ℤ] Ω :=
    ((IntermediateField.equivOfEq (blockFnField_eq_top c hc hB)).trans
      IntermediateField.topEquiv).toRingEquiv.toIntAlgEquiv
  have h2 : Algebra.trdeg ℤ Ω = D := by rw [← hE.trdeg_eq]; convert h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h2, ← trdeg_add_eq ℤ ℚ (A := Ω), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]


omit [CharZero Ω] in
theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ} {L : Fin (D + 1) → MRing ι}
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hL : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ j, aeval y (L j) ≠ 0 := by
  have hne : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    (RingHom.ker_isPrime (mConeMap y)).ne_top (top_le_iff.mp h)
  obtain ⟨z, hzP, -⟩ := exists_mcPts_not_mem_mcPts hA hne
  obtain ⟨j, hj⟩ := hz z hzP
  refine ⟨j, fun h0 => hj (hzP.2 _ ?_)⟩
  change mConeMap y (L j) = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y (hL j), h0, map_zero, zero_mul]

def dehom {D : ℕ} (j₀ : Fin (D + 1)) (F : MvPolynomial (Fin (D + 1)) ℚ) : MvPolynomial {i // i ≠ j₀} ℚ :=
  bind₁ (fun i => if h : i = j₀ then 1 else X ⟨i, h⟩) F

omit [Field Ω] [CharZero Ω] in
theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℚ A] {D : ℕ} (j₀ : Fin (D + 1))
    (F : MvPolynomial (Fin (D + 1)) ℚ) (u : {i // i ≠ j₀} → A) :
    aeval u (dehom j₀ F) = aeval (fun i => if h : i = j₀ then 1 else u ⟨i, h⟩) F := by
  rw [dehom, aeval_bind₁]
  refine congrArg (fun f => aeval f F) (funext fun i => ?_)
  split_ifs <;> simp

end PullFormsGeneric


open PullFormsGeneric in
theorem PullFormsGeneric.proof (hR : PullRatiosAlgebraic.Statement) : PullFormsGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D e L hA hB he hL hz d F hF h0
  classical
  obtain ⟨j₀, hj₀⟩ := exists_ne_zero hA hL hz
  set a := aeval y (L j₀)
  set r : {i // i ≠ j₀} → Ω := fun i => aeval y (L i.1) / a

  have hP : pullField y L = IntermediateField.adjoin ℚ (Set.range r) := by
    have hw : ∀ i, aeval y (L i) / a ∈ IntermediateField.adjoin ℚ (Set.range r) := by
      intro i
      by_cases h : i = j₀
      · subst h; rw [div_self hj₀]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨i, h⟩, rfl⟩
    apply le_antisymm
    · rw [pullField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, j, hj, rfl⟩
      rw [← div_div_div_cancel_right₀ hj₀]
      exact div_mem (hw i) (hw j)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨i.1, j₀, hj₀, rfl⟩

  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have halg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range r)) Ω := by
    refine ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.mp ?_⟩
    have hle : blockFnField y ≤
        (algebraicClosure (IntermediateField.adjoin ℚ (Set.range r)) Ω).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨p, q, hpq, rfl⟩
      refine (IntermediateField.mem_restrictScalars _).mpr (mem_algebraicClosure_iff.mpr ?_)
      have := hR K ι Ω y D e L hrel' he hL hz p q hpq
      rwa [hP] at this
    have hx := hle ((blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top : x ∈ blockFnField y)
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars _).mp hx)

  have hcard : Cardinal.mk {i : Fin (D + 1) // i ≠ j₀} ≤ Algebra.trdeg ℚ Ω := by
    rw [trdeg_eq ⟨‹_›, ⟨‹_›, ‹_›, hrel⟩, ‹_›, ‹_›⟩ hB, Cardinal.mk_fintype]
    norm_cast
    simp [Fintype.card_subtype_compl]
  have hind : AlgebraicIndependent ℚ r :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ r hcard).1

  have hw : (fun i => if h : i = j₀ then (1 : Ω) else r ⟨i, h⟩) = fun i => aeval y (L i) / a := by
    funext i
    split_ifs with h
    · subst h; exact (div_self hj₀).symm
    · rfl
  have hr0 : aeval r (dehom j₀ F) = 0 := by
    rw [aeval_dehom, hw]
    have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous hF a (fun i => aeval y (L i) / a)
    simp only [mul_div_cancel₀ _ hj₀] at h1
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hj₀)
  have hG : dehom j₀ F = 0 := hind.eq_zero_of_aeval_eq_zero _ hr0

  have hFX : F * X j₀ = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x j₀ = 0
    · rw [hx, mul_zero]
    · have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous (Ω := ℚ) hF (x j₀) (fun i => x i / x j₀)
      have h2 := aeval_dehom j₀ F (fun i => x i.1 / x j₀)
      have hw' : (fun i => if h : i = j₀ then (1 : ℚ) else x i / x j₀) = fun i => x i / x j₀ := by
        funext i
        split_ifs with h
        · subst h; exact (div_self hx).symm
        · rfl
      rw [hG, map_zero, hw'] at h2
      have e1 : eval x F = x j₀ ^ d * eval (fun i => x i / x j₀) F := by
        have hs : (fun j => x j₀ * (x j / x j₀)) = x := funext fun j => mul_div_cancel₀ _ hx
        rw [hs] at h1
        rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
        exact h1
      have e2 : eval (fun i => x i / x j₀) F = 0 := by
        rw [← coe_aeval_eq_eval]
        exact h2.symm
      rw [e1, e2, mul_zero, zero_mul]
  exact (mul_eq_zero.mp hFX).resolve_right (X_ne_zero _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem vanish_of_vanish_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (N : K → ℤ) {q : ℕ}
    (hq : 1 ≤ q)
    (h : ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + (c * q) • N) 1))
    (e : K → ℤ) : ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) := by
  choose c₀ hc₀ using fun r : ℕ => h (e + r • N)
  refine ⟨((Finset.range q).sup c₀ + 1) * q, fun c hc => ?_⟩
  have hr : c % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  have h1 : c₀ (c % q) ≤ (Finset.range q).sup c₀ := Finset.le_sup (f := c₀) hr
  have h2 : (Finset.range q).sup c₀ + 1 ≤ c / q := (Nat.le_div_iff_mul_le (by omega)).mpr hc
  have h3 := hc₀ (c % q) (c / q) (by omega)
  have e' : e + (c % q) • N + (c / q * q) • N = e + c • N := by
    rw [add_assoc, ← add_smul, Nat.mod_add_div' c q]
  rwa [e'] at h3

theorem KleimanVarietyH1Generation.proof (hK : KH.KAmpStatement) (hDev : H1VanishingDevissage.Statement)
    (hGen : GenerationOfH1Vanishing.Statement) : KleimanVarietyH1Generation.Statement := by
  intro F _ K _ _ ι _ _ I Q α b a hI hQ hN hb ha
  refine hGen F K ι Q _ inferInstance (hDev F K ι Q _ inferInstance fun P hP hQP e => ?_)

  obtain ⟨D, hKD, hD⟩ := Targets.ContractMixedField.exists_dim hP
  have hPd : IsProjVarF P (D - Fintype.card K) := ⟨hP, by rw [hD, Nat.sub_add_cancel hKD]⟩
  have hNP : KH.NefOnF I P α := fun W hW hPW => hN W hW (hQP.trans hPW)

  obtain ⟨q, hq, -, hvan⟩ := hK F K ι I P _ α b a hI hPd hNP hb ha
  exact vanish_of_vanish_nsmul _ _ hq hvan e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurveSmallCountLower

theorem statement_iff : CurveSmallCountLower.Statement ↔ Targets.CurveCountLower.Statement :=
  Iff.rfl

end CurveSmallCountLower

theorem CurveSmallCountLower.proof (hD : Targets.CurveDegreeVert.Statement) (hV : Targets.CurveVertIndex.Statement)
    (hL : Targets.CurveIndexLinear.Statement) (hN : Targets.CurveBoxCount.Statement) :
    CurveSmallCountLower.Statement :=
  CurveSmallCountLower.statement_iff.mpr (Targets.CurveCountLower.proof hD hV hL hN)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry



theorem FibreSectionLift.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hsq : KH.CechDSqStatement) (hdg : KH.CechDDegStatement) (hR : ReductionComplex.Statement)
    (hZ : ZeroCocycleSection.Statement) (hC : SecCochReduce.Statement) : FibreSectionLift.Statement := by
  intro K _ _ ι _ _ Ω _ y D p a hV hp hH1
  have hH1' : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) := hH1
  show ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 0,
    ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y (ZMod p) s a = z
  intro z hz'

  let instC : ∀ n : ℕ, Module ℤ (KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) := fun n =>
    (fun {A : Type} {_ : AddCommMonoid A} {i : Module ℤ A} (_ : Submodule ℤ A) => i)
      (KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n)
  let instZ : Module ℤ (KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := Submodule.module _
  let instCp : ∀ n : ℕ, Module (ZMod p) (KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n) :=
    fun n => (fun {A : Type} {_ : AddCommMonoid A} {i : Module (ZMod p) A} (_ : Submodule (ZMod p) A) => i)
      (KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n)
  let instZp : Module (ZMod p) (KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) :=
    Submodule.module _
  let instH : Module ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) :=
    Submodule.Quotient.module _
  obtain ⟨hd, hrd, hon, hker₀, hnzd₀, hkill₀⟩ := hR K ι Ω y D p a hV hp

  have hker : ∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w' := by
    intro n w hw h0
    obtain ⟨w', h1, h2⟩ := hker₀ n w hw h0
    exact ⟨w', h1, by convert h2 using 2⟩
  have hnzd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      (p : ℤ) • w = 0 → w = 0 := fun n w h => hnzd₀ n w (by convert h using 2)
  have hkill : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0 := fun n w => by convert hkill₀ n w using 3
  have hgr : KH.IsMGraded ℤ ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) :=
    hG ℤ K ι _ (by rw [FibreReduction.idealOver_int]; exact hV.2.1.2.1)
  have hfin : Module.Finite ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := by
    exact (hS ℤ K ι _ _ inferInstance inferInstance hgr).1 a 1
  have dd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ (n + 1) (KH.cechD ℤ ι _ n w) = 0 := fun n w =>
    LinearMap.congr_fun (hsq ℤ K ι _ n) w
  have dsmul : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ n ((p : ℤ) • w) = (p : ℤ) • KH.cechD ℤ ι _ n w := fun n w =>
    map_zsmul (KH.cechD ℤ ι _ n).toAddMonoidHom (p : ℤ) w
  have memZ : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n → KH.cechD ℤ ι _ n w = 0 →
        w ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n := fun n w hC hD =>
    Submodule.mem_inf.mpr ⟨hC, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hD⟩

  let f : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 →ₗ[ℤ]
      KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 := LinearMap.lsmul ℤ _ (p : ℤ)
  have hq : ∀ x : KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1,
      f (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((p : ℤ) • x) := fun x => by
    rw [LinearMap.lsmul_apply, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, map_zsmul]
    exact int_smul_eq_zsmul instH (p : ℤ) _
  have hsurj : Function.Surjective f := by
    intro h
    induction h using Submodule.Quotient.induction_on with
    | H x =>
    have hx := Submodule.mem_inf.mp x.2
    have hxd : KH.cechD ℤ ι _ 1 x.1 = 0 := by
      have := hx.2
      rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
    have hrx : FibreReduction.redCoch y p 1 x.1 ∈
        KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1 :=
      Submodule.mem_inf.mpr ⟨hrd 1 _ hx.1, by
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, ← hd, hxd, map_zero]⟩
    have h0' : (Submodule.Quotient.mk ⟨_, hrx⟩ :
        KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) = 0 := Subsingleton.elim _ _
    have h0 := (Submodule.Quotient.mk_eq_zero _).mp h0'
    obtain ⟨u, hu, hdu⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp h0)
    obtain ⟨u', hu', hru'⟩ := hon 0 u hu
    have hdu' := hdg ℤ K ι _ _ a 0 u' hu'
    obtain ⟨x', hx'C, hx'eq⟩ := hker 1 (x.1 - KH.cechD ℤ ι _ 0 u') (sub_mem hx.1 hdu') (by
      rw [map_sub, hd, hru']
      exact sub_eq_zero.mpr hdu.symm)
    have hx'Z := memZ 1 x' hx'C (hnzd 2 _ (by rw [← dsmul, ← hx'eq, map_sub, hxd, dd, sub_self]))
    refine ⟨Submodule.Quotient.mk ⟨x', hx'Z⟩, ?_⟩
    rw [hq, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, map_zsmul]
    refine Submodule.mem_map.mpr ⟨-u', neg_mem hu', ?_⟩
    rw [LinearMap.restrictScalars_apply, map_neg, Submodule.subtype_apply, Submodule.subtype_apply]
    show _ = (p : ℤ) • x' - x.1
    rw [← hx'eq]
    abel
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hsurj

  obtain ⟨w, hwC, hrw⟩ := hon 0 z (Submodule.mem_inf.mp hz').1
  have hzd : KH.cechD (ZMod p) ι _ 0 z = 0 := by
    have := (Submodule.mem_inf.mp hz').2
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
  obtain ⟨w', hw'C, hw'eq⟩ := hker 1 _ (hdg ℤ K ι _ _ a 0 w hwC) (by rw [hd, hrw, hzd])
  have hw'Z := memZ 1 w' hw'C (hnzd 2 _ (by rw [← dsmul, ← hw'eq, dd]))
  have hcls : (Submodule.Quotient.mk ⟨w', hw'Z⟩ : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) = 0 := by
    apply hinj
    rw [map_zero, hq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_zsmul, Submodule.subtype_apply]
    exact Submodule.mem_map.mpr ⟨w, hwC, hw'eq⟩
  obtain ⟨v, hvC, hdv⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hcls))
  have hv0 := memZ 0 (w - (p : ℤ) • v) (sub_mem hwC (zsmul_mem hvC _)) (by
    rw [map_sub, dsmul]
    rw [LinearMap.restrictScalars_apply] at hdv
    rw [hdv]
    exact sub_eq_zero.mpr hw'eq)
  obtain ⟨s, hs, hsv⟩ := hZ K ι Ω y a _ hv0
  refine ⟨s, hs, ?_⟩
  rw [← hC K ι Ω y p a s hs, hsv, map_sub, hkill, sub_zero, hrw]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
