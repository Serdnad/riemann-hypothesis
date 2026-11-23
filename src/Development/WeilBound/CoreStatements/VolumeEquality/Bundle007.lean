module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle011
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

@[expose] public section

section

noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type}
  [∀ b, Fintype (ι' b)]

theorem ne_of_arith {Ω : Type} [Field Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

theorem arith_of_isPt [Nonempty K] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsPt ℚ y d) :
    IsArithVar (mCoordIdeal y) (d + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : ‹Algebra ℚ Ω› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  choose c hc using h1
  have hF : fnField ℚ y ≤ IntermediateField.adjoin ℚ (coneRatios y c) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨k, i⟩, ⟨k', j⟩, e, rfl⟩
    obtain rfl : k = k' := e
    have : y ⟨k, i⟩ / y ⟨k, j⟩ = (y ⟨k, i⟩ / y ⟨k, c k⟩) / (y ⟨k, j⟩ / y ⟨k, c k⟩) := by
      rw [div_div_div_cancel_right₀ (hc k)]
    rw [SetLike.mem_coe, this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, rfl⟩)
  have hA : Algebra.IsAlgebraic (Algebra.adjoin ℚ (fnField ℚ y : Set Ω)) Ω := by
    have e : Algebra.adjoin ℚ (fnField ℚ y : Set Ω) = (fnField ℚ y).toSubalgebra := Algebra.adjoin_eq (fnField ℚ y).toSubalgebra
    rw [e]
    exact inferInstanceAs (Algebra.IsAlgebraic (fnField ℚ y) Ω)
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℚ) (fnField ℚ y : Set Ω)
  have hc' : Cardinal.mk t = d := hb.cardinalMk_eq_trdeg.trans h3
  obtain ⟨e⟩ : Nonempty (Fin d ≃ t) := Cardinal.eq.1 (by simp [hc'])
  have hb' := hb.comp_equiv e
  have := hb'.isAlgebraic_field
  exact CoordConeArithVar.proof IntDomainDim.full K ι Ω y c d _ inferInstance hc hb'.1 (fun i => hF (ht (e i).2))
    fun r _ => Algebra.IsAlgebraic.isAlgebraic r

theorem mem_of_birational {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω) {y : (Σ b, ι b) → Ω₁} (hb : Birational y)
    (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) (F : Subfield Ω) (hF : ∀ k j j', i (y ⟨k, j⟩) / i (y ⟨k, j'⟩) ∈ F) (s : Ω₁) : i s ∈ F := by
  choose c hc using hne
  have key : ∀ (g : MRing ι) (d : K → ℕ), IsMultiHomog g d → i (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) ∈ F := by
    intro g d hg
    have h1 : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
      have h := congrArg (eval fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap_of_isMultiHomog y hg)
      have h' : (eval fun k => (y ⟨k, c k⟩)⁻¹).comp (mConeMap y : MRing ι →+* MvPolynomial K Ω₁) =
          ((aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω₁) : MRing ι →+* Ω₁) := by
        refine ringHom_ext (fun c => by simp) fun p => ?_
        simp [mConeMap, div_eq_mul_inv]
      have h'' := DFunLike.congr_fun h' g
      simp only [RingHom.comp_apply, RingHom.coe_coe] at h''
      rw [← h'', h, map_mul, eval_C]
      simp [div_eq_mul_inv]
    rw [h1]
    clear h1 hg
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simpa using add_mem hf hg
    | mul_X f p hf => simpa using mul_mem hf (hF p.1 p.2 (c p.1))
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hb s
  have hp : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have : s = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) / (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k) := by
    rw [div_div_div_cancel_right₀ hp, e, mul_div_cancel_right₀ _ h0]
  rw [this, map_div₀]
  exact div_mem (key g d hg) (key h d hh)

variable {Ω₁ : Type} [Field Ω₁] [Algebra ℚ Ω₁] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra Ω₁ Ω]

theorem fnField_join {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield = (fnField Ω₁ y').toSubfield := by
  apply le_antisymm
  · rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨⟨k | k, j⟩, ⟨k', j'⟩, e, rfl⟩)
    · simp
    · obtain rfl : Sum.inl k = k' := e
      exact div_mem ((fnField Ω₁ y').algebraMap_mem _) ((fnField Ω₁ y').algebraMap_mem _)
    · obtain rfl : Sum.inr k = k' := e
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, ⟨k, j'⟩, rfl, rfl⟩
  · rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨s, rfl⟩ | ⟨⟨k, j⟩, ⟨k', j'⟩, e, rfl⟩)
    · refine mem_of_birational _ hb hne _ (fun k j j' => ?_) s
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨.inl k, j⟩, ⟨.inl k, j'⟩, rfl, rfl⟩
    · obtain rfl : k = k' := e
      exact IntermediateField.subset_adjoin _ _ ⟨⟨.inr k, j⟩, ⟨.inr k, j'⟩, rfl, rfl⟩

theorem finrank_join {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')) Ω = Module.finrank (fnField Ω₁ y') Ω := by
  show Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield Ω =
    Module.finrank (fnField Ω₁ y').toSubfield Ω
  rw [fnField_join y' hb hne]

theorem isPt_join {y : (Σ b, ι b) → Ω₁} {y' : (Σ b, ι' b) → Ω} {n r : ℕ} (hb : Birational y)
    (ha : IsArithVar (mCoordIdeal y) (n + 1)) (h : IsPt Ω₁ y' r) :
    IsPt ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y') (n + r) := by
  have hne := ne_of_arith ha
  refine ⟨?_, ?_, ?_⟩
  · rintro (k | k)
    · obtain ⟨j, hj⟩ := hne k
      exact ⟨j, (map_ne_zero (algebraMap Ω₁ Ω)).2 hj⟩
    · exact h.1 k
  · have := h.2.1
    exact Module.finite_of_finrank_pos (by rw [finrank_join y' hb hne]; exact Module.finrank_pos)
  · have h1 := FnFieldTrdeg.full K ι Ω₁ y n hb ha
    have : CharZero Ω₁ := algebraRat.charZero Ω₁
    have : IsScalarTower ℤ ℚ Ω₁ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : IsScalarTower ℚ Ω₁ Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have h2 := trdeg_add_eq ℤ ℚ (A := Ω₁)
    rw [trdeg_eq_zero, zero_add, h1] at h2
    rw [← trdeg_add_eq ℚ Ω₁ (A := Ω), h2, h.2.2, Nat.cast_add]

end SheetDecomposition.PF
end
end

section

noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal pointConeMap intNum)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

theorem pointIdeal_rat {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] (y : (Σ b, ι b) → Ω) :
    pointIdeal ℚ y = (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  have hcomp : ∀ F : MRing ι, pointConeMap ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = mConeMap y F := by
    intro F
    simp only [pointConeMap, mConeMap, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have key : ∀ G : MvPolynomial (Σ b, ι b) ℚ, ∃ n : ℕ, 0 < n ∧ ∃ F : MRing ι,
      MvPolynomial.map (Int.castRingHom ℚ) F = (n : MvPolynomial (Σ b, ι b) ℚ) * G := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a =>
      refine ⟨a.den, a.pos, C a.num, ?_⟩
      rw [map_C, ← map_natCast (C : ℚ →+* MvPolynomial (Σ b, ι b) ℚ), ← C_mul, Rat.den_mul_eq_num]
      rfl
    | add p q hp hq =>
      obtain ⟨n, hn, F, hF⟩ := hp
      obtain ⟨n', hn', F', hF'⟩ := hq
      refine ⟨n * n', Nat.mul_pos hn hn', C (n' : ℤ) * F + C (n : ℤ) * F', ?_⟩
      rw [map_add (f := _), map_mul, map_mul, hF, hF', map_C, map_C]
      simp only [eq_intCast, Int.cast_natCast, map_natCast, Nat.cast_mul]
      ring
    | mul_X p j hp =>
      obtain ⟨n, hn, F, hF⟩ := hp
      exact ⟨n, hn, F * X j, by rw [map_mul, map_X, hF, mul_assoc]⟩
  apply le_antisymm
  · intro G hG
    obtain ⟨n, hn, F, hF⟩ := key G
    have hG0 : pointConeMap ℚ y G = 0 := hG
    have hFker : F ∈ mCoordIdeal y := by
      show mConeMap y F = 0
      rw [← hcomp, hF, map_mul, hG0, mul_zero]
    have hGeq : G = C ((n : ℚ)⁻¹) * MvPolynomial.map (Int.castRingHom ℚ) F := by
      rw [hF, ← mul_assoc, ← map_natCast (C : ℚ →+* MvPolynomial (Σ b, ι b) ℚ), ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hn.ne'), C_1, one_mul]
    rw [hGeq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFker)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    show pointConeMap ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = 0
    rw [hcomp]
    exact hF

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem pointIdeal_map {R Ω₂ Ω : Type} [CommRing R] [Field Ω₂] [Field Ω] [Algebra R Ω₂] [Algebra R Ω] (i : Ω₂ →ₐ[R] Ω)
    (y : (Σ b, ι b) → Ω₂) : pointIdeal R (fun x => i (y x)) = pointIdeal R y := by
  have h : (MvPolynomial.mapAlgHom i).comp (pointConeMap R y) = pointConeMap R (fun x => i (y x)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap]
  ext F
  change pointConeMap R (fun x => i (y x)) F = 0 ↔ pointConeMap R y F = 0
  rw [← h, AlgHom.comp_apply]
  constructor
  · intro h0
    apply MvPolynomial.map_injective (i : Ω₂ →+* Ω) i.toRingHom.injective
    rw [map_zero]
    exact h0
  · intro h0
    rw [h0, map_zero]

theorem ne_of_arith {Ω : Type} [Field Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (b : K) :
    ∃ j, y ⟨b, j⟩ ≠ 0 := by
  obtain ⟨j, hj⟩ := h.2.1.2.2 b
  refine ⟨j, fun h0 => hj ?_⟩
  show mConeMap y (X ⟨b, j⟩) = 0
  simp [mConeMap, h0]

theorem range_le_fnField {Ω₂ Ω : Type} [Field Ω₂] [Field Ω] (i : Ω₂ →+* Ω) {y : (Σ b, ι b) → Ω₂} (hb : Birational y)
    (hy : ∀ b, ∃ j, y ⟨b, j⟩ ≠ 0) (k : Type) [Field k] [Algebra k Ω] :
    i.fieldRange ≤ (fnField k fun x => i (y x)).toSubfield := by
  choose c hc using hy
  have htop := BirationalRatioClosure.full K ι Ω₂ y c hb hc
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ Subfield.closure (GroundTheory.Heights₂.Heights.coneRatios y c) := htop ▸ Subfield.mem_top s
  have hle : Subfield.closure (GroundTheory.Heights₂.Heights.coneRatios y c) ≤
      (fnField k fun x => i (y x)).toSubfield.comap i := by
    rw [Subfield.closure_le]
    rintro _ ⟨p, rfl⟩
    show i (y p / y ⟨p.1, c p.1⟩) ∈ (fnField k fun x => i (y x)).toSubfield
    rw [map_div₀]
    exact IntermediateField.subset_adjoin k _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  exact hle hs

private theorem finiteDimensional_of_subfield_le {Ω : Type} [Field Ω] (S T : Subfield Ω) (h : S ≤ T) [FiniteDimensional S Ω] :
    FiniteDimensional T Ω := by
  letI : Algebra S T := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower S T Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.Finite.of_restrictScalars_finite S T Ω

private theorem trdeg_eq_of_finrank_fieldRange_pos {Ω₂ Ω : Type} [Field Ω₂] [Field Ω] [Algebra ℚ Ω₂] [Algebra ℚ Ω] (i : Ω₂ →+* Ω)
    (d : ℕ) (hZ : Algebra.trdeg ℤ Ω₂ = d) (hfin : 0 < Module.finrank i.fieldRange Ω) :
    Algebra.trdeg ℚ Ω = d := by
  have hQ : Algebra.trdeg ℚ Ω₂ = d := by
    haveI := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have h := _root_.trdeg_add_eq ℤ ℚ (A := Ω₂)
    rw [_root_.trdeg_eq_zero, zero_add, hZ] at h
    exact h
  letI : Algebra Ω₂ Ω := i.toAlgebra
  haveI : IsScalarTower ℚ Ω₂ Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : Algebra Ω₂ i.fieldRange := i.rangeRestrictField.toAlgebra
  haveI : IsScalarTower Ω₂ i.fieldRange Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite i.fieldRange Ω := Module.finite_of_finrank_pos hfin
  haveI : Module.Finite Ω₂ i.fieldRange := by
    refine Module.Finite.of_surjective (Algebra.linearMap Ω₂ i.fieldRange) ?_
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := RingHom.mem_fieldRange.1 hz
    exact ⟨x, Subtype.ext rfl⟩
  haveI : Module.Finite Ω₂ Ω := Module.Finite.trans i.fieldRange Ω
  have h := _root_.trdeg_add_eq ℚ Ω₂ (A := Ω)
  rw [_root_.trdeg_eq_zero (R := Ω₂) (A := Ω), add_zero, hQ] at h
  exact h.symm

theorem numMap : NumMap := by
  intro Ω₂ _ _ Ω _ _ i K _ ι _ y d hb har hfin
  have hy : ∀ b, ∃ j, y ⟨b, j⟩ ≠ 0 := ne_of_arith har
  have hiy : ∀ b, ∃ j, i (y ⟨b, j⟩) ≠ 0 := fun b => by
    obtain ⟨j, hj⟩ := hy b
    exact ⟨j, (map_ne_zero i).2 hj⟩
  haveI : FiniteDimensional i.fieldRange Ω := Module.finite_of_finrank_pos hfin
  have hFD : ∀ (k : Type) [Field k] [Algebra k Ω], FiniteDimensional (fnField k fun x => i (y x)) Ω := by
    intro k _ _
    haveI := finiteDimensional_of_subfield_le i.fieldRange _ (range_le_fnField i hb hy k)
    exact this
  have heq : (fnField ℚ fun x => i (y x)).toSubfield = i.fieldRange := by
    refine le_antisymm ?_ (range_le_fnField i hb hy ℚ)
    rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨p, p', _, rfl⟩)
    · exact RingHom.mem_fieldRange.2 ⟨algebraMap ℚ Ω₂ q, by simp⟩
    · exact RingHom.mem_fieldRange.2 ⟨y p / y p', by rw [map_div₀]⟩
  have hrank : Module.finrank (fnField ℚ fun x => i (y x)) Ω = Module.finrank i.fieldRange Ω := by
    rw [show Module.finrank (fnField ℚ fun x => i (y x)) Ω =
      Module.finrank (fnField ℚ fun x => i (y x)).toSubfield Ω from rfl, heq]
  have hpi : pointIdeal ℚ (fun x => i (y x)) = pointIdeal ℚ y := pointIdeal_map i.toRatAlgHom y
  refine ⟨⟨hiy, hFD ℚ, trdeg_eq_of_finrank_fieldRange_pos i d (FnFieldTrdeg.full K ι Ω₂ y d hb har) hfin⟩, hFD, fun a => ?_, fun a => ?_⟩
  · simp only [num, inum]
    rw [hrank, hpi]
  · simp only [inum, GroundTheory.Heights₂.Heights.HilbertSamuel.genDeg]
    rw [pointIdeal_rat]

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem null_of_lines {n : ℕ} (Z : Set (Fin n → ℂ)) (hZ : MeasurableSet Z) (p : Fin n → ℂ)
    (h : ∀ x : Fin n → ℂ, ∀ᵐ t : ℝ, p + t • x ∉ Z) : volume Z = 0 := by
  have hm : MeasurableSet {u : (Fin n → ℂ) × ℝ | p + u.2 • u.1 ∉ Z} :=
    (hZ.compl).preimage (f := fun u : (Fin n → ℂ) × ℝ => p + u.2 • u.1) (Continuous.measurable (by fun_prop))
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ x : Fin n → ℂ, p + t • x ∉ Z :=
    (Measure.ae_ae_comm (p := fun (x : Fin n → ℂ) (t : ℝ) => p + t • x ∉ Z) hm).mp (Eventually.of_forall h)
  have h2 : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff]
  obtain ⟨t, ht, ht0⟩ := (h1.and h2).exists
  have h3 : volume ((t • ·) ⁻¹' ((p + ·) ⁻¹' Z)) = 0 := by
    rw [ae_iff] at ht
    simpa [Set.preimage] using ht
  rw [Measure.addHaar_preimage_smul volume ht0, measure_preimage_add, mul_eq_zero] at h3
  refine h3.resolve_left ?_
  rw [ENNReal.ofReal_eq_zero, not_le, abs_pos]
  exact inv_ne_zero (pow_ne_zero _ ht0)

theorem zero_set_null {n : ℕ} (V : Set (Fin n → ℂ)) (hV : IsOpen V) (hc : Convex ℝ V) (f : (Fin n → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f V) (p : Fin n → ℂ) (hp : p ∈ V) (hfp : f p ≠ 0) : volume {x ∈ V | f x = 0} = 0 := by
  have hm : MeasurableSet {x ∈ V | f x = 0} := by
    have : {x ∈ V | f x = 0} = V \ (V ∩ f ⁻¹' {0}ᶜ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      tauto
    rw [this]
    exact hV.measurableSet.diff (hf.continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton).measurableSet
  refine null_of_lines _ hm p fun x => ?_
  set S : Set ℝ := (fun t : ℝ => p + t • x) ⁻¹' V with hS
  have hSo : IsOpen S := hV.preimage (by fun_prop)
  have hSc : Convex ℝ S := by
    intro s hs t ht a b ha hb hab
    have := hc hs ht ha hb hab
    have e : a • (p + s • x) + b • (p + t • x) = p + (a • s + b • t) • x := by
      have : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
      conv_rhs => rw [this]
      simp only [smul_add, add_smul, smul_assoc]
      abel
    rw [e] at this
    exact this
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => f (p + s • x)) ((fun s : ℂ => p + s • x) ⁻¹' V) := by
    refine DifferentiableOn.analyticOnNhd ?_ (hV.preimage (by fun_prop))
    exact hf.comp (by fun_prop) fun s hs => hs
  have hh : AnalyticOnNhd ℝ (fun t : ℝ => f (p + t • x)) S := by
    intro t ht
    have h1 : AnalyticAt ℝ (fun s : ℂ => f (p + s • x)) (Complex.ofRealCLM t) :=
      (hg t (by simpa [hS] using ht)).restrictScalars
    have := h1.comp (Complex.ofRealCLM.analyticAt t)
    simpa [Function.comp_def] using this
  rcases hh.eqOn_zero_or_eventually_ne_zero_of_preconnected hSc.isPreconnected with h0 | h0
  · exact (hfp (by simpa using h0 (x := 0) (by simpa [hS] using hp))).elim
  · have h1 : ∀ᵐ t ∂(volume.restrict S), f (p + t • x) ≠ 0 := ae_restrict_le_codiscreteWithin hSo.measurableSet h0
    rw [ae_restrict_iff' hSo.measurableSet] at h1
    filter_upwards [h1] with t ht hz using ht hz.1 hz.2

theorem top_le_iff_pt {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (q : Sp ℂ) : ⊤ ≤ x ⁻¹ᵁ U ↔ x q ∈ U := by
  refine ⟨fun h => h (x := q) trivial, fun h q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) q' q
  rw [this]
  exact h

theorem local_null {X : Scheme.{0}} {n : ℕ} {B : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (U : X.Opens)
    (hy : IsHolTo B y) {b : Fin n → ℂ} (hb : b ∈ B) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ b ∈ V ∧ V ⊆ B ∧
      ((∃ b' ∈ V, ⊤ ≤ y b' ⁻¹ᵁ U) → volume {b' ∈ V | ¬ ⊤ ≤ y b' ⁻¹ᵁ U} = 0) := by
  let q : Sp ℂ := (default : PrimeSpectrum ℂ)
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y b q) (U := ⊤) trivial
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hy W 0).1 b ⟨hb, (top_le_iff_pt _ _ q).mpr hbW⟩
  refine ⟨Metric.ball b ε, Metric.isOpen_ball, Metric.mem_ball_self hε, fun z hz => (hball hz).1, ?_⟩
  rintro ⟨b', hb', hU⟩
  obtain ⟨f, hfU, hf⟩ := hW.exists_basicOpen_le (V := U) ⟨y b' q, (top_le_iff_pt _ _ q).mp hU⟩
    ((top_le_iff_pt _ _ q).mp (hball hb').2)
  refine measure_mono_null ?_ (zero_set_null (Metric.ball b ε) Metric.isOpen_ball (convex_ball b ε)
    (fun z => valAt' (y z) W f) ((hy W f).2.mono hball) b' hb' ((valAt'_ne_zero_iff _ _ (hball hb').2 f q).mpr hf))
  rintro z ⟨hz, hzU⟩
  refine ⟨hz, ?_⟩
  by_contra hne
  exact hzU ((top_le_iff_pt _ _ q).mpr (hfU ((valAt'_ne_zero_iff _ _ (hball hz).2 f q).mp hne)))

theorem holNull : HolNull := by
  intro X n B y U _ hBc hy ⟨b₀, hb₀, hU₀⟩
  choose! V hVo hVb hVB hV using fun b (hb : b ∈ B) => local_null U hy hb
  set G : Set (Fin n → ℂ) := {b | ⊤ ≤ y b ⁻¹ᵁ U} with hG
  have hsub : B ⊆ interior (closure G) := by
    refine hBc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr fun z hz hz' => hz' (interior_subset hz)) (fun b hb => ?_) ?_ |>.trans le_rfl
    · by_cases hcl : b ∈ closure G
      · left
        refine interior_maximal (t := V b) (fun z hz => ?_) (hVo b hb) (hVb b hb)
        obtain ⟨b', hb'V, hb'G⟩ := mem_closure_iff.mp hcl (V b) (hVo b hb) (hVb b hb)
        have hnull := hV b hb ⟨b', hb'V, hb'G⟩
        by_contra hz'
        have ho : IsOpen (V b ∩ (closure G)ᶜ) := (hVo b hb).inter isClosed_closure.isOpen_compl
        refine (ho.measure_pos volume ⟨z, hz, hz'⟩).ne' (measure_mono_null ?_ hnull)
        exact fun w hw => ⟨hw.1, fun h => hw.2 (subset_closure h)⟩
      · exact Or.inr hcl
    · refine ⟨b₀, hb₀, interior_maximal (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}) (fun z hz => subset_closure hz.2) (hy U 0).1 ⟨hb₀, hU₀⟩⟩
  refine measure_null_of_locally_null _ fun b hb => ?_
  obtain ⟨b', hb'V, hb'G⟩ := mem_closure_iff.mp (interior_subset (hsub hb.1)) (V b) (hVo b hb.1) (hVb b hb.1)
  refine ⟨{b' ∈ V b | ¬ ⊤ ≤ y b' ⁻¹ᵁ U}, ?_, hV b hb.1 ⟨b', hb'V, hb'G⟩⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((hVo b hb.1).mem_nhds (hVb b hb.1))] with z hz hz'
    using ⟨hz', hz.2⟩

end SheetDecomposition
end
end
