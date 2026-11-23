module

public import Development.EtaleCohomology.EtaleSheaves.Bundle056
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Development.EtaleCohomology.EtaleSheaves.Bundle057
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.EtaleCohomology.EtaleSheaves.Bundle058
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafTripleFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  rw [← Spec.map_comp]
  rfl

theorem pb_lift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {f : D ⟶ Sp R} {v : C ⟶ D} (hs : IsPullback v c f (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w)) c
      (pullback.snd f (incl h)) (toR R') := by
  have e1 : pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ pullback.fst f (incl h) = v :=
    pullback.lift_fst _ _ _
  have t : IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫
      pullback.fst f (incl h)) c f (toR R' ≫ incl h) := by rw [e1, toR_incl]; exact hs
  exact IsPullback.of_right t (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (incl h))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def LeafPairRel : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → ∀ (hs : IsPullback v0 c0 q (toR R)),
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (E1 : Scheme.{0}) (e1 : E1 ⟶ pullback q (incl h)) (w1 : C1 ⟶ E1),
      FP (e1 ≫ pullback.snd q (incl h)) ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ pullback.snd q (incl h)) (toR R') ∧
      γ1 ≫ pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) = w1 ≫ e1

theorem tripleDescent_of_pairRelation (hR : LeafPairRel) : LeafTripleFP := by
  intro k _ Ω _ _ R hRfg C0 C1 C2 c0 γ1 γ2 h2 D0 D1 q d1 v0 v1 hq hq1 hs0 hs1 hc
  obtain ⟨R', h, hR', E2, e2, w2, hf2, hs2, hc2⟩ :=
    hR k Ω R hRfg (γ1 ≫ c0) γ2 h2 (d1 ≫ q) v1 hq1 hs1
  have hsnd : pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]) ≫
      pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR', _, _, _, pullback.snd q (incl h),
    pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]), e2,
    pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs0.w),
    pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs1.w), w2, ?_⟩
  refine ⟨fp_snd _ _ hq, ?_, ?_, pb_lift h hs0, ?_, ?_, ?_, hc2⟩
  · rw [hsnd]; exact fp_snd _ _ hq1
  · rw [hsnd]; exact hf2
  · rw [hsnd]; exact pb_lift h hs1
  · rw [hsnd]; exact hs2
  · apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hc]
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]

end LateralTheory.E.LeafTripleFPPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafRelDimOnePf

theorem exists_ne_generic {C : Scheme.{0}} [IsIntegral C] (hd : topologicalKrullDim C = 1) :
    ∃ x : C, x ≠ genericPoint C := by
  by_contra h
  push Not at h
  have : Subsingleton C := ⟨fun a b => (h a).trans (h b).symm⟩
  have : DiscreteTopology C := inferInstance
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hd] at this
  exact absurd this (by decide)

theorem isField_top (Ω : Type) [Field Ω] : IsField Γ(Sp Ω, ⊤) :=
  MulEquiv.isField (Field.toIsField Ω)
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv

theorem chart (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [IsIntegral C]
    (hd : topologicalKrullDim C = 1) (U : (Sp Ω).Opens) (V : C.Opens) (hV : IsAffineOpen V)
    (x : C) (hx : x ∈ V) (hxη : x ≠ genericPoint C) (e : V ≤ c ⁻¹ᵁ U)
    (hs : (c.appLE U V e).hom.IsStandardSmooth) :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (c.appLE U V e).hom := by
  have hU : U = ⊤ := by
    ext p
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : p = c x := Subsingleton.elim _ _
    subst this
    exact e hx
  subst hU
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let : Field Γ(Sp Ω, ⊤) := (isField_top Ω).toField
  let : Algebra Γ(Sp Ω, ⊤) Γ(C, V) := (c.appLE ⊤ V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  have : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp Ω, ⊤) Γ(C, V) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have h1 := GlobalTheory.AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := Γ(Sp Ω, ⊤)) (A := Γ(C, V))
    (d := P.dimension)
  have hle : ringKrullDim Γ(C, V) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hd]
    exact hV.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
  have hne : ringKrullDim Γ(C, V) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 Γ(C, V) := Ring.krullDimLE_iff.mpr (by rw [h0]; rfl)
    have hF := Ring.KrullDimLE.isField_of_isDomain (R := Γ(C, V))
    let := hF.toField
    have hη : genericPoint C ∈ V :=
      ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x, by simp, hx⟩
    have hx' : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hx
    have hη' : genericPoint C ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hη
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, hb⟩ := hη'
    apply hxη
    rw [← hb]
    have key : ∀ p : PrimeSpectrum Γ(C, V), p.asIdeal = ⊥ := by
      intro p
      have hp := p.isPrime
      exact Ideal.eq_bot_of_prime _
    congr 1
    exact PrimeSpectrum.ext ((key a).trans (key b).symm)
  rw [h1] at hle hne
  have h2 : P.dimension ≤ 1 := by exact_mod_cast hle
  have h3 : P.dimension ≠ 0 := by exact_mod_cast hne
  exact P.isStandardSmoothOfRelativeDimension (by omega)

theorem LeafRelDimOne_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafRelDimOne := by
  intro Ω _ C c hC hs hd
  obtain ⟨x₀, hx₀⟩ := exists_ne_generic hd
  constructor
  intro y
  by_cases hy : y = genericPoint C
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c x₀
    have hyV : y ∈ V := hy ▸ ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr ⟨x₀, by simp, hx⟩
    exact ⟨U, hU, V, hV, hyV, e, chart Ω c hd U V hV x₀ hx hx₀ e h⟩
  · obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth c y
    exact ⟨U, hU, V, hV, hx, e, chart Ω c hd U V hV y hx hy e h⟩

end LateralTheory.E.LeafRelDimOnePf
end
end

section

noncomputable section
open Polynomial

namespace LateralTheory.E.LeafIntClosureAlgPf
open LateralTheory.E.LeafNormalModelPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L]

theorem isAlgebraic_of_mem_adjoin (u x : L) (hx : x ∈ IntermediateField.adjoin Ω {u}) :
    IsAlgebraic (Algebra.adjoin Ω {u}) x := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (F := Ω) (α := u) x).1 hx
  set R := Algebra.adjoin Ω {u}
  have hr : aeval u r ∈ R := by rw [show R = _ from Algebra.adjoin_singleton_eq_range_aeval Ω u]; exact ⟨r, rfl⟩
  have hs : aeval u s ∈ R := by rw [show R = _ from Algebra.adjoin_singleton_eq_range_aeval Ω u]; exact ⟨s, rfl⟩
  by_cases h0 : aeval u s = 0
  · rw [h0, div_zero]; exact isAlgebraic_zero
  refine ⟨C (⟨aeval u s, hs⟩ : R) * X - C ⟨aeval u r, hr⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun p => p.coeff 1) h
    simp only [coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C, one_ne_zero, if_false,
      sub_zero, coeff_zero] at this
    exact h0 (congrArg Subtype.val this)
  · simp only [map_sub, map_mul, aeval_C, aeval_X]
    change aeval u s * (aeval u r / aeval u s) - aeval u r = 0
    rw [mul_div_cancel₀ _ h0, sub_self]

variable (Ω) in
theorem isAlgebraic_adjoin (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    Algebra.IsAlgebraic (Algebra.adjoin Ω {u}) L := by
  constructor
  intro z
  set K := IntermediateField.adjoin Ω {u}
  have h1 : IsAlgebraic K z := Algebra.IsAlgebraic.isAlgebraic z
  have h2 : IsAlgebraic K.toSubalgebra z := h1
  have h3 : IsAlgebraic (Algebra.adjoin Ω (K : Set L)) z :=
    h2.tower_top_of_subalgebra_le (fun y hy => Algebra.subset_adjoin hy)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic (fun y hy => ?_) h3
  exact isAlgebraic_of_mem_adjoin u y hy.1

variable (Ω) in
theorem isFractionRing_intClosure (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    IsFractionRing (integralClosure (Algebra.adjoin Ω {u}) L) L := by
  have := isAlgebraic_adjoin Ω u
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨y, hy, hint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin Ω {u}) z).exists_integral_multiple
  have hy' : (y : L) ≠ 0 := fun h => hy (Subtype.ext h)
  refine ⟨⟨y • z, hint⟩, ⟨(y : L), isIntegral_algebraMap (R := Algebra.adjoin Ω {u}) (x := y)⟩, ?_⟩
  change z = y • z / (y : L)
  rw [Algebra.smul_def]
  change z = (y : L) * z / (y : L)
  field_simp

variable (Ω) in
theorem isIntegrallyClosed_intClosure (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    IsIntegrallyClosed (integralClosure (Algebra.adjoin Ω {u}) L) := by
  have := isFractionRing_intClosure Ω u
  rw [isIntegrallyClosed_iff L]
  intro x hx
  set_option synthInstance.maxHeartbeats 200000 in
    exact ⟨⟨x, isIntegral_trans (A := integralClosure (Algebra.adjoin Ω {u}) L) x hx⟩, rfl⟩

theorem ringKrullDim_intClosure (u : L) (hu : Transcendental Ω u) :
    ringKrullDim (integralClosure (Algebra.adjoin Ω {u}) L) = 1 := by
  have h1 := ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := Algebra.adjoin Ω {u})
    (B := integralClosure (Algebra.adjoin Ω {u}) L) (fun a b h => Subtype.ext (congrArg (Subtype.val : integralClosure (Algebra.adjoin Ω {u}) L → L) h))
  have h2 := ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental Ω u hu).toRingEquiv
  rw [h1, ← h2]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField Ω)

def LeafIntClFinite : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Module.Finite (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L)

theorem finiteType_intCl (u : L) (h : Module.Finite (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L)) :
    Algebra.FiniteType Ω (intCl Ω u) := by
  have h1 : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    (Subalgebra.fg_iff_finiteType _).1 ⟨{u}, by rw [Finset.coe_singleton]⟩
  have h2 : Algebra.FiniteType (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L) := inferInstance
  have h3 : Algebra.FiniteType Ω (integralClosure (Algebra.adjoin Ω {u}) L) :=
    Algebra.FiniteType.trans (S := Algebra.adjoin Ω {u}) h1 h2
  exact h3

theorem LeafIntClosureAlg_of (h : LeafIntClFinite) : LeafIntClosureAlg := by
  intro Ω L _ _ _ u hu hfd
  refine ⟨finiteType_intCl u (h Ω L u hu hfd), ?_, ?_, ?_⟩
  · exact isIntegrallyClosed_intClosure Ω u
  · exact ringKrullDim_intClosure u hu
  · exact isFractionRing_intClosure Ω u

end LateralTheory.E.LeafIntClosureAlgPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGlueProperPf

structure Glued (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hAD : A ≤ D) (hBD : B ≤ D) where
  C0 : Scheme.{0}
  c0 : C0 ⟶ Sp Ω
  iA : Sp A ⟶ C0
  iB : Sp B ⟶ C0
  hiA : IsOpenImmersion iA
  hiB : IsOpenImmersion iB
  hcA : iA ≫ c0 = Spec.map (CommRingCat.ofHom (algebraMap Ω A))
  hcB : iB ≫ c0 = Spec.map (CommRingCat.ofHom (algebraMap Ω B))
  agree : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom) ≫ iA =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBD).toRingHom) ≫ iB
  cover : Set.range iA.base ∪ Set.range iB.base = Set.univ
  inter : Set.range iA.base ∩ Set.range iB.base =
    Set.range (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hAD).toRingHom) ≫ iA).base

def GH (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) : Prop :=
  u ≠ 0 ∧ u ∈ A ∧ u⁻¹ ∈ B ∧ Algebra.FiniteType Ω A ∧ Algebra.FiniteType Ω B ∧
  IsIntegrallyClosed A ∧ IsIntegrallyClosed B ∧ ringKrullDim A = 1 ∧ ringKrullDim B = 1 ∧
  IsFractionRing A L ∧ IsFractionRing B L ∧
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u}) ∧
  (∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) → (A : Set L) ⊆ V ∨ (B : Set L) ⊆ V)

abbrev Dr (Ω : Type) {L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) (u : L) : Subalgebra Ω L :=
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹})

theorem le_Dr_A {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) (u : L) : A ≤ Dr Ω A u :=
  fun x hx => Algebra.subset_adjoin (Set.mem_union_left _ hx)

theorem le_Dr_B {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
    (h : Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u})) : B ≤ Dr Ω A u := by
  intro x hx
  show x ∈ Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹})
  rw [h]; exact Algebra.subset_adjoin (Set.mem_union_left _ hx)

def LeafGlueExists : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u), Nonempty (Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1))

def LeafGlueIntegral : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsIntegral G.C0

def LeafGlueNormal : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ∀ y : G.C0, IsIntegrallyClosed (G.C0.presheaf.stalk y)

def LeafGlueDim : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  topologicalKrullDim G.C0 = 1

def LeafGlueIsProper : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsProper G.c0

def LeafGlueGeneric : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ∃ (x : G.C0) (ψ : Spec (G.C0.presheaf.stalk x) ⟶ Sp L), IsGenericPoint x (⊤ : Set G.C0) ∧
    ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = G.C0.fromSpecStalk x ≫ G.c0

theorem LeafGlueProper_of (h1 : LeafGlueExists) (h2 : LeafGlueIntegral) (h3 : LeafGlueNormal) (h4 : LeafGlueDim)
    (h5 : LeafGlueIsProper) (h6 : LeafGlueGeneric) : LateralTheory.E.LeafNormalModelPf.LeafGlueProper := by
  intro Ω L _ _ _ A B u hu huA huB hfA hfB hicA hicB hdA hdB hfrA hfrB hadj hV
  have h : GH Ω L A B u := ⟨hu, huA, huB, hfA, hfB, hicA, hicB, hdA, hdB, hfrA, hfrB, hadj, hV⟩
  obtain ⟨G⟩ := h1 Ω L A B u h
  obtain ⟨x, ψ, hx, hψ⟩ := h6 Ω L A B u h G
  exact ⟨G.C0, G.c0, x, ψ, h2 Ω L A B u h G, h5 Ω L A B u h G, h3 Ω L A B u h G, h4 Ω L A B u h G, hx, hψ⟩

theorem normal_spec (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (p : Sp R) :
    IsIntegrallyClosed ((Sp R).presheaf.stalk p) := by
  let q : PrimeSpectrum R := p
  have : IsIntegrallyClosed ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.stalk q) := by
    haveI : q.asIdeal.IsPrime := q.isPrime
    exact isIntegrallyClosed_of_isLocalization (R := R) _ q.asIdeal.primeCompl
      (fun x hx => mem_nonZeroDivisors_of_ne_zero (fun h => hx (h ▸ q.asIdeal.zero_mem)))
  exact this

theorem normal_of_openImm {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X)
    (h : IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed (Y.presheaf.stalk (f.base x)) :=
  IsIntegrallyClosed.of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm

theorem glued_affine_curve_stalks_integrally_closed : LeafGlueNormal := by
  intro Ω L _ _ _ A B u h G y
  haveI := G.hiA; haveI := G.hiB
  have hy : y ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ y
  rcases hy with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · haveI := h.2.2.2.2.2.1; exact normal_of_openImm G.iA z (normal_spec A z)
  · haveI := h.2.2.2.2.2.2.1; exact normal_of_openImm G.iB z (normal_spec B z)

theorem irr_union {X : Type} [TopologicalSpace X] {U V : Set X} (hU : IsIrreducible U) (hV : IsIrreducible V)
    (hVo : IsOpen U) (hi : (U ∩ V).Nonempty) (hc : U ∪ V = Set.univ) : IrreducibleSpace X := by
  have h1 : V ⊆ closure (V ∩ U) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hV.2 hVo (by rwa [Set.inter_comm])
  have h2 : closure U = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hc]
    exact Set.union_subset subset_closure (h1.trans (closure_mono Set.inter_subset_right))
  have := hU.closure
  rw [h2] at this
  exact (irreducibleSpace_def X).2 this

theorem glued_affine_curve_is_integral_scheme : LeafGlueIntegral := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  haveI : IrreducibleSpace G.C0 := by
    have hA := (IrreducibleSpace.isIrreducible_univ (Sp A)).image G.iA.base G.iA.base.hom.continuous.continuousOn
    have hB := (IrreducibleSpace.isIrreducible_univ (Sp B)).image G.iB.base G.iB.base.hom.continuous.continuousOn
    rw [Set.image_univ] at hA hB
    refine irr_union hA hB G.iA.isOpenEmbedding.isOpen_range ?_ G.cover
    rw [G.inter]; exact Set.range_nonempty _
  haveI : ∀ y : G.C0, _root_.IsReduced (G.C0.presheaf.stalk y) := by
    intro y
    have hy : y ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ y
    rcases hy with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact isReduced_of_injective (asIso (G.iA.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (G.iA.stalkMap z)).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective (asIso (G.iB.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (G.iB.stalkMap z)).commRingCatIsoToRingEquiv.injective
  haveI : IsReduced G.C0 := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end LeafGlueProperPf
end E
end LateralTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.NbIsoPf

def FlatMonoLim : Prop := ∀ {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
  (ι : ∀ j, D.obj j ⟶ Y), (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) →
  (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) →
  ∀ {X : Scheme.{0}} (m : X ⟶ Y), Mono m → Flat m → QuasiCompact m → Set.range m = ⋂ j, Set.range (ι j) →
  ∀ c : Cone D, IsLimit c → Nonempty (c.pt ≅ X)

def SysFM : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
        Mono m ∧ Flat m ∧ QuasiCompact m ∧ Set.range m = ⋂ j, Set.range (ι j)

theorem NbIso_of (hS : SysFM) (hL : FlatMonoLim) : LateralTheory.E.SysPf.NbIso := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, m, hm, hf, hq, hr⟩ := hS W w hW y
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, fun c hc => ?_⟩
  exact hL D ι (fun j => ⟨(h1 j).1, (h1 j).2.1⟩) (fun f => (h2 f).1) m hm hf hq hr c hc

end LateralTheory.E.NbIsoPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfA

variable (R : Type) [CommRing R]

def hEq (X : Scheme.{0}) : HomotopyEquiv ((chainsN R).obj (sch.obj X))
    ((ChainComplex.single₀ (Shv R)).obj ((free R).obj (yoneda.obj X))) :=
  ((SimplicialObject.Augmented.ExtraDegeneracy.const (yoneda.obj X)).map (free R)).homotopyEquiv

abbrev Q := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

def isoQ (X : Scheme.{0}) : (Q R).obj ((chains R).obj (sch.obj X)) ≅ (Q R).obj (LateralTheory.E.LocSecPf.pt R X) :=
  ((ComplexShape.embeddingDownNat.extendHomotopyFunctorFactors (Shv R)).app _).symm ≪≫
  (ComplexShape.embeddingDownNat.extendHomotopyFunctor (Shv R)).mapIso (HomotopyCategory.isoOfHomotopyEquiv (hEq R X)) ≪≫
  (ComplexShape.embeddingDownNat.extendHomotopyFunctorFactors (Shv R)).app _ ≪≫
  (Q R).mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat _ 0 0 rfl)

def transIso {K K' L : Cx R} (i : (Q R).obj K ≅ (Q R).obj K') (n : ℤ) :
    CohomologyClass K L n ≃+ CohomologyClass K' L n :=
  (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).trans
    ({ toFun := fun f => i.inv ≫ f, invFun := fun g => i.hom ≫ g,
       left_inv := fun f => by simp, right_inv := fun g => by simp,
       map_add' := fun f g => Preadditive.comp_add _ _ _ _ _ _ } : _ ≃+ _) |>.trans
    (CohomologyClass.homAddEquiv (K := K') (L := L) (n := n)).symm

theorem locSecA : LateralTheory.E.LocSecPf.LocSecA := fun R _ X F n => ⟨transIso R (isoQ R X) n⟩

end LateralTheory.E.LocSecPfA
end
end
