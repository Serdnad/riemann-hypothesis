module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Module.SpanRankOperations
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Sheaves.SheafOfFunctions

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

theorem spanFinrank_maximalIdeal_quotient_add_one_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  set m := maximalIdeal R with hm
  let x' : m := ⟨x, hx⟩
  let v0 : CotangentSpace R := m.toCotangent x'
  have hx0 : v0 ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    simpa [pow_two] using hx2
  let L : Submodule (ResidueField R) (CotangentSpace R) := Submodule.span _ {v0}
  have hL : Module.finrank (ResidueField R) L = 1 := finrank_span_singleton hx0
  set q := Module.finrank (ResidueField R) (CotangentSpace R ⧸ L) with hq
  have hdim : q + 1 = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [hq, ← hL, L.finrank_quotient_add_finrank]
  let bW := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ L)
  have hlift : ∀ i : Fin q, ∃ y : m, L.mkQ (m.toCotangent y) = bW i := by
    intro i
    obtain ⟨v, hv⟩ := L.mkQ_surjective (bW i)
    obtain ⟨y, rfl⟩ := m.toCotangent_surjective v
    exact ⟨y, hv⟩
  choose t ht using hlift
  let s : Set m := insert x' (Set.range t)
  have hspan : Submodule.span (ResidueField R) (m.toCotangent '' s) = ⊤ := by
    set S := Submodule.span (ResidueField R) (m.toCotangent '' s)
    have hLS : L ≤ S := Submodule.span_le.mpr (by
      rintro _ rfl
      exact Submodule.subset_span ⟨x', Set.mem_insert _ _, rfl⟩)
    have hmap : S.map L.mkQ = ⊤ := by
      rw [eq_top_iff, ← bW.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨m.toCotangent (t i), Submodule.subset_span ⟨t i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩,
        ht i⟩
    rw [Submodule.map_mkQ_eq_top] at hmap
    rwa [sup_eq_right.mpr hLS] at hmap
  have hspanR : Submodule.span R s = ⊤ := CotangentSpace.span_image_eq_top_iff.mp hspan
  have hmspan : m = Ideal.span (Subtype.val '' s) := by
    have := Submodule.map_span m.subtype s
    rw [hspanR, Submodule.map_subtype_top] at this
    exact this
  have hmax : maximalIdeal (R ⧸ span {x}) =
      Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
    rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hm,
      congrArg (Ideal.map (Ideal.Quotient.mk (span {x}))) hmspan, Ideal.map_span]
    have : (Ideal.Quotient.mk (span {x})) '' (Subtype.val '' s) =
        insert 0 (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
      simp only [s, Set.image_insert_eq, ← Set.range_comp]
      congr 1
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
    rw [this, Ideal.span_insert_zero]
  have hle : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ q := by
    rw [hmax]
    have hfin : (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) =
        ((Finset.univ.image (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R)) :
          Finset (R ⧸ span {x})) : Set (R ⧸ span {x})) := by simp
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [hfin, Set.ncard_coe_finset]
    exact (Finset.card_image_le).trans (by simp)
  have hmr : m.spanFinrank = q + 1 := by
    rw [hm, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)]
    exact hdim.symm
  omega

private lemma exists_nat_of_le_add_one {d : WithBot ℕ∞} {n b : ℕ} (h2 : (n : WithBot ℕ∞) ≤ d + 1)
    (h3 : d ≤ b) : ∃ k : ℕ, d = k := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h2
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((b : ℕ∞) : WithBot ℕ∞) := h3
      rw [WithBot.coe_le_coe, top_le_iff] at h4
      exact ENat.natCast_ne_top b h4
    | coe k => exact ⟨k, rfl⟩

theorem isRegularLocalRing_quotient [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    IsRegularLocalRing (R ⧸ span {x}) ∧ ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h1 := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff R).mp inferInstance).symm
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (span {x}) ?_).trans ?_
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact (span_singleton_le_iff_mem _).mpr hx
    · gcongr
      exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans
        (by simp)
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R := R ⧸ span {x})
  rw [hR] at h2
  obtain ⟨k, hk⟩ := exists_nat_of_le_add_one h2 h3
  rw [hk] at h2 h3 ⊢
  have h2' : (maximalIdeal R).spanFinrank ≤ k + 1 := by exact_mod_cast h2
  have h3' : k ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by exact_mod_cast h3
  have hk' : (maximalIdeal (R ⧸ span {x})).spanFinrank = k := by omega
  refine ⟨(isRegularLocalRing_iff _).mpr (by rw [hk, hk']), ?_⟩
  rw [hR]
  exact_mod_cast (by omega : k + 1 = (maximalIdeal R).spanFinrank)

theorem IsRegularLocalRing.isDomain [IsRegularLocalRing R] : IsDomain R := by
  apply PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isDomain <;> assumption

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsLocallyFactorial (X : Scheme.{u}) : Prop where
  ufm_stalk : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)

variable {X : Scheme.{u}}

instance (priority := 100) IsLocallyFactorial.isNormalScheme [IsIntegral X]
    [IsLocallyFactorial X] : IsNormalScheme X where
  isDomain_stalk _ := inferInstance
  isIntegrallyClosed_stalk x := by
    have := IsLocallyFactorial.ufm_stalk (X := X) x
    infer_instance

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]


omit [IsLocallyNoetherian X] [IsNormalScheme X] in
lemma heightOneSpectrum_eq (x : PrimeDivisor X)
    (w : HeightOneSpectrum (X.presheaf.stalk x.point)) : w = x.heightOneSpectrum := by
  have := x.dimensionLEOne_stalk
  have hmax : w.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime w.ne_bot w.isPrime
  ext1
  exact IsLocalRing.eq_maximalIdeal hmax

lemma ord_nonneg_iff (x : PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    0 ≤ x.ord f ↔ f ∈ (algebraMap (X.presheaf.stalk x.point) X.functionField).range := by
  have := x.isDedekindDomain_stalk
  have hv0 : x.valuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have key : 0 ≤ x.ord f ↔ x.valuation f ≤ 1 := by
    simp only [ord, Left.nonneg_neg_iff]
    rw [WithZero.log_le_iff_le_exp hv0]
    simp
  rw [key]
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    rw [x.heightOneSpectrum_eq w]
    exact h
  · rintro ⟨a, rfl⟩
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _

end PrimeDivisor

section Algebra

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

end Algebra

section Hartogs

end Hartogs

section Affine

variable {U : X.Opens} (hU : IsAffineOpen U)


variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

end Affine

section Uniformizer

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Uniformizer

section LocallyPrincipal

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

end LocallyPrincipal

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Regular

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Regular

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits

universe w u

variable {X : TopCat.{u}}

lemma discPresheaf_isSheaf (A : X → AddCommGrpCat.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (discPresheaf A) := by
  have h := TopCat.Presheaf.toTypes_isSheaf X (fun x => A x)
  have := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u}) (discPresheaf A)).2
  exact this h

noncomputable def germSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨discPresheaf (fun x => F.presheaf.stalk x), discPresheaf_isSheaf _⟩

noncomputable def toGerms (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F.presheaf ⟶ discPresheaf (fun x => F.presheaf.stalk x) where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s x => F.presheaf.germ W.unop x.1 x.2 s
      map_zero' := by funext x; simp
      map_add' := fun s t => by funext x; simp }
  naturality W W' h := by
    ext s
    funext x
    exact F.presheaf.germ_res_apply h.unop x.1 x.2 s

lemma toGerms_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X) (W : (Opens X)ᵒᵖ) :
    Function.Injective ((toGerms F).app W) := by
  intro s t h
  apply TopCat.Presheaf.section_ext F W.unop s t
  intro x hx
  exact congrFun h ⟨x, hx⟩

noncomputable def toGermSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) : F ⟶ germSheaf F :=
  ObjectProperty.homMk (toGerms F)

instance (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Mono (toGermSheaf F) := by
  have : ∀ W, Mono ((toGerms F).app W) := fun W =>
    (AddCommGrpCat.mono_iff_injective _).2 (toGerms_injective F W)
  have : Mono (toGermSheaf F).hom := NatTrans.mono_of_mono_app (toGerms F)
  exact Sheaf.Hom.mono_of_presheaf_mono (f := toGermSheaf F)

theorem cechAcyclic_of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I]
    {ι : Type w} (U : ι → Opens X) : CechAcyclic I.obj U := by
  let r := Injective.factorThru (𝟙 I) (toGermSheaf I)
  have hr : toGermSheaf I ≫ r = 𝟙 I := Injective.comp_factorThru _ _
  have hr' : toGerms I ≫ r.hom = 𝟙 I.obj := congrArg (fun f => f.hom) hr
  exact CechAcyclic.of_retract (U := U) (toGerms I) r.hom hr' (cechAcyclic_discPresheaf U _)

end GroundTheory.Arith.SchemeCoh
end
