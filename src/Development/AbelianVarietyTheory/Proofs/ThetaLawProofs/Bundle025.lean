module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

theorem _root_.GlobalTheory.T.exactAt_sectionCube_of_mul_pullback : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by
  first | exact @GlobalTheory.exactAt_secCube_of_mul_pull | exact GlobalTheory.exactAt_secCube_of_mul_pull | (intros; apply GlobalTheory.exactAt_secCube_of_mul_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.HenselZero

theorem exists_factor_stalk {X : Scheme.{0}} {T : CommRingCat.{0}} [IsLocalRing T] (w : Spec T ⟶ X) {y : X}
    (hw : w (closedPoint T) = y) : ∃ χ : X.presheaf.stalk y ⟶ T, Spec.map χ ≫ X.fromSpecStalk y = w := by
  subst hw
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk w⟩

theorem exists_formallySmooth_stalk {O : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec O) [Smooth p] (y : X) :
    ∃ α : O ⟶ X.presheaf.stalk y, α.hom.FormallySmooth ∧ Spec.map α = X.fromSpecStalk y ≫ p := by
  let τ : O ⟶ (Spec O).presheaf.stalk (p y) := StructureSheaf.toStalk O (p y)
  refine ⟨τ ≫ p.stalkMap y, ?_, ?_⟩
  · have hs : (p.stalkMap y).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (p.smoothLocus_eq_top.ge (Set.mem_univ y))
    letI : Algebra O ((Spec O).presheaf.stalk (p y)) := StructureSheaf.stalkAlgebra O (p y)
    have := (p y).isPrime
    have : IsLocalization.AtPrime ((Spec O).presheaf.stalk (p y)) (p y).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk O (p y)
    have h₀ : Algebra.FormallySmooth O ((Spec O).presheaf.stalk (p y)) :=
      Algebra.FormallySmooth.of_isLocalization (p y).asIdeal.primeCompl
    exact RingHom.FormallySmooth.comp (RingHom.formallySmooth_algebraMap.2 h₀) hs
  · have e : (Spec O).fromSpecStalk (p y) = Spec.map τ := Spec.fromSpecStalk_eq' _ _
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, e]

theorem fromSpecStalk_mem_basicOpen {X : Scheme.{0}} {y : X} {U : X.Opens} (hy : y ∈ U) (f : Γ(X, U))
    (q : Spec (X.presheaf.stalk y)) (hq : (X.presheaf.germ U y hy).hom f ∉ q.asIdeal) :
    X.fromSpecStalk y q ∈ X.basicOpen f := by
  have ht : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk y)
    (by rwa [Scheme.fromSpecStalk_closedPoint])).ge
  rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen, Scheme.fromSpecStalk_app hy]
  simp only [CommRingCat.comp_apply]
  rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]
  exact ⟨ht trivial, hq⟩

section Fibre

variable {O : Type} [CommRing O] [IsLocalRing O] {X Y : Scheme.{0}} {p : X ⟶ Sp O} {q : Y ⟶ Sp (ResidueField O)}
  {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
include hφ

theorem isClosedImmersion_fibre : IsClosedImmersion φ :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) hφ.flip
    (IsClosedImmersion.spec_of_surjective _ residue_surjective)

theorem maximalIdeal_le_span_sup {ι : Type} (y : Y) (α : CommRingCat.of O ⟶ X.presheaf.stalk (φ y))
    (hα : Spec.map α = X.fromSpecStalk (φ y) ≫ p) (f : ι → X.presheaf.stalk (φ y))
    (h : maximalIdeal _ ≤ Ideal.span (Set.range fun i => (φ.stalkMap y).hom (f i))) :
    maximalIdeal _ ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map α.hom := by
  have := isClosedImmersion_fibre hφ
  let I := (maximalIdeal O).map α.hom
  by_cases hI : I = ⊤
  · exact le_sup_of_le_right (le_top.trans hI.ge)
  have : Nontrivial (X.presheaf.stalk (φ y) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (X.presheaf.stalk (φ y) ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
  let π : X.presheaf.stalk (φ y) ⟶ .of (X.presheaf.stalk (φ y) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let β : ResidueField O →+* X.presheaf.stalk (φ y) ⧸ I := Ideal.quotientMap I α.hom Ideal.le_comap_map
  have hw : (Spec.map π ≫ X.fromSpecStalk (φ y)) ≫ p = spMap β ≫ spMap (residue O) := by
    rw [Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨χ, hχ⟩ := exists_factor_stalk (hφ.lift _ _ hw) (y := y) (φ.isClosedEmbedding.injective (by
    refine (congrArg (fun g => g (closedPoint (X.presheaf.stalk (φ y) ⧸ I))) (hφ.lift_fst _ _ hw)).trans ?_
    exact (congrArg (X.fromSpecStalk (φ y)) (comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint))
  have e : φ.stalkMap y ≫ χ = π := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (φ y)), Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      reassoc_of% hχ, hφ.lift_fst]
  have e' : ∀ a, χ.hom ((φ.stalkMap y).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun g => g.hom a) e
  intro a ha
  obtain hr := Ideal.mem_map_of_mem χ.hom (h (map_nonunit (φ.stalkMap y).hom a ha))
  rw [e', Ideal.map_span, ← Set.range_comp] at hr
  have hr' : Ideal.Quotient.mk I a ∈ (Ideal.span (Set.range f)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact (congrArg (fun F => _ ∈ Ideal.span (Set.range F)) (funext fun i => e' (f i))).mp hr
  exact Ideal.mem_quotient_iff_mem_sup.1 hr'

end Fibre

theorem exists_section_of_transversal {O ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Fintype ι] [DecidableEq ι] {X Y : Scheme.{0}} {p : X ⟶ Sp O} [Smooth p]
    {q : Y ⟶ Sp (ResidueField O)} {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
    (t : Sp (ResidueField O) ⟶ Y) (ht : t ≫ q = 𝟙 _) (pt : Sp (ResidueField O)) {U : X.Opens} (hU : φ (t pt) ∈ U)
    (f : ι → Γ(X, U)) (hf : ∀ i, valT (t ≫ φ) U (f i) = 0)
    (hm : maximalIdeal _ ≤ Ideal.span (Set.range fun i => gs φ (t pt) U (f i)))
    (w : ι → (Sp (DualNumber (ResidueField O)) ⟶ Y))
    (hw₁ : ∀ k, spMap (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom ≫ w k = t)
    (hw₂ : ∀ k, w k ≫ q = spMap (algebraMap _ _))
    (hd : (Matrix.of fun i k => (valT (w k ≫ φ) U (f i)).snd).det ≠ 0) :
    ∃ z : Sp O ⟶ X, z ≫ p = 𝟙 _ ∧ spMap (residue O) ≫ z = t ≫ φ ∧ (∀ i, valT z U (f i) = 0) ∧
      ∀ y, y ⤳ φ (t pt) → (∀ i, y ∉ X.basicOpen (f i)) → ∃ r, z r = y := by
  obtain rfl : pt = closedPoint (ResidueField O) := Subsingleton.elim (α := PrimeSpectrum (ResidueField O)) _ _
  set y₀ := φ (t (closedPoint (ResidueField O))) with hy₀
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨α, hs, hα⟩ := exists_formallySmooth_stalk p y₀
  obtain ⟨u, hu⟩ := exists_factor_stalk (t ≫ φ) (y := y₀) rfl
  have : IsLocalRing (DualNumber (ResidueField O)) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _
  have hχ := fun k => exists_factor_stalk (w k ≫ φ) (y := y₀) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    rw [← comap_closedPoint (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom,
      hy₀, ← hw₁ k]
    rfl)
  choose χ hχ using hχ
  letI := α.hom.toAlgebra
  have : Algebra.FormallySmooth O (X.presheaf.stalk y₀) := hs
  have e₁ : α ≫ u = CommRingCat.ofHom (residue O) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hu, hφ.w, reassoc_of% ht]
  have e₂ : ∀ k, χ k ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom = u := fun k => by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk y₀), Spec.map_comp, Category.assoc, hχ, hu, ← hw₁ k, Category.assoc]
  have e₃ : ∀ k, α ≫ χ k = CommRingCat.ofHom (residue O) ≫ CommRingCat.ofHom (algebraMap _ _) := fun k => by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ, hφ.w, reassoc_of% hw₂, Spec.map_comp]
  obtain ⟨ψ, hψ, hk⟩ := exists_algHom_ker_eq (O := O) (fun i => (X.presheaf.germ U y₀ hU).hom (f i)) u.hom
    (fun r => congrArg (fun g => g.hom r) e₁)
    (fun i => (JacGen.valT_specMap_fromSpecStalk hU u (f i)).symm.trans (hu ▸ hf i))
    (fun k => (χ k).hom) (fun k a => congrArg (fun g => g.hom a) (e₂ k))
    (fun k r => congrArg (fun g => g.hom r) (e₃ k))
    (by
      refine fun h => hd (Eq.trans ?_ h)
      congr 1
      ext i k
      rw [Matrix.of_apply, Matrix.of_apply, ← hχ, JacGen.valT_specMap_fromSpecStalk hU])
    (maximalIdeal_le_span_sup hφ _ α hα _ (hm.trans_eq (congrArg (fun F => Ideal.span (Set.range F))
      (funext fun i => (gs_eq φ _ U hU _).trans (Scheme.Hom.germ_stalkMap_apply φ U _ hU _).symm))))
  have hs' : Function.Surjective ψ := fun r => ⟨_, ψ.commutes r⟩
  refine ⟨spMap ψ.toRingHom ≫ X.fromSpecStalk y₀, ?_, ?_, fun i => ?_, fun y hy hyf => ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact ψ.commutes r
  · rw [← hu, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact hψ a
  · exact (JacGen.valT_specMap_fromSpecStalk hU (CommRingCat.ofHom ψ.toRingHom) (f i)).trans
      (hk.ge (Ideal.subset_span ⟨i, rfl⟩))
  · obtain ⟨r, rfl⟩ : y ∈ Set.range (X.fromSpecStalk y₀) := by
      rw [Scheme.range_fromSpecStalk]
      exact hy
    obtain ⟨r', hr'⟩ : r ∈ Set.range (PrimeSpectrum.comap ψ.toRingHom) := by
      rw [range_comap_of_surjective _ _ hs']
      refine hk.le.trans (Ideal.span_le.2 ?_)
      rintro _ ⟨i, rfl⟩
      by_contra hn
      exact hyf i (fromSpecStalk_mem_basicOpen hU _ r hn)
    exact ⟨r', congrArg (X.fromSpecStalk y₀) hr'⟩

end GlobalTheory.HenselZero
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.transversal_zeros_of_jacobian_ne_zero_domain : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] (x : KeyIn O) (x' : KeyIn K) (f : O →+* K) φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → Kˣ), EtZ x' s' z' ch' ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := K) (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : K) ^ l = f (valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  first | exact @GlobalTheory.KeyKa.etZ_of_jac_ne_zero | exact GlobalTheory.KeyKa.etZ_of_jac_ne_zero | (intros; apply GlobalTheory.KeyKa.etZ_of_jac_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.TransvFin

theorem valT_eq_zero_of_notMem {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ w ⁻¹ᵁ U) (f : Γ(X, U)) (p : Sp K) (hp : w p ∉ X.basicOpen f) : valT (T := K) w U f = 0 := by
  by_contra hne
  have h1 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((w.appLE U ⊤ h).hom f)) := by
    have e : valT (T := K) w U f = _ := dif_pos h
    exact e ▸ Ne.isUnit hne
  have h2 : IsUnit ((w.appLE U ⊤ h).hom f) := by
    have := h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [Iso.hom_inv_id_apply] at this
  have h3 := (Sp K).basicOpen_of_isUnit h2
  rw [Scheme.basicOpen_appLE] at h3
  exact hp ((h3.ge (x := p) trivial).2)

theorem eq_of_specializes {X : Scheme.{0}} {J : Type} {U : X.Opens} (f : J → Γ(X, U)) {y y' : X} (h : y' ⤳ y)
    (hy : y ∈ U)
    (hf : Ideal.span (Set.range fun i => gs (𝟙 X) y U (f i)) = IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (h0 : ∀ i, y' ∉ X.basicOpen (f i)) : y' = y := by
  by_contra hne
  have hn : ¬ y ⤳ y' := fun h' => hne (h.antisymm h').eq
  rw [specializes_iff_forall_open] at hn
  push_neg at hn
  obtain ⟨V, hV, hV1, hV2⟩ := hn
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hyW' : y' ∈ W := h.mem_open W.isOpen hyW
  obtain ⟨g, hg, hg'⟩ := hW.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨y', hV1⟩ hyW'
  have hle : IsLocalRing.maximalIdeal (X.presheaf.stalk y) ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y')).comap (X.presheaf.stalkSpecializes h).hom := by
    rw [← hf, Ideal.span_le]
    rintro _ ⟨i, rfl⟩ hu
    refine h0 i ((X.mem_basicOpen (f i) y' (h.mem_open U.isOpen hy)).2 ?_)
    have e : gs (𝟙 X) y U (f i) = (X.presheaf.germ U y hy).hom (f i) := gs_eq (𝟙 X) y U hy (f i)
    beta_reduce at hu
    rwa [e, TopCat.Presheaf.germ_stalkSpecializes_apply] at hu
  have hm : (X.presheaf.germ W y hyW).hom g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun hu => hV2 (hg ((X.mem_basicOpen g y hyW).2 hu))
  refine hle hm ?_
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (X.mem_basicOpen g y' hyW').1 hg'

theorem finite_of_isClosed_singleton {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    [QuasiSober T] {Z : Set T} (hZ : IsClosed Z) (h : ∀ y ∈ Z, IsClosed ({y} : Set T)) : Z.Finite := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hS.sUnion fun t ht => ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober (hi t ht) (hc t ht)
  rw [← hy.def, (h y ⟨t, ht, hy.mem⟩).closure_eq]
  exact Set.finite_singleton y

end GlobalTheory.TransvFin


open GlobalTheory.TransvFin in
theorem GlobalTheory.KeyKa.exists_etZ_of_jac_ne_zero : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n), (∀ (z : Pt x) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) → jac x s z c ≠ 0) → ∃ (d : ℕ) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  intro K _ _ x n s hs
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  have : IsProper x.P.A.hom := x.P.isAb.proper
  have : JacobsonSpace x.P.A.left := LocallyOfFiniteType.jacobsonSpace x.P.A.hom
  have : IsLocallyNoetherian x.P.A.left := LocallyOfFiniteType.isLocallyNoetherian x.P.A.hom
  have : CompactSpace x.P.A.left := QuasiCompact.compactSpace_of_compactSpace x.P.A.hom
  have : IsNoetherian x.P.A.left := {}
  let Z : Set x.P.A.left := {y | ∀ i, y ∉ Out.nonzeroLocus (s i)}
  have hZ : IsClosed Z := by
    have e : Z = ⋂ i, (Out.nonzeroLocus (s i) : Set x.P.A.left)ᶜ := by
      ext y
      simp [Z]
    rw [e]
    exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
  have hb : ∀ y ∈ Z, ∀ c i, y ∉ x.P.A.left.basicOpen ((s i).f c) := fun y hy c i h =>
    hy i (TopologicalSpace.Opens.mem_iSup.2 ⟨c, h⟩)
  have key : ∀ y ∈ Z, IsClosed ({y} : Set x.P.A.left) → ∃ (z : Pt x) (c : x.P.L.ι), (∀ p, z.left p = y) ∧
      ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧ ∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0 := by
    intro y hy hc
    let z : Pt x := Over.homMk (pointOfClosedPoint (K := K) x.P.A.hom y hc)
      (pointOfClosedPoint_comp (K := K) x.P.A.hom y hc)
    have hz (p) : z.left p = y := pointOfClosedPoint_apply (K := K) x.P.A.hom y hc p
    obtain ⟨c, hyc⟩ := TopologicalSpace.Opens.mem_iSup.1 (x.P.isLB.cover.ge (x := y) trivial)
    have ht : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c := fun p _ => (congrArg (· ∈ x.P.L.U c) (hz p)).mpr hyc
    exact ⟨z, c, hz, ht, fun i => valT_eq_zero_of_notMem z.left ht _ (IsLocalRing.closedPoint K)
      fun h => hb y hy c i ((congrArg (· ∈ x.P.A.left.basicOpen ((s i).f c)) (hz _)).mp h)⟩
  have hcl : ∀ y ∈ Z, IsClosed ({y} : Set x.P.A.left) := by
    intro y' hy'
    obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints (Z := closure ({y'} : Set x.P.A.left))
      ⟨y', subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hsp : y' ⤳ y := specializes_iff_mem_closure.2 hy
    obtain ⟨z, c, hz, ht, h0⟩ := key y (hsp.mem_closed hZ hy') hc
    have h1 := (jac_ne_zero_iff_span_eq_maximalIdeal K x n s z c (IsLocalRing.closedPoint K) ht h0).1 (hs z c ht h0)
    have hU : z.left (IsLocalRing.closedPoint K) ∈ x.P.L.U c := ht (x := IsLocalRing.closedPoint K) trivial
    have e := eq_of_specializes (fun i => (s i).f c) ((hz _).symm ▸ hsp) hU h1 (hb y' hy' c)
    rw [e.trans (hz _)]
    exact hc
  have hfin := finite_of_isClosed_singleton hZ hcl
  obtain ⟨d, ⟨e⟩⟩ := Finite.exists_equiv_fin Z (h := hfin)
  choose z c hz ht h0 using fun y : Z => key y y.2 (hcl y y.2)
  refine ⟨d, fun a => z (e.symm a), fun a => c (e.symm a), fun a => ht _, fun a => h0 _,
    fun a => (hs _ _ (ht _) (h0 _)).isUnit, fun a a' hne p h => hne ?_,
    fun y hy => ⟨e ⟨y, hy⟩, IsLocalRing.closedPoint K, ?_⟩⟩
  · exact e.symm.injective (Subtype.ext ((hz _ p).symm.trans (h.trans (hz _ p))))
  · exact (hz _ _).trans (congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩))
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.BoxSpan

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def ev (p : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_cst (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst p U c) = ev (r ≫ p) z c :=
  (gs_res r z le_top h _).trans ((gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _))

theorem gs_sum {I : Type} (s : Finset I) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : I → Γ(Y, U)) :
    gs r z U (∑ i ∈ s, a i) = ∑ i ∈ s, gs r z U (a i) := by

  simp only [gs_eq r z U h, map_sum]

theorem exists_sec_pw (L : LB X) (t : ℤ) (a : LB.Sec (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => t))) :
    ∃ a' : LB.Sec (pw L t), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
      sval a r z J = gs r z (L.U (J r)) (a'.f (J r)) := by
  have hle : ∀ i, L.U i ≤ LB.wchart L (K := PUnit) (fun _ => 𝟙 X) (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  refine ⟨⟨fun i => rs X (hle i) (a.f fun _ => i), fun i j => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · have hy' : y ∈ L.U i ⊓ L.U j := hy
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (hle i) hy'.1 _)).trans
      ((sec_trans a (𝟙 X) y (hle i hy'.1) (hle j hy'.2)).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (hle j) hy'.2 _)).symm
    refine Eq.trans ?_ (gs_unit (𝟙 X) y (L.U i ⊓ L.U j) hy' (L.g i j ^ t)).symm
    rw [map_zpow]
    exact congrArg Units.val (Fintype.prod_unique (fun _ : PUnit => gm (𝟙 X ≫ 𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) ^ t))
  · rw [sval_of a r z J (fun _ => J r) (fun _ => by rw [Category.comp_id])]
    exact (gs_res r z (hle _) (hJ r) _).symm

theorem isProper_powObj {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : IsAbelianScheme A) :
    ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => (AbelianSchemeGerms.isAbelianScheme_powObj A h n).proper

theorem exists_coords (x : KeyIn R) {m N : ℕ} (b : Fin N → RR x m) (hb : IsBasis x b)
    (a : LB.Sec (LB.LinComb x.P.L (K := PUnit) (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)))) :
    ∃ c : Fin N → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) J, Good x.P.L z J →
      sval a r z J = ∑ k, ev (r ≫ x.P.A.hom) z (c k) * gs r z (x.P.L.U (J r)) ((b k).f (J r)) := by
  obtain ⟨a', ha⟩ := exists_sec_pw x.P.L m a
  obtain ⟨c, hc, -⟩ := hb a'
  refine ⟨c, fun Z r z J hJ => (ha Z r z J hJ).trans ((congrArg (gs r z _) (hc (J r))).trans
    ((gs_sum _ r z _ (hJ r) _).trans (Finset.sum_congr rfl fun k _ => ?_)))⟩
  exact (gs_mul r z _ (hJ r) _ _).trans (congrArg (· * _) (gs_cst _ r z _ (hJ r) _))

theorem sum_mul_sum_cons {T : Type} [CommRing T] {E₁ E₂ E : R →+* T} (h₁ : E₁ = E) (h₂ : E₂ = E) {n N k : ℕ}
    (G : Fin (n + 1) → Fin N → T) (c : Fin k → Fin N → R) (q : Fin k → (Fin n → Fin N) → R) :
    ∑ i, (∑ j, E₁ (c i j) * G 0 j) * ∑ I, E₂ (q i I) * ∏ d : Fin n, G d.succ (I d) =
      ∑ I : Fin (n + 1) → Fin N, E (∑ i, c i (I 0) * q i (Fin.tail I)) * ∏ d, G d (I d) := by
  subst h₁ h₂
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]

  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, map_sum, map_mul]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.tail_cons]
  ring

theorem span_ev (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m) (hb : IsBasis x b) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))),
      ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj x.P.A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  induction n with
  | zero =>
    intro s
    have hW : LB.wchart x.P.L (K := Fin 0) (fun c => (Out.powPr x.P.A c).left) Fin.elim0 = ⊤ :=
      top_le_iff.1 fun _ _ => Set.mem_iInter.2 fun k => k.elim0
    haveI : IsIso (Out.powObj x.P.A 0).hom := inferInstanceAs (IsIso (𝟙 (Sp K)))
    obtain ⟨c, hc⟩ := (cst_bijective (Out.powObj x.P.A 0).hom hW).2 (s.f Fin.elim0)
    refine ⟨fun _ => c, fun Z r z J hJ => ?_⟩
    rw [sval_of s r z J Fin.elim0 (fun k => k.elim0), ← hc, Fintype.sum_unique, Fin.prod_univ_zero, _root_.mul_one]
    exact gs_cst _ r z _ (Set.mem_iInter.2 fun k => k.elim0) c
  | succ n ih =>
    intro s
    haveI := x.P.isAb.proper
    haveI := isProper_powObj x.P.A x.P.isAb n
    have hF : FormEq (K := Fin (n + 1)) (K' := PUnit ⊕ Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ))
        (Sum.elim (fun _ => (fst x.P.A (Out.powObj x.P.A n)).left ≫ 𝟙 x.P.A.left)
          (fun k => (snd x.P.A (Out.powObj x.P.A n)).left ≫ (Out.powPr x.P.A k).left))
        (Sum.elim (fun _ => (m : ℤ)) (fun _ => (m : ℤ))) := fun U _ h => by
      rw [Fin.prod_univ_succ, Fintype.prod_sum_type]
      exact congrArg₂ (· * ·) (Fintype.prod_unique
        (fun _ : PUnit => h ((fst x.P.A (Out.powObj x.P.A n)).left ≫ 𝟙 x.P.A.left) ^ (m : ℤ))).symm rfl
    obtain ⟨v, hv⟩ := exists_sec x.P.isLB hF s
    obtain ⟨k, a₁, a₂, ha⟩ := (GlobalTheory.T.section_lin_comb_fiber_product_separated K x.P.A.left x.P.L x.P.isLB x.P.A (Out.powObj x.P.A n) PUnit (Fin n)
      (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ))).1 v
    choose c hc using fun i => exists_coords x b hb (a₁ i)
    choose q hq using fun i => ih (a₂ i)
    refine ⟨fun I => ∑ i, c i (I 0) * q i (Fin.tail I), fun Z r z J hJ => ?_⟩
    refine (hv Z r z J hJ).symm.trans ((ha Z r z J hJ).trans ?_)
    have e₁ : (r ≫ (fst x.P.A (Out.powObj x.P.A n)).left) ≫ x.P.A.hom = r ≫ (Out.powObj x.P.A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (fst x.P.A (Out.powObj x.P.A n))))
    have e₂ : (r ≫ (snd x.P.A (Out.powObj x.P.A n)).left) ≫ (Out.powObj x.P.A n).hom =
        r ≫ (Out.powObj x.P.A (n + 1)).hom :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w (snd x.P.A (Out.powObj x.P.A n))))
    refine (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (hc i Z _ z J hJ) (hq i Z _ z J hJ)).trans ?_
    exact sum_mul_sum_cons (congrArg (ev · z) e₁) (congrArg (ev · z) e₂)
      (fun d j => gs (r ≫ (Out.powPr x.P.A d).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A d).left)))
          ((b j).f (J (r ≫ (Out.powPr x.P.A d).left)))) c q

theorem boxProducts_span : ∀ (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m), IsBasis x b → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))), ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  intro K _ x m N b hb n s
  obtain ⟨q, hq⟩ := span_ev K x m N b hb n s
  refine ⟨q, fun Z r z J hJ => (hq Z r z J hJ).trans (Finset.sum_congr rfl fun I _ => ?_)⟩
  rw [gs_cst _ r z ⊤ trivial]

end GlobalTheory.BoxSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → w.IsGen → w'.IsGen → (∀ v : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, (∀ r, v ≫ alMap x al r 1 = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → val w (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w' r z J = val w' (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w r z J) → ξ = ξ' := by
  first | exact @GlobalTheory.KeyKa.eq_of_similitude_invariant | exact GlobalTheory.KeyKa.eq_of_similitude_invariant | (intros; apply GlobalTheory.KeyKa.eq_of_similitude_invariant <;> assumption)
end
