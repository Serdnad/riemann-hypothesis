module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitTorusZero

open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

variable {D : D7} {V : HSp D}

theorem rat_mem_GQ (g : GF V) : rat V g ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨g, rfl⟩

theorem zeroClause_of_conj (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ g : GF V)
    (h : ZeroClause μ f (rat V (g * γ * g⁻¹))) : ZeroClause μ f (rat V γ) := by
  have hg := rat_mem_GQ g
  have e : ratClass (GQ V) (rat V (g * γ * g⁻¹)) = ratClass (GQ V) (rat V γ) := by
    ext δ
    simp only [ratClass, Set.mem_ofPred_eq, map_mul, map_inv]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(rat V g)⁻¹ * k, mul_mem (inv_mem hg) hk, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨rat V g * k, mul_mem hg hk, by group⟩
  intro 𝓕 h𝓕
  have := h 𝓕 h𝓕
  unfold HasClassInt classKernel at *
  rw [e] at this
  exact this

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_of_quot {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) (hi : Integrable (descend (GQ V) φ) (autMeasure V μ)) :
    IntegrableOn φ 𝓕 μ ∧ ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (p := 1)).1 (memLp_one_iff_integrable.2 hi)
    rw [hφ.lift_descend] at this
    exact memLp_one_iff_integrable.1 this
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

end GlobalTheory.SplitTorusZero
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen.SmallExt

variable {S : Scheme.{0}}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

theorem surjective_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : Function.Surjective φ)
    (hn : ∀ a ∈ RingHom.ker φ, IsNilpotent a) : Surjective (spMap φ) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := by
    rw [range_comap_of_surjective _ _ hφ]
    intro a ha
    obtain ⟨n, hn⟩ := hn a ha
    exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  exact this

theorem pull_wl_comp {A X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (c : Pic (A ⊗ Z).left) :
    CechPic.pull (A ◁ (f ≫ g)).left c = CechPic.pull (A ◁ f).left (CechPic.pull (A ◁ g).left c) := by
  rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left, pull_comp]

theorem pull_wl_id {A X : Over S} (c : Pic (A ⊗ X).left) : CechPic.pull (A ◁ 𝟙 X).left c = c := by
  rw [MonoidalCategory.whiskerLeft_id, Over.id_left, pull_id]

end GlobalTheory.DualOpen.SmallExt


open GlobalTheory.DualOpen.SmallExt in
theorem GlobalTheory.DualOpen.exists_same_of_smallExt : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∀ u' : Over.mk s ⟶ U, Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) (ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u') → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  intro S _ A _ hA U M hMf hMi hMt C _ _ e he hme hne s N hNf u' hsame
  haveI : Smooth A.hom := hA.smooth
  obtain ⟨P, _, i, p, σ, q, hpi, hσi, hqi, hσc, hσs, hM1, hM2⟩ := GlobalTheory.T.smallExtension_dualNumber_fibreProduct_affineMilnorSquare C e he hme hne
  have calc3 := (GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.2.1
  set k := IsLocalRing.ResidueField C
  set π : C →+* C ⧸ Ideal.span {e} := Ideal.Quotient.mk (Ideal.span {e})
  set ρ : C →+* k := IsLocalRing.residue C
  have hfi : (dnFst k).comp (dnInl k) = RingHom.id k := RingHom.ext fun x ↦ rfl
  let TC : Over S := Over.mk s
  let TP : Over S := Over.mk (spMap i ≫ s)
  let Tε : Over S := Over.mk (spMap (dnInl k) ≫ spMap ρ ≫ s)
  let Tk : Over S := Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s)
  let jp : TC ⟶ TP := Over.homMk (spMap p) (by
    show spMap p ≫ spMap i ≫ s = s
    rw [← Category.assoc, ← spMap_comp', hpi, spMap_id', Category.id_comp])
  let jσ : TC ⟶ TP := Over.homMk (spMap σ) (by
    show spMap σ ≫ spMap i ≫ s = s
    rw [← Category.assoc, ← spMap_comp', hσi, spMap_id', Category.id_comp])
  let jq : Tε ⟶ TP := Over.homMk (spMap q) (by
    show spMap q ≫ spMap i ≫ s = spMap (dnInl k) ≫ spMap ρ ≫ s
    rw [← Category.assoc, ← spMap_comp', hqi, spMap_comp', Category.assoc])
  let r : TP ⟶ TC := Over.homMk (spMap i) rfl
  let kε : Tk ⟶ Tε := ptMap _ (dnFst k)
  let kc : Tk ⟶ TC := Over.homMk (spMap ρ) (by
    show spMap ρ ≫ s = spMap (dnFst k) ≫ spMap (dnInl k) ≫ spMap ρ ≫ s
    rw [← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])
  let k₀ := ptMap s π
  have hjr : jp ≫ r = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap p ≫ spMap i = 𝟙 _
    rw [← spMap_comp', hpi, spMap_id'])
  have hσr : jσ ≫ r = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap σ ≫ spMap i = 𝟙 _
    rw [← spMap_comp', hσi, spMap_id'])
  have hsq : kε ≫ jq = kc ≫ jp := Over.OverMorphism.ext hM2.w.symm
  have hkqr : kε ≫ jq ≫ r = kc := Over.OverMorphism.ext (by
    show spMap (dnFst k) ≫ spMap q ≫ spMap i = spMap ρ
    rw [← spMap_comp' i q, hqi, spMap_comp', ← Category.assoc, ← spMap_comp', hfi, spMap_id', Category.id_comp])
  have hεs : Function.Surjective (dnFst k) := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  have hεn : ∀ a ∈ RingHom.ker (dnFst k), IsNilpotent a := by
    intro a ha
    have h0 : a.fst = 0 := ha
    refine ⟨2, ?_⟩
    ext <;> simp [pow_two, h0]
  have hπn : ∀ a ∈ RingHom.ker π, IsNilpotent a := by
    intro a ha
    rw [Ideal.mk_ker] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    exact ⟨2, by rw [mul_pow, sq e, hme e he, mul_zero]⟩
  have hkεs : Surjective kε.left := surjective_spMap _ hεs hεn
  have hkεc : IsClosedImmersion kε.left := IsClosedImmersion.spec_of_surjective _ hεs
  have hk₀s : Surjective k₀.left := surjective_spMap _ Ideal.Quotient.mk_surjective hπn

  set n := cls N hNf.isLB
  set m := cls M hMf.isLB
  have hd : CechPic.pull (A ◁ k₀).left (n - CechPic.pull (A ◁ u').left m) = 0 := by
    have h := (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).1 hsame
    rw [map_sub, h, pull_wl_comp, sub_self]
  obtain ⟨d', hd'p, hd'σ⟩ := GlobalTheory.T.exists_picardClass_extend_affineMilnorSquare S A TP TC TC _ jp jσ k₀ k₀ hM1 hσc hσs hk₀s _ hd
  have h3 : CechPic.pull (A ◁ kε).left (CechPic.pull (A ◁ jq).left d') = 0 := by
    rw [← pull_wl_comp, hsq, pull_wl_comp, hd'p, map_zero]
  obtain ⟨D, hD, hDc⟩ := cls_surj (CechPic.pull (A ◁ jq).left d')
  have hDf : Fam A D := GlobalTheory.T.additiveFamily_of_trivial_mod_epsilon S A hA k (spMap (dnInl k) ≫ spMap ρ ≫ s) D hD (by rw [hDc]; exact h3)
  obtain ⟨D₂, hD₂, hD₂c⟩ := cls_surj (CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m)
  have hD₂f : Fam A D₂ := (GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.1 Tε U Tε D M hDf hMf (𝟙 _) (jq ≫ r ≫ u') D₂ hD₂
    (Or.inl (by rw [hD₂c, pull_wl_id, hDc]))
  obtain ⟨v, hv⟩ := hMt k (spMap ρ ≫ s) D₂ hD₂f (kε ≫ jq ≫ r ≫ u') ((calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).2 (by
    rw [hD₂c, map_add (f := _), h3, zero_add, pull_wl_comp kε]))
  have hv' : CechPic.pull (A ◁ jq).left d' + CechPic.pull (A ◁ (jq ≫ r ≫ u')).left m =
      CechPic.pull (A ◁ v).left m := by
    have h := (calc3 _ _ _ D₂ M hD₂ hMf.isLB _ _).1 hv
    rwa [pull_wl_id, hD₂c] at h
  have hglue : kc ≫ u' = kε ≫ v := hMi Tk _ _ ((calc3 _ _ _ M M hMf.isLB hMf.isLB _ _).2 (by
    rw [← hkqr, Category.assoc, Category.assoc, pull_wl_comp kε (jq ≫ r ≫ u'), pull_wl_comp kε v, ← hv', map_add (f := _),
      h3, zero_add]))
  obtain ⟨V, hVa, hV0, -⟩ := exists_isAffineOpen_mem_and_subset (X := U.left) (U := ⊤)
    (x := u'.left (IsLocalRing.closedPoint C)) trivial
  have hu'V : ∀ x, u'.left x ∈ V := fun x ↦
    ((IsLocalRing.specializes_closedPoint (R := C) x).map u'.left.continuous).mem_open V.isOpen hV0
  have hvV : ∀ y, v.left y ∈ V := by
    intro y
    obtain ⟨z, rfl⟩ := hkεs.surj y
    have h := congrArg (fun f ↦ f.left z) hglue
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    rw [← h]
    exact hu'V _
  obtain ⟨w, hw₁, hw₂⟩ := GlobalTheory.T.glue_morphisms_into_affineOpen_milnorSquare S U TP TC Tε Tk jp jq kc kε hM2 V hVa u' v hglue hu'V hvV
  have hunit := GlobalTheory.T.abelianScheme_units_lift_along_thickening S A hA Tε Tk kε (inferInstanceAs (IsAffine (Sp (DualNumber k)))) hkεc hkεs
  have hE := GlobalTheory.T.picardClass_eq_zero_affineMilnorSquare S A TP TC Tε Tk jp jq kc kε hM2 hunit
    (CechPic.pull (A ◁ w).left m - CechPic.pull (A ◁ (r ≫ u')).left m - d') (by
      rw [map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₁, ← Category.assoc, hjr, Category.id_comp, hd'p,
        sub_self, sub_zero]) (by
      rw [map_sub, map_sub, ← pull_wl_comp, ← pull_wl_comp, hw₂, ← hv', add_sub_cancel_right, sub_self])
  have hwe : CechPic.pull (A ◁ w).left m = CechPic.pull (A ◁ (r ≫ u')).left m + d' := by
    rw [sub_sub] at hE
    exact sub_eq_zero.1 hE
  refine ⟨jσ ≫ w, (calc3 _ _ _ N M hNf.isLB hMf.isLB _ _).2 ?_⟩
  rw [pull_wl_id, pull_wl_comp, hwe, map_add (f := _), ← pull_wl_comp, ← Category.assoc, hσr, Category.id_comp, hd'σ]
  exact (add_sub_cancel _ _).symm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetEx

open TrivSqZeroExt

variable {W : Type} [CommRing W]

theorem dual_isLocalRing [IsLocalRing W] : IsLocalRing (DualNumber W) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

theorem fstHom_isLocalHom : IsLocalHom (TrivSqZeroExt.fstHom W W W).toRingHom :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩

abbrev red (W : Type) [CommRing W] : Sp W ⟶ Sp (DualNumber W) := spMap (TrivSqZeroExt.fstHom W W W).toRingHom

theorem red_closedPoint [IsLocalRing W] :
    letI := dual_isLocalRing (W := W)
    (red W).base (IsLocalRing.closedPoint W) = IsLocalRing.closedPoint (DualNumber W) := by
  letI := dual_isLocalRing (W := W)
  haveI := fstHom_isLocalHom (W := W)
  rw [Spec.map_base]
  exact IsLocalRing.comap_closedPoint _

theorem top_le_of_red [IsLocalRing W] {X : Scheme.{0}} (y : Sp (DualNumber W) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (red W ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  letI := dual_isLocalRing (W := W)
  rw [Scheme.preimage_eq_top_of_closedPoint_mem y (U := U) ?_]
  have := h (show IsLocalRing.closedPoint W ∈ (⊤ : (Sp W).Opens) from trivial)
  rw [← red_closedPoint]
  exact this

theorem valR_fst {X : Scheme.{0}} (y : Sp (DualNumber W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) :
    (valR y U f).fst = valR (red W ≫ y) U f := by
  have h' : ⊤ ≤ (red W ≫ y) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage]; exact fun p _ => h trivial
  unfold valR
  rw [dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE (red W) y U ⊤ ⊤ h le_top]
  have n := congrArg (fun q => q.hom ((y.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom W W W).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [show (red W).appLE ⊤ ⊤ le_top = (red W).appTop from (Scheme.Hom.app_eq_appLE _).symm]
  exact n.symm

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow.JetEx

open TrivSqZeroExt

variable {W : Type} [CommRing W]

theorem epsLift_fst {A : Over (Sp W)} [GrpObj A] (u : epsR W ⟶ A) :
    epsLift u ≫ (fst (baseOver (Sp W)) A).left = (epsR W).hom := by
  rw [epsLift, ← Over.comp_left, lift_fst]; rfl

theorem epsLift_snd {A : Over (Sp W)} [GrpObj A] (u : epsR W ⟶ A) :
    epsLift u ≫ (snd (baseOver (Sp W)) A).left = u.left := by
  rw [epsLift, ← Over.comp_left, lift_snd]

theorem red_epsLift {A : Over (Sp W)} [GrpObj A] (v v' : epsR W ⟶ A) (hv : IsTangent v) (hv' : IsTangent v') :
    red W ≫ epsLift v = red W ≫ epsLift v' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, ← Over.fst_left, epsLift_fst, epsLift_fst]
  · rw [Category.assoc, Category.assoc, ← Over.snd_left, epsLift_snd, epsLift_snd]
    exact hv.trans hv'.symm

theorem red_epsLift_snd {A : Over (Sp W)} [GrpObj A] (v : epsR W ⟶ A) (hv : IsTangent v) :
    (red W ≫ epsLift v) ≫ (snd (baseOver (Sp W)) A).left = 𝟙 (Sp W) ≫ eSec A := by
  rw [Category.assoc, epsLift_snd, Category.id_comp]
  exact hv

open Classical in
theorem exists_jets [IsLocalRing W] (P : PolAV (Sp W)) (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) {I : Type}
    (t : I → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W))))) {g : ℕ} (v : Fin g → (epsR W ⟶ P.A))
    (hv : ∀ j, IsTangent (v j)) :
    ∃ (i₀ : P.L.ι) (c : Fin g → W) (ϑ : I → W) (J : I → Fin g → W),
      ⊤ ≤ (𝟙 (Sp W) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ ∧
      ∀ i j, valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) ((t i).f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (𝟙 (Sp W)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i j + c j * ϑ i)) := by
  have hL := P.isLB
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((eSec P.A : Sp W ⟶ P.A.left).base (IsLocalRing.closedPoint W))
  have htop : ⊤ ≤ (𝟙 (Sp W) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ := by
    rw [Category.id_comp, Scheme.preimage_eq_top_of_closedPoint_mem (eSec P.A : Sp W ⟶ P.A.left) hi₀]
  have hρt : ⊤ ≤ (𝟙 (Sp W)) ⁻¹ᵁ ((P.L.pull (eSec P.A)).U fun _ => i₀) := fun p _ =>
    Set.mem_iInter.2 fun _ => by
      have := htop (show p ∈ (⊤ : (Sp W).Opens) from trivial)
      exact this
  set u := valR (𝟙 (Sp W)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val with hu_def
  have hu : IsUnit u := by
    rw [hu_def, valR, dif_pos hρt]
    exact ((ρ.s _).isUnit.map _).map _
  set ui := Ring.inverse (u ^ k)
  have hui : u ^ k * ui = 1 := Ring.mul_inverse_cancel _ (hu.pow k)
  have hch : ∀ j, ⊤ ≤ (epsLift (v j)) ⁻¹ᵁ ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) := fun j =>
    top_le_of_red _ _ fun p _ => Set.mem_iInter.2 fun _ => by
      have := htop (show p ∈ (⊤ : (Sp W).Opens) from trivial)
      rw [← red_epsLift_snd (v j) (hv j)] at this
      exact this
  refine ⟨i₀, 0, fun i => if hn : Nonempty (Fin g) then
      ui * (valR (epsLift (v hn.some)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).fst else 0,
    fun i j => ui * (valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).snd, htop, fun i j => ?_⟩
  have hn : Nonempty (Fin g) := ⟨j⟩
  simp only [dif_pos hn]
  have hf : (valR (epsLift (v hn.some)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).fst =
      (valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) ((t i).f fun _ => i₀)).fst := by
    rw [valR_fst _ _ (hch _), valR_fst _ _ (hch _), red_epsLift _ _ (hv _) (hv j)]
  rw [hf]
  ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero]
    rw [← _root_.mul_assoc, hui, _root_.one_mul]
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, add_zero, Pi.zero_apply, zero_mul,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, zero_add, MulOpposite.unop_op]
    rw [← _root_.mul_assoc, hui, _root_.one_mul]

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow.JetEx

variable {W : Type} [CommRing W]

theorem exists_symLift_tr [IsNoetherianRing W] [IsLocalRing W] (P : PolAV (Sp W)) (ρ : LB.Gen (P.L.pull (eSec P.A)))
    (hρ : ρ.IsGen) (m : ℕ) (hm : Odd m) (hmu : IsUnit (m : W))
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))) (x : Over.mk (𝟙 (Sp W)) ⟶ P.A)
    (hx : x ^ (m ^ 2) = 1) :
    ∃ (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))
      (t : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))),
      SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U ∧ Tr P ρ m th U t := by
  have hLaw : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL := P.isLB
  let T : Over (Sp W) := Over.mk (𝟙 (Sp W))
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Sp W, ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    exact (by rw [Nat.cast_pow]; exact hmu.pow 2 : IsUnit ((m ^ 2 : ℕ) : W)).map e
  obtain ⟨hex, -⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex (IsLocalRing.closedPoint W)
  have hVt : V = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem (𝟙 (Sp W)) hV
  subst hVt
  let h : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : h ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull hL h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P m
  have e₁ : (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := GlobalTheory.NormTheta.exists_normalised hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) (by simp) α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hL (translT P.A θ.pt) (translPt P.A θ.pt) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
  exact ⟨θ, t, hθ, α, s₁, hα, hn, hs₁, ht⟩

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow

theorem exists_thJet_local : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (x : KeyIn W)
    (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → IsUnit (m : W) → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ x.P.A)),
    (∀ i, pt i ^ (m ^ 2) = 1) → ∃ ϑ J, ThJet x hg m pt ϑ J := by
  intro W _ _ _ _ x g hg m hm hmu I pt hpt
  choose U t hUt using fun i =>
    JetEx.exists_symLift_tr x.P x.rig x.rig_gen m hm hmu (TrSec.thSec x.P x.th) (pt i) (hpt i)
  obtain ⟨i₀, c, ϑ, J, htop, hval⟩ :=
    JetEx.exists_jets x.P x.rig (m ^ 2) t (fun j => x.v (j.cast hg.symm)) (fun j => x.basis.1 _)
  exact ⟨ϑ, J, TrSec.thSec x.P x.th, TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th, U, t, i₀, c, fun i => hUt i, htop, hval⟩

end GlobalTheory.MBLow
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.definitePairs_ratio_locally_rational_times_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  first | (exact @GlobalTheory.LocTriv.ratio_local_norm_dpair) | (exact GlobalTheory.LocTriv.ratio_local_norm_dpair) | (intros; apply GlobalTheory.LocTriv.ratio_local_norm_dpair  <;> assumption)
end
