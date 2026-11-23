module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Principalise

theorem memIdealOfLocally {W : Scheme.{0}} (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, GlobalTheory.Cartier.app_resG] at this
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

theorem comapIdealTopLe {X W : Scheme.{0}} [IsAffine W] (J : X.IdealSheafData) (g : W ⟶ X)
    (U : X.affineOpens) (h : ⊤ ≤ g ⁻¹ᵁ U.1) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤ Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U) := by
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop (Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U)) := by
    refine (GlobalTheory.Cartier.comap_le_iff _ _ _).2 fun U' a ha B hB => memIdealOfLocally _ _ _ fun y hy => ?_
    obtain ⟨t, htle, hyt⟩ := U.2.exists_basicOpen_le (V := U'.1 ⊓ U.1) ⟨g y, hB hy, h trivial⟩ (h trivial)
    obtain ⟨_, ⟨B', hB'a, rfl⟩, hyB', hB'le⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ B.1 ⊓ g ⁻¹ᵁ X.basicOpen t from ⟨hy, hyt⟩) (B.1 ⊓ g ⁻¹ᵁ X.basicOpen t).isOpen
    refine ⟨⟨B', hB'a⟩, fun x hx => (hB'le hx).1, hyB', ?_⟩
    have hDU' : X.basicOpen t ≤ U'.1 := htle.trans inf_le_left
    have h1 : resG X hDU' a ∈ J.ideal (X.affineBasicOpen t) :=
      J.ideal_le_comap_ideal (U := X.affineBasicOpen t) (V := U') hDU' ha
    rw [← J.map_ideal_basicOpen U t] at h1
    have hB'D : B' ≤ g ⁻¹ᵁ X.basicOpen t := fun x hx => (hB'le hx).2
    have e : resG W (fun x hx => (hB'le hx).1 : B' ≤ B.1) (resG W hB ((g.app U'.1).hom a)) =
        (g.appLE (X.basicOpen t) B' hB'D).hom (resG X hDU' a) := by
      show _ = resG W hB'D ((g.app (X.basicOpen t)).hom (resG X hDU' a))
      rw [GlobalTheory.Cartier.app_resG, GlobalTheory.Cartier.resG_resG, GlobalTheory.Cartier.resG_resG]
    rw [e, Scheme.IdealSheafData.ofIdealTop_ideal]
    have h2 := Ideal.mem_map_of_mem (g.appLE (X.basicOpen t) B' hB'D).hom h1
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h2
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    exact h2
  have := key ⟨⊤, isAffineOpen_top W⟩
  rw [Scheme.IdealSheafData.ofIdealTop_ideal] at this
  refine this.trans (le_of_eq ?_)
  convert Ideal.map_id _
  rw [show homOfLE (le_top : (⊤ : W.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem comapIdealAffine : ∀ {X W : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (U : X.affineOpens) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ U.1), (J.comap g).ideal A = Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U) := by
  intro X W J g U A h
  apply le_antisymm
  · intro x hx
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := (GlobalTheory.Cartier.comap_le_iff (J.comap g) A.1.ι _).1 le_rfl A x hx ⟨⊤, isAffineOpen_top _⟩ hA
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := comapIdealTopLe J (A.1.ι ≫ g) U (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U)),
      Ideal.mem_comap, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    exact h2
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (GlobalTheory.Cartier.comap_le_iff J g _).1 le_rfl U a ha A h

theorem kerIdealAffine : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U)), ∃ J : X.IdealSheafData, J.ideal ⟨U, hU⟩ = I ∧ ∀ N : ℕ, (N : Γ(X, U)) ∈ I → ∀ V : X.affineOpens, (N : Γ(X, V.1)) ∈ J.ideal V := by
  intro X _ U hU I
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I := Ideal.Quotient.mk I
  let f : Spec (CommRingCat.of (Γ(X, U) ⧸ I)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  haveI : QuasiCompact f := quasiCompact_of_noetherianSpace_source f
  have hz : ⊤ ≤ f ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : f.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : f.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp]
    congr 1
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (f.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  refine ⟨f.ker, ?_, ?_⟩
  · ext a
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    constructor
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        show resG _ hz ((f.app U).hom a) = 0
        rw [ha, map_zero]
      rw [k1] at h1
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).hom.hom h1
      rw [Iso.inv_hom_id_apply, map_zero] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        rw [k1, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
      refine GlobalTheory.Cartier.ext_germ fun x hx => ?_
      rw [map_zero, ← GlobalTheory.Cartier.germ_resG hz x trivial]
      exact (congrArg _ h1).trans (map_zero _)
  · intro N hN V
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, map_natCast]
    have h0 : (N : Γ(X, U) ⧸ I) = 0 := by
      rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]; exact hN
    have h1 : (N : Γ(Spec (CommRingCat.of (Γ(X, U) ⧸ I)), ⊤)) = 0 := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom, h0, map_zero]
    rw [← map_natCast (resG _ (le_top : f ⁻¹ᵁ V.1 ≤ ⊤)), h1, map_zero]

theorem exists_dvd_of_span_mul_eq {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {m : ℕ}
    (A : Fin m → R) (I' : Ideal R) {f : R} (h : Ideal.span (Set.range A) * I' = Ideal.span {f})
    (hf : f ∈ nonZeroDivisors R) : ∃ k, ∃ s ∉ P, ∀ k', A k ∣ s * A k' := by
  have hfm : f ∈ Ideal.span (Set.range A) * I' := h ▸ Ideal.mem_span_singleton_self f
  have key : ∀ x ∈ Ideal.span (Set.range A) * I', ∃ c : Fin m → R, (∀ k, c k ∈ I') ∧ x = ∑ k, A k * c k := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩ => ?_)
    · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      refine ⟨fun k => d k * b, fun k => I'.mul_mem_left _ hb, ?_⟩
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring
    · refine ⟨c + d, fun k => I'.add_mem (hc k) (hd k), ?_⟩
      simp only [hx, hy, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  obtain ⟨c, hc, hfc⟩ := key f hfm
  have hAc : ∀ k k', ∃ t, A k' * c k = f * t := fun k k' => by
    have : A k' * c k ∈ Ideal.span {f} :=
      h ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨k', rfl⟩) (hc k)
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨t, by rw [← ht, mul_comm]⟩
  choose t ht using hAc
  have hsum : ∑ k, t k k = 1 := by
    refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
    rw [Finset.mul_sum, _root_.mul_one]
    conv_rhs => rw [hfc]
    exact Finset.sum_congr rfl fun k _ => (ht k k).symm
  obtain ⟨k, hk⟩ : ∃ k, t k k ∉ P := by
    by_contra hcon
    push_neg at hcon
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2
      (hsum ▸ Ideal.sum_mem _ fun k _ => hcon k))
  refine ⟨k, t k k, hk, fun k' => ⟨t k k', ?_⟩⟩
  refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
  calc f * (t k k * A k') = (f * t k k) * A k' := by ring
    _ = A k * c k * A k' := by rw [ht]
    _ = A k * (A k' * c k) := by ring
    _ = f * (A k * t k k') := by rw [ht]; ring

end GlobalTheory.Principalise
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FieldPtGlue

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X}

theorem valF_ne_zero_iff {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  rw [e3]
  constructor
  · intro hne
    exact (Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hne).map _)).ge
  · intro hle h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at hle
    exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem valF_restrict {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_sub {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a - b) = valF x U a - valF x U b := by
  simp only [valF, dif_pos h, map_sub]

theorem le_preimage_iff (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint F) ∈ U := by
  constructor
  · intro h
    exact h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
  · intro h y _
    have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    subst this
    exact h

end Val

noncomputable def resPt (X : Scheme.{0}) (z : X) : Sp (X.residueField z : Type) ⟶ X := X.fromSpecResidueField z

theorem resPt_le_iff (X : Scheme.{0}) (z : X) (U : X.Opens) : ⊤ ≤ resPt X z ⁻¹ᵁ U ↔ z ∈ U := by
  rw [le_preimage_iff]
  have : resPt X z (IsLocalRing.closedPoint (X.residueField z : Type)) = z :=
    Scheme.fromSpecResidueField_apply z _
  rw [this]

theorem section_ext {X : Scheme.{0}} [IsReduced X] {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → valF w U a = valF w U b) : a = b := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro z hz
  have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 (X.basicOpen_le _ hz)
  have h1 := (valF_ne_zero_iff hU (a - b)).2 ((resPt_le_iff X z _).2 hz)
  rw [valF_sub hU, h _ _ hU, sub_self] at h1
  exact absurd rfl h1

theorem exists_unit_of_locally : ∀ (X : Scheme.{0}) [IsReduced X] (U : X.Opens) (P : ∀ (k : Type) [Field k], (Sp k ⟶ X) → k → Prop), (∀ (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : k), ⊤ ≤ w ⁻¹ᵁ U → P k w a → P k w a' → a = a') → (∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → ¬ P k w 0) → (∀ z ∈ U, ∃ (V : X.Opens) (s : Γ(X, V)), z ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → P k w (valF w V s)) → ∃ s : Γ(X, U)ˣ, ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U s.val) := by
  intro X _ U P huniq hne hloc
  choose V s hzV hVU hP using hloc
  let V' : U → X.Opens := fun z => V z.1 z.2
  let s' : ∀ z : U, Γ(X, V' z) := fun z => s z.1 z.2
  have hcov : U ≤ iSup V' := fun z hz =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzV z hz⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V' s' := by
    intro i j
    refine section_ext (X := X) (U := V' i ⊓ V' j) _ _ fun k _ w hw => ?_
    have hi : ⊤ ≤ w ⁻¹ᵁ V' i := fun q hq => (hw hq).1
    have hj : ⊤ ≤ w ⁻¹ᵁ V' j := fun q hq => (hw hq).2
    refine (valF_restrict inf_le_left hw (s' i)).trans
      (Eq.trans ?_ (valF_restrict inf_le_right hw (s' j)).symm)
    exact huniq k w _ _ (fun q hq => hVU i.1 i.2 (hi hq)) (hP i.1 i.2 k w hi) (hP j.1 j.2 k w hj)
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' V' U (fun i => homOfLE (hVU i.1 i.2)) hcov s' hcomp
  have key : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U t) := by
    intro k _ w hw
    have hz := (le_preimage_iff U).1 hw
    have hV : ⊤ ≤ w ⁻¹ᵁ V _ hz := (le_preimage_iff _).2 (hzV _ hz)
    have e : valF w U t = valF w (V _ hz) (s _ hz) :=
      (valF_restrict (hVU _ hz) hV t).symm.trans (congrArg (valF w (V _ hz)) (ht ⟨_, hz⟩))
    rw [e]
    exact hP _ hz k w hV
  have hu : IsUnit (M := Γ(X, U)) t := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 hz
    have h0 : valF (resPt X z) U t ≠ 0 := fun h0 => hne _ _ hU (h0 ▸ key _ _ hU)
    have h1 := (resPt_le_iff X z _).1 ((valF_ne_zero_iff hU t).1 h0)
    exact (X.mem_basicOpen t z hz).1 h1
  exact ⟨hu.unit, key⟩

end GlobalTheory.FieldPtGlue
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m : ℕ}

theorem lin_comp {u u' : Fin m → V} (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0)
    (hu : ∀ j, u' j = ∑ i, A j i • u i) (d : Fin m → k) (j : Fin m) (hd : ∀ i, j < i → d i = 0) :
    ∃ e : Fin m → k, (∀ i, j < i → e i = 0) ∧ e j = d j * A j j ∧ ∑ i, d i • u' i = ∑ i, e i • u i := by
  refine ⟨fun i => ∑ l, d l * A l i, fun i hi => Finset.sum_eq_zero fun l _ => ?_, ?_, ?_⟩
  · rcases lt_or_ge j l with h | h
    · rw [hd l h, zero_mul]
    · rw [hA l i (h.trans_lt hi), mul_zero]
  · refine Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA l j h, mul_zero]
    · rw [hd l h, zero_mul]
  · simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm

theorem lin_symm {u u' : Fin m → V} (hi : ∀ c c' : Fin m → k, ∑ i, c i • u' i = ∑ i, c' i • u' i → c = c')
    (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0) (hu : ∀ j, u' j = ∑ i, A j i • u i) :
    ∃ B : Fin m → Fin m → k, (∀ j i, j < i → B j i = 0) ∧ (∀ j, u j = ∑ i, B j i • u' i) ∧ ∀ j, A j j * B j j = 1 := by
  classical
  let M : Matrix (Fin m) (Fin m) k := Matrix.of A
  have key : ∀ d : Fin m → k, ∑ i, d i • u' i = ∑ i, Matrix.vecMul d M i • u i := fun d => by
    simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul, Matrix.vecMul, dotProduct, M, Matrix.of_apply]
    exact Finset.sum_comm
  have hM : IsUnit M := Matrix.vecMul_injective_iff_isUnit.1 fun d d' h => hi _ _ (by
    rw [key, key]; exact congrArg (fun c : Fin m → k => ∑ i, c i • u i) h)
  obtain ⟨I⟩ := hM.nonempty_invertible
  have ht : M.BlockTriangular OrderDual.toDual := fun j i h => hA j i h
  have hB : ∀ j i, j < i → M⁻¹ j i = 0 := fun j i h => Matrix.blockTriangular_inv_of_blockTriangular ht h
  have h2 : ∀ j, u j = ∑ i, M⁻¹ j i • u' i := fun j => by
    rw [key, show Matrix.vecMul (M⁻¹ j) M = (M⁻¹ * M) j from rfl, Matrix.inv_mul_of_invertible]
    simp [Matrix.one_apply]
  refine ⟨fun j i => M⁻¹ j i, hB, h2, fun j => ?_⟩
  obtain ⟨e, -, he, h⟩ := lin_comp (fun j i => M⁻¹ j i) hB h2 (A j) j (hA j)
  have := hi e (Pi.single j 1) (by rw [← h, ← hu]; simp [Pi.single_apply])
  rw [← he, this, Pi.single_eq_same]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

section Tan

variable {k : Type} [Field k] (x : Sp k ⟶ X) {m : ℕ}

def Ind (u : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def Tri (u u' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  ∀ j, ∃ cf : Fin m → k, (∀ i, j < i → cf i = 0) ∧ IsCombAtG t x u cf (u' j)

variable {t x} {u u' u'' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)}

theorem comb_iff (U : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (U i)).left) a w ↔ w = (tv (∑ i, a i • U i)).left := by
  have h := (GlobalTheory.LieMet.isComb_iff U a _).2 rfl
  refine ⟨fun h' => ?_, fun e => e ▸ h⟩
  exact ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h').symm.trans
    ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h)

theorem exists_tan (h : ∀ i, IsTanAtG t x (u i)) : ∃ U : Fin m → TanM x t.G, u = fun i => (tv (U i)).left :=
  ⟨fun i => tanOf (h i), rfl⟩

theorem Tri.comp (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u') {d : Fin m → k}
    {j : Fin m} (hd : ∀ i, j < i → d i = 0) {w : Sp (DualNumber k) ⟶ t.G.left} (hw : IsCombAtG t x u' d w) :
    ∃ c e : Fin m → k, IsCombAtG t x u c (u' j) ∧ (∀ i, j < i → e i = 0) ∧ e j = d j * c j ∧ IsCombAtG t x u e w := by
  obtain ⟨U, rfl⟩ := exists_tan hu
  obtain ⟨U', rfl⟩ := exists_tan hu'
  choose A hA hc using h
  obtain ⟨e, h1, h2, h3⟩ := lin_comp A hA (fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)) d j hd
  exact ⟨A j, e, hc j, h1, h2, (comb_iff _ _ _).2 (h3 ▸ (comb_iff _ _ _).1 hw)⟩

theorem Tri.trans (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u')
    (h' : Tri t x u' u'') : Tri t x u u'' := fun j => by
  obtain ⟨d, hd, hw⟩ := h' j
  obtain ⟨-, e, -, h1, -, h2⟩ := h.comp hu hu' hd hw
  exact ⟨e, h1, h2⟩

theorem Tri.symm (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') : Tri t x u' u ∧
    ∀ j c d, IsCombAtG t x u c (u' j) → IsCombAtG t x u' d (u j) → c j * d j = 1 := by
  obtain ⟨U, rfl⟩ := exists_tan hu.1
  obtain ⟨U', rfl⟩ := exists_tan hu'.1
  choose A hA hc using h
  obtain ⟨B, h1, h2, h3⟩ := lin_symm (u := U) (u' := U') (fun c c' e => hu'.2 c c' _ ((GlobalTheory.LieMet.isComb_iff _ _ _).2 rfl)
    ((GlobalTheory.LieMet.isComb_iff _ _ _).2 e)) A hA fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)
  refine ⟨fun j => ⟨B j, h1 j, (GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)⟩, fun j c d hc' hd => ?_⟩
  rw [hu.2 _ _ _ hc' (hc j), hu'.2 _ _ _ hd ((GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)), h3]

theorem Tri.diag (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') {j : Fin m} {c : Fin m → k}
    (hc : IsCombAtG t x u c (u' j)) : c j ≠ 0 ∧ ∀ i, j < i → c i = 0 := by
  obtain ⟨h1, h2⟩ := h.symm hu hu'
  obtain ⟨d, -, hd⟩ := h1 j
  obtain ⟨c', h3, h4⟩ := h j
  exact ⟨left_ne_zero_of_mul_eq_one (h2 j c d hc hd), hu.2 _ _ _ hc h4 ▸ h3⟩

end Tan

section Norm

variable {t} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}


end Norm

end GlobalTheory.ShFam.Pad.Pull
end
end
