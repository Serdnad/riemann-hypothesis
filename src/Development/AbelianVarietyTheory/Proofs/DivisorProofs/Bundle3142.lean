module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle020
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem genPt_map_unique {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V)
    (κ κ' : Sp (FractionRing V) ⟶ Sp (FractionRing R)) (h : κ ≫ jK R = jK V ≫ spMap θ)
    (h' : κ' ≫ jK R = jK V ≫ spMap θ) : κ = κ' := by
  obtain ⟨a, rfl⟩ : ∃ a, Spec.map a = κ := ⟨_, Spec.map_preimage κ⟩
  obtain ⟨a', rfl⟩ : ∃ a, Spec.map a = κ' := ⟨_, Spec.map_preimage κ'⟩
  have e : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ a) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ a') := by
    rw [Spec.map_comp, Spec.map_comp]
    exact h.trans h'.symm
  have e2 := Spec.map_injective e
  congr 1
  ext1
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  exact congrArg CommRingCat.Hom.hom e2

end GlobalTheory.TInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.baseEq_of_sameImage : ∀ {o R V : Type} [CommRing o] [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {X : Scheme.{0}} (sX : X ⟶ Sp o) (y : Sp (FractionRing R) ⟶ X) (b : o →+* R), y ≫ sX = jK R ≫ spMap b → ∀ (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → θ₁.comp b = θ₂.comp b := by
  intro o R V _ _ _ _ _ X sX y b hy θ₁ θ₂ κ₁ κ₂ h₁ h₂ hκ
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp b) = κ ≫ y ≫ sX := by
    intro θ κ h
    rw [hy, ← Category.assoc, h, Category.assoc]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl
  have e : jK V ≫ spMap (θ₁.comp b) = jK V ≫ spMap (θ₂.comp b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hκ, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisFixedSectionExtension

theorem extend_section {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of V)) [IsFinite p] (g : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ s = g := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ X.isoSpec.hom)
  obtain ⟨π, hπ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  have hfin : π.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hπ]
    infer_instance
  have hcomp : π ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hπ, Category.assoc, Iso.hom_inv_id_assoc, hg]
  have hc : ∀ v : V, φ.hom (π.hom v) = algebraMap V (FractionRing V) v := fun v =>
    congrArg (fun f => f.hom v) hcomp
  have hmem : ∀ a, φ.hom a ∈ (algebraMap V (FractionRing V)).range := by
    intro a
    obtain ⟨q, hq, hqa⟩ := hfin.to_isIntegral a
    have hint : IsIntegral V (φ.hom a) := by
      refine ⟨q, hq, ?_⟩
      have h1 := Polynomial.hom_eval₂ q π.hom φ.hom a
      rw [hqa, map_zero] at h1
      have h2 : φ.hom.comp π.hom = algebraMap V (FractionRing V) := RingHom.ext hc
      rw [h2] at h1
      exact h1.symm
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap V (FractionRing V)).rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* V := e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)
  have hψ : ∀ a, algebraMap V (FractionRing V) (ψ a) = φ.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict _ hmem a))
  have hψφ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V (FractionRing V)) = φ := by
    ext a
    exact hψ a
  have hπψ : π ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
    ext v
    exact hinj ((hψ _).trans (hc v))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hπ, ← Spec.map_comp, hπψ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψφ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem exists_section_of_galoisFixed : ∀ (V : Type) [inst : CommRing V] [inst_1 : IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)), AlgebraicGeometry.IsFinite (CategoryTheory.Over.hom N) → ∀ (nb : ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ (σ : Gal(AlgebraicClosure (FractionRing V)/FractionRing V)), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (AlgHom.toRingHom (↑σ : AlgebraicClosure (FractionRing V) →ₐ[FractionRing V] AlgebraicClosure (FractionRing V)))) (CategoryTheory.Over.Hom.left nb) = CategoryTheory.Over.Hom.left nb) → ∃ (s : CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)) ⟶ N), nb = CategoryTheory.CategoryStruct.comp (CategoryTheory.SemiCartesianMonoidalCategory.toUnit (ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)))) s := by
  intro V _ _ _ hV N hN nb hfix
  haveI := hV
  haveI := hN
  haveI : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨g, hg⟩ := GlobalTheory.TorsDescent.descend_point (K := FractionRing V) N.left nb.left hfix
  have hg' : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫ g =
      nb.left := hg
  have hw : nb.left ≫ N.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := Over.w nb
  have hgp : g ≫ N.hom = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (g ≫ N.hom)
    rw [← hχ]
    congr 1
    have h1 : χ ≫ CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        CommRingCat.ofHom (algebraMap V (FractionRing V)) ≫
          CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, hχ, ← hw, ← hg', Category.assoc]
    ext v
    exact (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective
      (congrArg (fun f => f.hom v) h1)
  obtain ⟨s, hs, hsg⟩ := extend_section N.left N.hom g hgp
  refine ⟨Over.homMk s hs, ?_⟩
  apply Over.OverMorphism.ext
  show nb.left = (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) ≫ s
  rw [Category.assoc, hsg, hg']

end GlobalTheory.GaloisFixedSectionExtension
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.eq_of_specializes_semiAbelian_square_same_projections : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ p q : (G ⊗ G).left, (fst G G).left p = x → (fst G G).left q = x → (snd G G).left p = (snd G G).left q → p ⤳ q → p = q := by
  first | exact @GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq | exact GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq | (intros; apply GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isClosed_image_snd_of_subset_semiAbelian_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} → IsClosed ((snd G G).left '' N) := by
  first | exact @GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | exact GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | (intros; apply GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ


theorem _root_.GlobalTheory.T.isomorphism_mon_hom_descends_finite_extension : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (A₁ A₂ : Over (Sp K)) [GrpObj A₁] [GrpObj A₂], IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ (f : (Over.pullback (spMap β)).obj A₁ ≅ (Over.pullback (spMap β)).obj A₂), IsMonHom f.hom → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω : Type) (_ : Field Ω) (j : L →+* Ω) (l : K' →+* Ω) (φ : (Over.pullback (spMap io)).obj A₁ ≅ (Over.pullback (spMap io)).obj A₂), io.Finite ∧ l.comp io = j.comp β ∧ IsMonHom φ.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A₁.hom (spMap β)) (p' : Z ⟶ pullback A₁.hom (spMap io)) (t : Z ⟶ Sp Ω), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.hom.left ≫ pullback.fst _ _ = p' ≫ φ.hom.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.IsoFinExt.exists_finite_iso | exact GlobalTheory.IsoFinExt.exists_finite_iso | (intros; apply GlobalTheory.IsoFinExt.exists_finite_iso <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_int_eq_mul_of_ne_zero {E : Type} [Field E] [NumberField E] (t : 𝓞 E) (ht : t ≠ 0) :
    ∃ (N : ℤ) (c : 𝓞 E), N ≠ 0 ∧ (N : 𝓞 E) = t * c := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {t}))
  refine ⟨(Ideal.absNorm (Ideal.span {t}) : ℤ), c, ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht
    exact_mod_cast this
  · rw [Int.cast_natCast, ← hc, mul_comm]

theorem eq_zero_of_forall_theta_mul {E : Type} [Field E] [NumberField E] {θ : 𝓞 E →+ ℤ} (hθ : θ ≠ 0)
    {t : 𝓞 E} (h : ∀ u, θ (t * u) = 0) : t = 0 := by
  by_contra ht
  obtain ⟨N, c, hN, hc⟩ := exists_int_eq_mul_of_ne_zero t ht
  apply hθ
  ext v
  have := h (c * v)
  rw [← mul_assoc, ← hc, ← zsmul_eq_mul, map_zsmul, smul_eq_mul] at this
  simpa [hN] using this

theorem exists_linear_theta_factor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (Z' : Submodule (𝓞 E) D.La) (θ : 𝓞 E →+ ℤ) (s : 𝓞 E) (hs : s ≠ 0)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) (w : D.La),
    ∃ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, ∀ x : Z', θ (ℓ x) = D.EF x (H.bar s • w) := by
  intro E _ _ _ H D Z' θ s hs hgen w
  have hθ : θ ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ (𝓞 E)).repr s i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hs ((Module.Free.chooseBasis ℤ (𝓞 E)).repr.injective (by ext i; simp [hne i]))
    obtain ⟨t, ht⟩ := hgen ((Module.Free.chooseBasis ℤ (𝓞 E)).coord i).toAddMonoidHom
    have := ht 1
    simp [h0] at this
    exact hi this
  have uniq : ∀ t t' : 𝓞 E, (∀ u, θ (t * u) = θ (t' * u)) → t = t' := fun t t' h =>
    sub_eq_zero.1 (eq_zero_of_forall_theta_mul hθ fun u => by rw [sub_mul, map_sub, h, sub_self])
  let ψ : D.La → 𝓞 E →+ ℤ := fun x => AddMonoidHom.mk' (fun u => D.EF (u • x) w) (fun a b => by simp [add_smul])
  choose T hT using fun x : Z' => hgen (ψ x)
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, fun x => ?_⟩
  · intro x y
    apply uniq
    intro u
    rw [← hT (x + y) u, add_mul, map_add (f := _), ← hT x u, ← hT y u]
    simp [ψ, smul_add]
  · intro c x
    show T (c • x) = c * T x
    apply uniq
    intro u
    rw [← hT (c • x) u, show c * T x * u = T x * (c * u) by ring, ← hT x (c * u)]
    simp only [ψ, AddMonoidHom.mk'_apply, Submodule.coe_smul, smul_smul]
    rw [show s * u * c = s * (c * u) by ring]
  · show θ (T x) = _
    have := hT x 1
    rw [mul_one, mul_one] at this
    rw [← this]
    simp only [ψ, AddMonoidHom.mk'_apply]
    exact D.adj s x w

end GlobalTheory.LowFilt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.weilPairing_eq_of_fractionField_domain : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (e : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ Over.mk (spMap f)), e.left = spMap (algebraMap W L) → ∀ (n : ℕ) (x y : Over.mk (spMap f) ⟶ P.A), x ^ n = 1 → y ^ n = 1 → ∀ (w : Wˣ), Out.WeilIs P.A P.L n (e ≫ x) (e ≫ y) (unitOn (Units.map (algebraMap W L).toMonoidHom w)) → Out.WeilIs P.A P.L n x y (unitOn w) := by
  first | exact @GlobalTheory.WeilDomain.weilIs_of_fractionField | exact GlobalTheory.WeilDomain.weilIs_of_fractionField | (intros; apply GlobalTheory.WeilDomain.weilIs_of_fractionField <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.generator_proportionality_spreads_from_generic : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (W : (Sp R).Opens) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (W.toScheme ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (W.toScheme ⟶ X)) (ε₂ : K₂ → ℤ), (∀ (U : Type) [CommGroup U] (h : (W.toScheme ⟶ X) → U), ∏ i, h (φ₁ i) ^ ε₁ i = ∏ i, h (φ₂ i) ^ ε₂ i) → ∀ (t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)), t₁.IsGen → t₂.IsGen → ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good L z J → val t₁ lam z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val t₂ lam z J) → ∀ z J, Good L z J → val t₁ g z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val t₂ g z J := by
  first | exact @GlobalTheory.GenSpread.val_spread | exact GlobalTheory.GenSpread.val_spread | (intros; apply GlobalTheory.GenSpread.val_spread <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem exists_qk_zero_over : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ b : TF (R := V) F ⟶ D.P.A, b ^ k = 1 → ∃ p : QkPt D F k, p.y = 0 ∧ p.g.b = b := by
  intro V _ _ D hB F _ _ _ k hk b hb
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  exact exists_qk_over (F := F) hJ hB hk 0 b (by rw [hb, cPoint_zero])

end GlobalTheory.TInj
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowFilt

theorem exists_equiv_y_eq_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R), D₀.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 0 < n → ∀ p : QkPt D₀ F n,
    (∃ q : QkPt D₀ F n, QkPt.Equiv D₀ F p q ∧ q.y = 0) ↔ ∃ e, p.y = n • e := by
  intro R _ _ D₀ hB F _ _ n _ p
  constructor
  · rintro ⟨q, hq, hy⟩
    obtain ⟨z, hz, -⟩ := (GlobalTheory.TorusExt.equiv_iff hB p q).1 hq
    refine ⟨-z, ?_⟩
    rw [smul_neg, eq_neg_iff_add_eq_zero, ← hz, hy]
  · rintro ⟨e, he⟩
    refine ⟨GlobalTheory.TorusExt.qkShift hB p (-e), GlobalTheory.TorusExt.equiv_qkShift hB p (-e), ?_⟩
    show p.y + n • (-e) = 0
    rw [he, smul_neg, add_neg_cancel]

end GlobalTheory.LowFilt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem qkPt_g_eq_of_equiv : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D F k, p.y = p'.y → QkPt.Equiv D F p p' → p.g = p'.g := by
  intro V _ _ D hB F _ _ k hk p p' hy ⟨z, hz, h, hi, ha⟩
  letI := GlobalTheory.TorusExt.gtGroup D F
  have hkz : k • z = 0 := by
    rw [hy] at hz
    exact left_eq_add.mp hz
  have z0 : z = 0 := by
    have : ((k : ℤ)) • z = 0 := by rw [natCast_zsmul]; exact hkz
    rcases smul_eq_zero.mp this with h0 | h0
    · omega
    · exact h0
  subst z0
  have h0 : h = 0 := by
    obtain ⟨w, hw, g, hg, hadd⟩ := qk_equiv_refl hB p
    have hw0 : w = 0 := by
      have hkw : k • w = 0 := left_eq_add.mp hw
      have hwz : (k : ℤ) • w = 0 := by rw [natCast_zsmul]; exact hkw
      rcases smul_eq_zero.mp hwz with hk0 | hw0
      · omega
      · exact hw0
    subst w
    have he : h = g := GlobalTheory.TorusExt.isIota_unique hi hg
    have heq := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hadd
    have hg0 : g = 0 := by
      have : p.g + g = p.g + 0 := by simpa using heq.symm
      exact add_left_cancel this
    exact he.trans hg0
  rw [(GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ha, h0, add_zero]

end GlobalTheory.TInj
end
