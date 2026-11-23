module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
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
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AxisTriv

theorem lift_comp_sq {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare β β₂) (a b : B ⟶ B) (a' b' : A ⟶ A)
    (ha : a.left ≫ β = β ≫ a'.left) (hb : b.left ≫ β = β ≫ b'.left) :
    (lift a b).left ≫ β₂ = β ≫ (lift a' b').left := by
  have k₁ : (lift a b).left ≫ (fst B B).left = a.left := congrArg (fun z => z.left) (lift_fst a b)
  have k₂ : (lift a' b').left ≫ (fst A A).left = a'.left := congrArg (fun z => z.left) (lift_fst a' b')
  have l₁ : (lift a b).left ≫ (snd B B).left = b.left := congrArg (fun z => z.left) (lift_snd a b)
  have l₂ : (lift a' b').left ≫ (snd A A).left = b'.left := congrArg (fun z => z.left) (lift_snd a' b')
  apply pullback.hom_ext
  · change ((lift a b).left ≫ β₂) ≫ (fst A A).left = (β ≫ (lift a' b').left) ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, k₁, Category.assoc, k₂, ha]
  · change ((lift a b).left ≫ β₂) ≫ (snd A A).left = (β ≫ (lift a' b').left) ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, l₁, Category.assoc, l₂, hb]

theorem exists_gen_pull {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} (hP : P.IsLB) (a : B ⟶ B ⊗ B) (a' : A ⟶ A ⊗ A)
    (e : a.left ≫ β₂ = β ≫ a'.left) (h : ∃ u : (P.pull a'.left).Gen, u.IsGen) :
    ∃ u : ((P.pull β₂).pull a.left).Gen, u.IsGen := by
  obtain ⟨u, hu⟩ := h
  have i₁ : LBIso ((P.pull β₂).pull a.left) (P.pull (a.left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (LB.isLB_pull hP β₂)) a.left
  have i₂ : LBIso ((P.pull a'.left).pull β) (P.pull (β ≫ a'.left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (LB.isLB_pull hP a'.left)) β
  rw [e] at i₁
  have i := LBIso.trans (LB.isLB_pull (LB.isLB_pull hP _) _) (LB.isLB_pull hP _) (LB.isLB_pull (LB.isLB_pull hP _) _) i₁ i₂.symm
  obtain ⟨w, hw⟩ := i.symm
  obtain ⟨v, hv, -⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_pull (LB.isLB_pull hP _) _) (LB.isLB_pull (LB.isLB_pull hP _) _)
    w hw (pullGenLB u β) (pullGenLB_isGen hu β)
  exact ⟨v, hv⟩

theorem axes_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left), P.IsLB → (∃ u : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, u.IsGen) → ∀ (t : T ⟶ S) (B : Over T) [GrpObj B] (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsGrpPullback B A t β → IsSquare β β₂ → (∃ u : ((P.pull β₂).pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) ∧ (∃ u : ((P.pull β₂).pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) := by
  intro S T A _ P hP h₁ h₂ t B _ β β₂ h hs
  have e₁ := GlobalTheory.PPAS.one_comp_of_isGrpPullback h
  exact ⟨exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ e₁ rfl) h₁,
    exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ rfl e₁) h₂⟩

end GlobalTheory.AxisTriv
end
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.GramAdj

theorem exists_endo_of_adjoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (β : D.La → D.La → ℤ), (∀ x y z, β (x + y) z = β x z + β y z) → (∀ x y z, β x (y + z) = β x y + β x z) → (∀ (s : 𝓞 E) x y, β (s • x) y = β x (H.bar s • y)) → ∃ γ : D.La →+ D.La, (∀ (s : 𝓞 E) x, γ (s • x) = s • γ x) ∧ ∀ x y, β x y = D.EF (γ x) y := by
  intro E _ _ _ H D β hl hr hs
  let f : D.La → (D.La →ₗ[ℤ] ℤ) := fun x => (AddMonoidHom.mk' (β x) (hr x)).toIntLinearMap
  have hf : ∀ x y, f x y = β x y := fun _ _ => rfl
  let e := Equiv.ofBijective D.EF D.unimod
  have he : ∀ g, D.EF (e.symm g) = g := fun g => e.apply_symm_apply g
  have key : ∀ x y, D.EF (e.symm (f x)) y = β x y := fun x y => by rw [he, hf]
  have hadd : ∀ x x', e.symm (f (x + x')) = e.symm (f x) + e.symm (f x') := by
    intro x x'
    apply D.unimod.1
    ext y
    simp only [map_add (f := _), LinearMap.add_apply, key, hl]
  refine ⟨AddMonoidHom.mk' (fun x => e.symm (f x)) hadd, ?_, ?_⟩
  · intro s x
    show e.symm (f (s • x)) = s • e.symm (f x)
    apply D.unimod.1
    ext y
    rw [key, hs, ← key, D.adj]
  · intro x y
    show β x y = D.EF (e.symm (f x)) y
    rw [key]

end GlobalTheory.GramAdj
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.SmoothStalk

theorem finitePresentation_algX {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [LocallyOfFinitePresentation p]
    (U : X.affineOpens) : (algX p U.1).FinitePresentation := by
  have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation p inferInstance ⟨⊤, isAffineOpen_top _⟩ U le_top
  refine RingHom.FinitePresentation.comp h ?_
  refine RingHom.FinitePresentation.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective ?_
  have : RingHom.ker (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective
  rw [this]; exact Submodule.fg_bot

theorem smooth_stalk : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1), letI := (algX p U.1).toAlgebra; letI := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra; Algebra.FinitePresentation k Γ(X, U.1) ∧ Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  intro k _ X p n _ U x hx
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  refine ⟨?_, ?_⟩
  · exact finitePresentation_algX p U
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) p ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(X, U.1)), x ∈ X.basicOpen (t : Γ(X, U.1)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff U.2).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen U.2 (t : Γ(X, U.1))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(X, X.basicOpen (t : Γ(X, U.1))))
  set V := X.basicOpen (t : Γ(X, U.1))
  have hVU : V ≤ U.1 := X.basicOpen_le _
  have h₂ : (algX p V).IsStandardSmoothOfRelativeDimension n := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p hVU]
    exact h₁
  have hV : IsAffineOpen V := U.2.basicOpen _
  letI iA : Algebra k Γ(X, V) := (algX p V).toAlgebra
  letI iS : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxt).hom.toAlgebra
  letI iK : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra
  have hcomp : ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)) = (X.presheaf.germ V x hxt).hom.comp (algX p V) := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p hVU, ← RingHom.comp_assoc]
    congr 1
    rw [← X.presheaf.germ_res (homOfLE hVU) x hxt]
    rfl
  haveI : IsScalarTower k Γ(X, V) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' hcomp
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := h₂
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxt⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxt⟩
  haveI : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf ⟨x, hxt⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, V) (X.presheaf.stalk x)
  haveI : Nontrivial Γ(X, V) := (X.presheaf.germ V x hxt).hom.domain_nontrivial
  haveI : Module.Free Γ(X, V) Ω[Γ(X, V)⁄k] := by
    obtain ⟨ι, σ, _, _, P, -⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V)›.out
    exact P.free_kaehlerDifferential
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := Γ(X, V)) n
  haveI : Module.Finite Γ(X, V) Ω[Γ(X, V)⁄k] := Module.finite_of_rank_eq_nat hr
  have hfr : Module.finrank Γ(X, V) Ω[Γ(X, V)⁄k] = n := Module.finrank_eq_of_rank_eq hr
  let b := Module.Free.chooseBasis Γ(X, V) Ω[Γ(X, V)⁄k]
  let b' := IsBaseChange.basis b hbc
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  rw [Module.finrank_eq_card_basis b', ← hfr, Module.finrank_eq_card_basis b]

end GlobalTheory.SmoothStalk
end
