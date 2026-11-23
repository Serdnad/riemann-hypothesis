module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle017
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle952
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle928
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FactorialLocus

open ReciprocityTheory.AnForm.R

theorem exists_affine_gen {X : Scheme.{0}} [IsLocallyNoetherian X] (G : X.IdealSheafData) (x : X)
    (t : X.presheaf.stalk x) (htnzd : t ∈ nonZeroDivisors (X.presheaf.stalk x))
    (ht : FinalTheorems.stalkId G x = Ideal.span {t}) :
    ∃ (U : X.affineOpens) (f : Γ(X, U.1)), x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧
      G.ideal U = Ideal.span {f} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have hx : x ∈ U'.1 := hxU
  rw [ds_stalkId_eq_map G U' x hx] at ht
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U'
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom := rfl
  rw [Ideal.map] at ht
  obtain ⟨y, ⟨a, haI, rfl⟩, c, hc⟩ := ds_gen_of_span _ t htnzd ht
  have hmap : (G.ideal U').map (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(X, U) (X.presheaf.stalk x) a} := by
    rw [halg, Ideal.map, ht, hc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(X, U) (X.presheaf.stalk x) a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
    rw [halg, hc]
    exact mul_mem (IsUnit.mem_nonZeroDivisors c.isUnit) htnzd
  obtain ⟨σ, hσP, hT⟩ := ds_spread (hU.primeIdealOf ⟨x, hx⟩).asIdeal (G.ideal U') a haI hmap hnzd
  haveI := hU.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(X, X.basicOpen σ)
  refine ⟨X.affineBasicOpen (U := U') σ, algebraMap Γ(X, U) Γ(X, X.basicOpen σ) a, ?_, h2, ?_⟩
  · show x ∈ X.basicOpen σ
    rw [X.mem_basicOpen σ x hx]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal σ).2 hσP
  · rw [← G.map_ideal_basicOpen U' σ]
    exact h1

theorem stalkId_eq_span_of_mem {X : Scheme.{0}} (G : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hf : f ∈ nonZeroDivisors Γ(X, U.1)) (hG : G.ideal U = Ideal.span {f})
    (y : X) (hy : y ∈ U.1) :
    ∃ t ∈ nonZeroDivisors (X.presheaf.stalk y), FinalTheorems.stalkId G y = Ideal.span {t} := by
  refine ⟨X.presheaf.germ U.1 y hy f, ?_, ?_⟩
  · letI : Algebra Γ(X, U.1) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hy⟩
    haveI := U.2.isLocalization_stalk ⟨y, hy⟩
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl hf
  · rw [ds_stalkId_eq_map G U y hy, hG, Ideal.map_span, Set.image_singleton]

theorem effCartier_comap_of_local {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f]
    (hI : ∀ x : X, ∃ (U : Y.affineOpens) (h : Γ(Y, U.1)), f x ∈ U.1 ∧
      h ∈ nonZeroDivisors Γ(Y, U.1) ∧ I.ideal U = Ideal.span {h}) :
    FinalTheorems.EffCartier (I.comap f) := by
  intro x
  obtain ⟨U, h, hxU, hh, hU⟩ := hI x
  obtain ⟨r, hrle, hxr⟩ := U.2.exists_basicOpen_le (V := f.opensRange) ⟨f x, ⟨x, rfl⟩⟩ hxU
  have himg : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) = Y.basicOpen r := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 hrle]
  have hUX : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r) := by
    rw [← f.isAffineOpen_iff_of_isOpenImmersion, himg]; exact U.2.basicOpen r
  have hle : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) ≤ U.1 := himg.le.trans (Y.basicOpen_le r)
  have hnzd : ∀ (O : Y.Opens) (hO : O = Y.basicOpen r) (hOU : O ≤ U.1),
      Y.presheaf.map (homOfLE hOU).op h ∈ nonZeroDivisors Γ(Y, O) := by
    rintro O rfl hOU
    have := U.2.isLocalization_basicOpen r
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers r) hh
  let e := (f.appIso (f ⁻¹ᵁ Y.basicOpen r)).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hUX⟩, e (Y.presheaf.map (homOfLE hle).op h), hxr, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors e (hnzd _ himg hle)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    rw [← I.map_ideal (U := ⟨_, (f.isAffineOpen_iff_of_isOpenImmersion).2 hUX⟩) (V := U) hle, hU,
      Ideal.map_span, Set.image_singleton]
    rw [show ((f.appIso (f ⁻¹ᵁ Y.basicOpen r)).inv.hom : _ →+* _) = (e.symm : _ →+* _) from rfl,
      Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
    rfl

theorem exists_isLocus : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (V : X.Opens), IsAffineOpen V → (V : Set X).Nonempty → ∃ W : X.Opens, V ≤ W ∧ (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) → x ∈ W) ∧ ∃ c : Pic W.toScheme, IsLocus c (W.ι ⁻¹ᵁ V) := by
  intro X _ _ _ V hV hne
  have hι : IsAffineHom V.ι :=
    haveI : IsAffine V := hV
    haveI : IsAffineHom (V.ι ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  let G := Scheme.IdealSheafData.vanishingIdeal V.compl
  let P : X → Prop := fun x =>
    ∃ t ∈ nonZeroDivisors (X.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}
  have hopen : IsOpen {x | P x} := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨t, ht, htG⟩ := hx
    obtain ⟨U, f, hxU, hf, hG⟩ := exists_affine_gen G x t ht htG
    exact ⟨U.1, fun y hy => stalkId_eq_span_of_mem G U f hf hG y hy, U.1.isOpen, hxU⟩
  let W : X.Opens := ⟨{x | P x}, hopen⟩
  have hVW : V ≤ W := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ V ↔ (1 : X.presheaf.stalk x) ∉ q.asIdeal := fun q => by
      refine iff_of_true ?_ fun h1 => q.2.ne_top ((Ideal.eq_top_iff_one _).2 h1)
      have hs : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hs
      exact Specializes.mem_open hs V.isOpen hx
    rw [GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl V x 1 h, Ideal.span_singleton_one,
      Ideal.radical_top]
  have hfac : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) → x ∈ W := by
    intro x hufd
    have hd : IsDomain (X.presheaf.stalk x) := inferInstance
    have hn : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    have hA : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ V) := by
      have : IsAffineHom (X.fromSpecStalk x ⁻¹ᵁ V).ι :=
        MorphismProperty.of_isPullback (P := @IsAffineHom)
          (isPullback_morphismRestrict (X.fromSpecStalk x) V) hι
      exact isAffine_of_isAffineHom (X.fromSpecStalk x ⁻¹ᵁ V).ι
    have hg : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨q, hq⟩ := hg
    have hqV : q ∈ X.fromSpecStalk x ⁻¹ᵁ V := by
      change X.fromSpecStalk x q ∈ V
      rw [hq]
      exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 (by simpa using hne)
    obtain ⟨a, ha⟩ := @GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization
      (X.presheaf.stalk x) (X.presheaf.stalk x).commRing hd hn hufd
      (X.fromSpecStalk x ⁻¹ᵁ V) hA ⟨q, hqV⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ V ↔ a ∉ q.asIdeal := fun q =>
      iff_of_eq (congrArg (fun V => q ∈ V) ha)
    have ha0 : a ≠ 0 := fun h0 => (h q).1 hqV (h0 ▸ zero_mem _)
    show P x
    simp only [P, G]
    rw [GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl V x a h]
    exact GlobalTheory.AffineComplement.exists_radical_span_singleton_eq ha0
  refine ⟨W, hVW, hfac, ?_⟩
  have hE : FinalTheorems.EffCartier (G.comap W.ι) := by
    refine effCartier_comap_of_local G W.ι fun y => ?_
    have hy : P (W.ι y) := y.2
    obtain ⟨t, ht, htG⟩ := hy
    exact exists_affine_gen G _ t ht htG
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hE
  refine ⟨cls D.lb D.isLB_lb, D.lb, D.isLB_lb, D.canonical, rfl, TopologicalSpace.Opens.ext ?_⟩
  refine D.coe_nonzeroLocus_canonical.trans ?_
  rw [hD, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  ext y
  simp

end GlobalTheory.FactorialLocus
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlgComplete

open GlobalTheory.CechPic GlobalTheory.ZV

theorem exists_lineBundle_of_reductions : GlobalTheory.Published.FormalAlgebraisation → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProjBy X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) → ∃ M : LB X.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro hP R _ _ I hI X hX Y β b hb hc N hN hv
  have hpr : IsProper X.hom := isProper_of_isProjBy R _ _ hX
  obtain ⟨H, hH, m, σ, hσ⟩ := hX
  have hA : IsAmpleLB H := isAmpleLB_of_veryAmpleBy hσ
  have hY : ∀ e, IsProper (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @IsProper) (hb e) hpr
  have hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e) := fun e => by
    refine IsPullback.of_right (h₁₂ := b (e + 1)) (h₂₂ := thick R I (e + 1)) (v₁₃ := X.hom) ?_ ?_ (hb (e + 1))
    · rw [hc, thickTrans_comp]
      exact hb e
    · have : Mono (thick R I (e + 1)) := by
        have : IsClosedImmersion (thick R I (e + 1)) :=
          IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
        infer_instance
      rw [← cancel_mono (thick R I (e + 1)), Category.assoc, Category.assoc, thickTrans_comp, ← (hb (e + 1)).w,
        ← Category.assoc, hc, (hb e).w]
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => LB.isLB_pull hH _
  have hA₀ : IsAmpleLB (H.pull (b 0)) := by
    have : IsClosedImmersion (thick R I 0) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsClosedImmersion (b 0) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hb 0).flip this
    exact hA.pull_of_isClosedImmersion _
  have := hY 0
  obtain ⟨t, ht⟩ := (AmpleDominates.eventually_isAmpleLB (Y 0).hom hA₀ (hN 0)).exists
  have hT : ∀ e, (LB.div (lbPow (H.pull (b e)) t) (N e)).IsLB := fun e =>
    LB.isLB_div (isLB_lbPow (hL e) t) (hN e)
  have eT : ∀ e, cls _ (hT e) = t • CechPic.pull (b e) (cls H hH) - cls _ (hN e) := fun e => by
    rw [cls_div (isLB_lbPow (hL e) t) (hN e), cls_lbPow (hL e), cls_pull hH]
  obtain ⟨X', M, b', hX', hM, -, hb', hc', hM'⟩ := hP.2 R I hI Y β hβ hY
    (fun e => LB.div (lbPow (H.pull (b e)) t) (N e)) hT
    (fun e => (cls_eq_iff (hT e) (LB.isLB_pull (hT (e + 1)) _)).1 (by
      rw [cls_pull (hT (e + 1)), eT, eT, (cls_eq_iff (hN e) (LB.isLB_pull (hN (e + 1)) _)).2 (hv e),
        cls_pull (hN (e + 1)), map_sub, map_nsmul, ← CechPic.pull_comp, hc]))
    ((relAmple_iff_isAmpleLB_of_isAffine (Y 0) (hT 0)).2 ht)
  obtain ⟨g, hg, -⟩ := hP.1.exists_iso hI hb hc hb' hc'
  have hMg : (M.pull g.hom.left).IsLB := LB.isLB_pull hM _
  have hF : (LB.div (lbPow H t) (M.pull g.hom.left)).IsLB := LB.isLB_div (isLB_lbPow hH t) hMg
  refine ⟨_, hF, fun e => (cls_eq_iff (hN e) (LB.isLB_pull hF _)).1 ?_⟩
  have e₁ := (cls_eq_iff (hT e) (LB.isLB_pull hM _)).2 (hM' e)
  rw [eT, cls_pull hM] at e₁
  rw [cls_pull hF, cls_div (isLB_lbPow hH t) hMg, cls_lbPow hH, cls_pull hM, map_sub, map_nsmul,
    ← CechPic.pull_comp, hg, ← e₁, sub_sub_cancel]

end GlobalTheory.LBAlgComplete
end

section

set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer.CloseTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def splitL (I : Type) [Fintype I] (g : ℕ) : (I ⊕ Fin g → ℂ) →L[ℂ] Tot I g :=
  (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun b ↦ ContinuousLinearMap.proj (Sum.inr b))


omit [DecidableEq I] in
theorem shift_eq (w : Fin g → ℂ) (x : I ⊕ Fin g → ℂ) :
    (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : Tot I g) = (0, w) + splitL I g x := by
  ext <;> simp [splitL]

theorem splitL_single (b : Fin g) :
    splitL I g (Pi.single (Sum.inr b) 1) = ((0, Pi.single b 1) : Tot I g) := by
  ext i <;> simp [splitL, Pi.single_apply]


omit [DecidableEq I] in
theorem eventually_shift_mem {W : Opens (Tot I g)} {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0, (0, w) + splitL I g x ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) :=
    continuous_const.add (splitL I g).continuous
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  simpa using hw


omit [DecidableEq I] in
theorem analyticAt_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x)
    (h.analytic _ hw) (analyticAt_const.add ((splitL I g).analyticAt 0)) (by simp)

theorem fderiv_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W)
    (b : Fin g) :
    (fun z ↦ fderiv ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) z (Pi.single (Sum.inr b) 1))
      =ᶠ[𝓝 0] fun x : I ⊕ Fin g → ℂ ↦ (dw b h).fn ((0, w) + splitL I g x) := by
  filter_upwards [eventually_shift_mem hw] with z hz
  have e : HasFDerivAt (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x))
      ((fderiv ℂ h.fn ((0, w) + splitL I g z)).comp (splitL I g)) z :=
    HasFDerivAt.comp (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) z
      (h.analytic _ hz).differentiableAt.hasFDerivAt ((splitL I g).hasFDerivAt.const_add _)
  rw [e.fderiv, ContinuousLinearMap.comp_apply, splitL_single]
  exact (Hol.fn_der _ h hz).symm

end GlobalTheory.AnPer.CloseTaylor


open GlobalTheory.AnPer.CloseTaylor in
theorem GlobalTheory.AnPer.close_of_sliceTaylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D), (∀ i, t i ∈ J) → ∀ (r : ℕ) (n : Fin r → Fin g → D), (∀ j a, n j a ∈ J) → (∀ j a b, n j a * n j b = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens (Tot I g)) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∀ ρ₁ ρ₂ : Hol W →+* D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₁ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun b ↦ ∑ j, n j b) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₂ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun _ ↦ 0) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol W₀)) ρ₁ ρ₂ := by
  intro I _ _ g D _ _ J N hJ t ht r n hn hnn E _ _ _ W W₀ a ha hW ρ₁ ρ₂ h₁ h₂
  induction r generalizing ρ₁ with
  | zero =>
    have : ρ₁ = ρ₂ := RingHom.ext fun h ↦ GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ by
      rw [h₁, h₂]; simp
    rw [this]
    exact Relation.ReflTransGen.refl
  | succ r ih =>
    obtain ⟨ρ', hρ'⟩ := GlobalTheory.T.tensorLift_ev_rho_eq_taylor_slice N (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b)
      (fun s ↦ hJ _ fun c ↦ by
        rcases s c with i | b
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _) W W₀ a ha hW
    refine Relation.ReflTransGen.head (b := (ρ' : Hol W →+* D ⊗[ℂ] Hol W₀)) ?_
      (ih (fun j ↦ n j.succ) (fun j ↦ hn _) (fun j ↦ hnn _) _ hρ')
    refine ⟨fun b ↦ (-n 0 b) ⊗ₜ[ℂ] 1, fun b ↦ Ideal.mem_map_of_mem _ (J.neg_mem (hn 0 b)), fun b c ↦ ?_, fun h ↦ ?_⟩
    · rw [Algebra.TensorProduct.tmul_mul_tmul, neg_mul_neg, hnn, zero_tmul]
    refine GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    have e : (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b) = fun i : I ⊕ Fin g ↦
        (Sum.elim t fun b ↦ ∑ j, n j b) i + (Sum.elim (fun _ ↦ 0) fun b ↦ -n 0 b) i := by
      ext (i | b)
      · simp
      · simp [Fin.sum_univ_succ]
    have hs := GlobalTheory.T.taylor_add_square_zero_nilpotent N (Sum.elim t fun b ↦ ∑ j, n j b) (Sum.elim (fun _ : I ↦ 0) fun b ↦ -n 0 b)
      (fun s hs ↦ hJ s fun c ↦ (Ideal.span_le.2 (by
        rintro _ (⟨i | b, rfl⟩ | ⟨i | b, rfl⟩)
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _
        · exact J.zero_mem
        · exact J.neg_mem (hn 0 b))) (hs c))
      (by rintro (i | b) (j | c) <;> simp [hnn]) _ (analyticAt_shifted h (hW p hp))
    obtain ⟨-, -, -, hcongr, -, -⟩ :=
      GlobalTheory.PeriodFamily.taylor_formal_properties N (Sum.elim t fun b ↦ ∑ j, n j b)

    rw [RingHom.coe_coe, hρ', map_add (f := _), map_sum, h₁, e]
    simp only [map_mul, h₁, shift_eq]
    rw [hs, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add]
    refine congrArg _ (Finset.sum_congr rfl fun b _ ↦ ?_)
    rw [hcongr _ _ (fderiv_shifted h (hW p hp) b)]
    simp
end
end

section

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_shear : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {g : ℕ} (h : (I → ℂ) × (Fin g → ℂ) → ℂ) (τ : (I → ℂ) → Fin g → ℂ) (w : Fin g → ℂ), AnalyticAt ℂ τ 0 → AnalyticAt ℂ h (0, w + τ 0) → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (z, w + τ z)) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun a ↦ GlobalTheory.PeriodFamily.taylor N t (fun z ↦ τ z a) - algebraMap ℂ D (τ 0 a)) (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) := by
  intro I _ _ D _ _ N t ht g h τ w hτ hh
  have hτa : ∀ a, AnalyticAt ℂ (fun z ↦ τ z a) 0 := fun a ↦ analyticAt_pi_iff.1 hτ a
  have hco : ∀ {J : Type} [Fintype J] (j : J) (x : J → ℂ), AnalyticAt ℂ (fun z : J → ℂ ↦ z j) x :=
    fun j x ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) j).analyticAt x
  have hΦ : AnalyticAt ℂ (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 := by
    refine analyticAt_pi_iff.2 ?_
    rintro (i | a)
    · exact hco i 0
    · exact (hτa a).sub analyticAt_const
  have hΦ0 : (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 = 0 := by
    funext k
    rcases k with i | a <;> simp
  have hH : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) 0 := by
    have hin : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
        ((fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)) : (I → ℂ) × (Fin g → ℂ))) 0 := by
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ hco _ 0) ?_
      refine analyticAt_pi_iff.2 fun a ↦ ?_
      exact (analyticAt_const (v := (w + τ 0) a)).add (hco (Sum.inr a) 0)
    refine AnalyticAt.comp_of_eq hh hin ?_
    ext <;> simp
  have key := GlobalTheory.T.taylor_comp_eq_taylor_taylor_of_analyticAt N t ht _ _ hΦ hΦ0 hH
  obtain ⟨hadd, -, hconst, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have e1 : (fun z : I → ℂ ↦ h (z, w + τ z)) = fun z : I → ℂ ↦
      (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)))
        (Sum.elim z (fun a ↦ τ z a - τ 0 a)) := by
    funext z
    congr 1
    ext <;> simp
  rw [e1, key]
  congr 1
  funext k
  rcases k with i | a
  · exact (GlobalTheory.T.taylor_coord_and_taylor_eval_of_prod_eq_zero N t ht).1 i
  · have := hadd (fun z ↦ τ z a) (fun _ ↦ - τ 0 a) (hτa a) analyticAt_const
    rw [hconst, map_neg] at this
    simpa [sub_eq_add_neg] using this

end GlobalTheory.PeriodFamily
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolAdjointRing

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
   intro P E _ _ _ H Dw l Xo S _ x A _ π hπ a ha ψ hψ z u v
   have hG := ObjDim.isAbelianScheme Xo.univ
   have hA : IsAbelianScheme A := by
     have := hG.comm
     have hc : IsCommMonObj A := by
       rw [isCommMonObj_iff_isMulCommutative]
       intro T
       refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
       rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
         ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
     exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
       MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
       MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
   have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
     (ObjDim.smoothOfRelativeDimension Xo.univ)
   have := hA.comm
   have := a.hom
   exact GlobalTheory.PolAdjoint.adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z)
     (a.act (H.bar z)) (GlobalTheory.PolAdjoint.lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v
end GlobalTheory.PolAdjointRing
end
end
