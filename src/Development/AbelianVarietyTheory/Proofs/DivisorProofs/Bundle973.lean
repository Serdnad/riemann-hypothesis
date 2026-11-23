module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle945
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeMulVecLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle948
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S : Sys I π s₀, RhoBC hI hk s₀ → S.Full hI → ∀ c : Cr hI π s₀, c ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) ↔ rho hI hk s₀ c ∈ F1 s₀ := by
  first | exact @GlobalTheory.LiftSys.Sys.mem_K_sup_iff | exact GlobalTheory.LiftSys.Sys.mem_K_sup_iff | (intros; apply GlobalTheory.LiftSys.Sys.mem_K_sup_iff <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.Div

theorem coh_subsingleton_of_cls_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB),
    cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) →
      Subsingleton (coh (LB.toMod N) q) := by
  intro X M N hM hN e q h
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X) hM hN e
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((Twist.unitTwistIso M).symm ≪≫ i ≪≫ Twist.unitTwistIso N)).toEquiv.subsingleton_congr.1 h

end GlobalTheory.Div
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open ProjSpace

theorem IsAmpleLB.exists_affine_boundary_functions {Y : Scheme.{0}} {L : LB Y} (h : IsAmpleLB L) (U : Y.Opens)
    (x : Y) (hx : x ∈ U) : ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
      ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
        resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  obtain ⟨k, hk, hg⟩ := h.exists_isGenerated_pow
  obtain ⟨d, -, t, hxt, hle, ha⟩ := ((isAmpleLB_pow_iff h.isLB hk).2 h).exists_affine_le hx
  obtain ⟨n, s, hs⟩ := hg.pow d
  refine ⟨nonzeroLocus t, n, fun l => secRatio t (s l), hxt, hle, ha, fun z => ?_⟩
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ z))
  refine ⟨nonzeroLocus (s l), secRatio (s l) t, l, hl, basicOpen_secRatio _ _, ?_⟩
  rw [secRatio_mul_secRatio t (s l) t inf_le_right inf_le_left, secRatio_self, map_one]

theorem exists_affine_boundary_functions_of_isProjOver :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (U : Y.Opens) (x : Y), x ∈ U →
      ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
        ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
          resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  rintro Y p ⟨N, i, hi, -⟩ U x hx
  exact ((isAmple_projective_O_one ℂ N).pull_of_isAffineHom i).exists_affine_boundary_functions U x hx

end GlobalTheory
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.product_representation_reorder_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e e' : (Σ a, Fin (d a)) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd e' π)) := by
  first | exact @GlobalTheory.PlacingProd.multiProd_placing_equiv | exact GlobalTheory.PlacingProd.multiProd_placing_equiv | (intros; apply GlobalTheory.PlacingProd.multiProd_placing_equiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheafDescent

theorem descendedIdealSheaf_exists : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  intro Y Z π _ hY _ _ hnZ hW hchar I
  have hK := GlobalTheory.T.isField_stalk_imageOfGenericPoint Y Z π hW
  have hfd := GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint Y Z π hK
  letI := GlobalTheory.NormSheafDescent.fieldK π hK
  letI := GlobalTheory.NormSheafDescent.algKL π
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  obtain ⟨J, hJ, hJs⟩ := GlobalTheory.T.exists_idealSheafData_of_isClopen_family Z (Set.range π) ⟨hcl, hW⟩ (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I)
    (fun U f hU => GlobalTheory.T.normCoeffIdealFamily_map_basicOpen Y Z π hK hfd I U f hU)
  have hgen : ∀ (U : Z.Opens) (x : Z), x ∈ U → x ∈ Set.range π →
      GlobalTheory.NormSheafDescent.genPt π ∈ U := by
    rintro U _ hx ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map π.continuous).mem_open U.isOpen hx
  refine ⟨Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π), Y.functionField, inferInstance, inferInstance,
    inferInstance, hfd, GlobalTheory.T.charZero_stalk_imageOfGenericPoint Y Z π hchar hK, J, ?_, ?_⟩
  · intro x hx
    by_contra hne
    push_neg at hne
    have hxW := hJs hx
    have hS : IsClosed (π '' (I.support : Set Y)) := π.isClosedMap _ I.support.isClosed
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (π '' (I.support : Set Y))ᶜ ∩ Set.range π from ⟨fun ⟨y, hy, e⟩ => hne y hy e, hxW⟩)
      (hS.isOpen_compl.inter hW)
    have htop := GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint Y Z π hK hfd I ⟨U, hU⟩ (fun y hy hyU => (hUsub hyU).1 ⟨y, hy, rfl⟩)
    have hx' := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    rw [hJ ⟨U, hU⟩ (fun z hz => (hUsub hz).2), htop] at hx'
    exact (Scheme.mem_zeroLocus_iff _ _ _).mp hx' 1 Submodule.mem_top (by simpa using hxU)
  · rintro U hUW ⟨x, hxU⟩
    have h := hgen U.1 x hxU (hUW hxU)
    obtain ⟨hdom, hfr⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hUW h
    letI := GlobalTheory.NormSheafDescent.algAK π U.1 h
    letI := GlobalTheory.NormSheafDescent.algBL π U.1 h
    haveI : Nonempty (π ⁻¹ᵁ U.1) := ⟨⟨genericPoint Y, h⟩⟩
    refine ⟨inferInstance, inferInstance, hdom, GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2,
      inferInstance, ?_, hfr, ?_, ?_, ?_⟩
    · exact π.finite_app U.1 U.2
    · exact functionField_isFractionRing_of_isAffineOpen Y _ (U.2.preimage π)
    · ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) h a
    · rw [hJ U hUW]
      simp only [GlobalTheory.NormSheafDescent.famIdeal, dif_pos h]

end GlobalTheory.NormSheafDescent
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleExcision_vanishing_under_refinement : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  first | (exact @GlobalTheory.EtC.mvRefine_main) | (exact GlobalTheory.EtC.mvRefine_main) | (intros; apply GlobalTheory.EtC.mvRefine_main <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.kummer_divisor_step) | (exact GlobalTheory.EtC.kummer_divisor_step) | (intros; apply GlobalTheory.EtC.kummer_divisor_step <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.div_const_origin : GlobalTheory.VertUnits.DivConstOrigin := by
  first | (exact @GlobalTheory.VertUnits.divConstOrigin) | (exact GlobalTheory.VertUnits.divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstOrigin <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restrict : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  first
  | exact @GlobalTheory.EtC.RedChern.res_defectSec
  | exact GlobalTheory.EtC.RedChern.res_defectSec
  | (intros; apply GlobalTheory.EtC.RedChern.res_defectSec <;> assumption)
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFg
open GlobalTheory.EtC

def invPSh (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Scheme.Γ.obj U))
  map f := TypeCat.ofHom fun h => ⟨(map_natCast (Scheme.Γ.map f).hom q) ▸ h.down.map (Scheme.Γ.map f).hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev lineSp (q : ℕ) : Spc := ptimes (invPSh q) (ofCat (glCat 1))

abbrev lineSp.line (q : ℕ) : lineSp q ⟶ ofCat (glCat 1) := ptimes.snd _ _

theorem inv_lineSp (q : ℕ) : Inv q (lineSp q) := fun _ ⟨y⟩ => y.1.down

theorem inv_of_map {E E' : Spc} (f : E ⟶ E') {q : ℕ} (h : Inv q E') : Inv q E := fun U ⟨x⟩ =>
  h U ⟨((f.app (op (SimplexCategory.mk 0))).app (op U)) x⟩

theorem isUnit_of_simplex {q : ℕ} {E : Spc} (hE : Inv q E) (p : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ)
    (x : (E.obj p).obj U) : IsUnit (q : Scheme.Γ.obj U) :=
  hE U.unop ⟨(E.map (SimplexCategory.const (SimplexCategory.mk 0) p.unop 0).op).app U x⟩

variable (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E)

def colInv (p : SimplexCategoryᵒᵖ) : ptimes (E.obj p) (Fib N) ⟶ disc.obj (invPSh q) where
  app n := { app := fun U => TypeCat.ofHom (fun y => ⟨isUnit_of_simplex hE p U y.1⟩), naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def colLine (p : SimplexCategoryᵒᵖ) : ptimes (E.obj p) (Fib N) ⟶ lineSp q :=
  (ptimesIsLimit _ _).lift (BinaryFan.mk (colInv q hE p) (ptimes.snd _ _ ≫ Fib.line N))

theorem colLine_line (p : SimplexCategoryᵒᵖ) : colLine q hE p ≫ lineSp.line q = ptimes.snd (E.obj p) (Fib N) ≫ Fib.line N :=
  (ptimesIsLimit _ _).fac _ ⟨WalkingPair.right⟩

def ellB : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (lineSp q) where
  app p := colLine q hE p
  naturality _ _ _ := rfl

theorem pull_cast {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E₂ n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f (tw q i) n x : Ht q E₁ n i) := by
  subst hn hi; rfl

theorem pull_cpow [NeZero q] {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) (h : Inv q E₂) (x : Ht q E₂ 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (a6nat_holds q).2.1 f h]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (a6nat_holds q).1, ih]

theorem mk_zcomp_ofHom {R : Type} [CommRing R] {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) {F : Shv R} {n : ℤ}
    (z : Cocycle ((chains R).obj E₂) (res R F) n) :
    CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _)) = pull R f F n (CohomologyClass.mk z) :=
  rfl

theorem diag_line : (bidiag.map (ellB q V hE) ≫ (bidiagConst (lineSp q)).hom) ≫ lineSp.line q =
    bidiag.map (twLine E V) ≫ (bidiagConst _).hom := rfl

theorem pbf_of_disc : ∀ (q : ℕ) [NeZero q] (N : ℕ),
    (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) →
      ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  intro q _ N hD E V hE
  have hB := inv_lineSp q
  have hP : Inv q (pullback V (PGL.pr N)) := inv_of_map (pullback.fst V (PGL.pr N)) hE
  choose z hz using fun j : Fin N => CohomologyClass.mk_surjective (cpow q (c1 q (lineSp.line q)) (j : ℕ))
  refine GlobalTheory.PBFc.pbf_of_model q V (ellB q V hE) hE z (fun j => ?_) (fun a j => ?_) hD
  · rw [mk_zcomp_ofHom, hz, pull_cpow q _ hB, (a6nat_holds q).2.2.1 _ _ hB, pull_cpow q _ hP,
      (a6nat_holds q).2.2.1 _ _ hP, twIso_line, diag_line]
  · rw [mk_zcomp_ofHom, hz, pull_cpow q _ hB, (a6nat_holds q).2.2.1 _ _ hB]
    exact congrArg (fun L => cpow q (c1 q L) (j : ℕ)) (colLine_line q hE _)

end GlobalTheory.PBFg
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

theorem _root_.GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  first
  | exact @GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | exact GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

theorem _root_.GlobalTheory.T.kummerSplittingDefect_glue_qthRoots : ∀ (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v') → ∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v := by
  first
  | exact @GlobalTheory.EtC.KumPic.DvGlue.glue
  | exact GlobalTheory.EtC.KumPic.DvGlue.glue
  | (intros; apply GlobalTheory.EtC.KumPic.DvGlue.glue <;> assumption)
end
