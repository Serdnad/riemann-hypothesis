module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Bundle001
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle004
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
public import GroundTheory.ArithmeticGeometry.EtaleCompletion.QcohZariski
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import GroundTheory.ArithmeticGeometry.EtaleCompletion.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

section Spec

variable {R : CommRingCat.{u}} {M N : (Spec (.of R)).Modules} (ψ : M ⟶ N)

def cokernelTildeIso (hM : IsIso M.fromTildeΓ) (hN : IsIso N.fromTildeΓ) :
    (tilde.functor R).obj (cokernel (moduleSpecΓFunctor.map ψ)) ≅ cokernel ψ :=
  let p : (moduleSpecΓFunctor ⋙ tilde.functor R).obj M ≅ M := @asIso _ _ _ _ M.fromTildeΓ hM
  let q : (moduleSpecΓFunctor ⋙ tilde.functor R).obj N ≅ N := @asIso _ _ _ _ N.fromTildeΓ hN
  PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map ψ) ≪≫
    cokernel.mapIso ((moduleSpecΓFunctor ⋙ tilde.functor R).map ψ) ψ p q
      (Scheme.Modules.fromTildeΓNatTrans.naturality ψ)

lemma cokernelTildeIso_comm (hM : IsIso M.fromTildeΓ) (hN : IsIso N.fromTildeΓ) :
    (tilde.functor R).map (cokernel.π (moduleSpecΓFunctor.map ψ)) ≫
      (cokernelTildeIso ψ hM hN).hom = N.fromTildeΓ ≫ cokernel.π ψ := by
  have h : (tilde.functor R).map (cokernel.π (moduleSpecΓFunctor.map ψ)) ≫
      (PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map ψ)).hom =
      cokernel.π ((tilde.functor R).map (moduleSpecΓFunctor.map ψ)) := by
    rw [← π_comp_cokernelComparison, ← PreservesCokernel.iso_inv, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [cokernelTildeIso, Iso.trans_hom, ← Category.assoc, h]
  simp [cokernel.mapIso]
  try rfl

lemma isQuasicoherent_cokernel_spec [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel ψ).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (.of R)).ringCatSheaf).prop_of_iso
    (cokernelTildeIso ψ inferInstance inferInstance)
    (inferInstanceAs ((tilde.functor R).obj _).IsQuasicoherent)

lemma surjective_cokernel_π_app_top [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective ((cokernel.π ψ).app ⊤) := by
  have hM : IsIso M.fromTildeΓ := inferInstance
  have hN : IsIso N.fromTildeΓ := inferInstance
  set Q := cokernel (moduleSpecΓFunctor.map ψ)
  set q := cokernel.π (moduleSpecΓFunctor.map ψ)
  have hq : Function.Surjective q := (ModuleCat.epi_iff_surjective q).1 inferInstance
  have h1 : Function.Surjective (((tilde.functor R).map q).app ⊤) := by
    have e := tilde.toOpen_map_app q ⊤
    intro y
    obtain ⟨y', rfl⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen Q ⊤)).2 y
    obtain ⟨z, rfl⟩ := hq y'
    refine ⟨tilde.toOpen _ ⊤ z, ?_⟩
    have := congrArg (fun g => g.hom z) e
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  have h2 : ∀ x, (cokernelTildeIso ψ hM hN).hom.app ⊤ (((tilde.functor R).map q).app ⊤ x) =
      (cokernel.π ψ).app ⊤ (N.fromTildeΓ.app ⊤ x) := fun x => by
    have := congrArg (fun g => (g.app ⊤) x) (cokernelTildeIso_comm ψ hM hN)
    exact this
  intro y
  obtain ⟨x, hx⟩ := ((ConcreteCategory.bijective_of_isIso
    ((cokernelTildeIso ψ hM hN).hom.app ⊤)).2.comp h1) y
  exact ⟨N.fromTildeΓ.app ⊤ x, (h2 x).symm.trans hx⟩

end Spec

section Scheme

variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G)

lemma bijective_app_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Function.Bijective (e.hom.app U) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app U, fun x => ?_, fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl

lemma isQuasicoherent_restrict_cokernel [F.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) : ((cokernel φ).restrict hU.fromSpec).IsQuasicoherent := by
  let Rf := Scheme.Modules.restrictFunctor hU.fromSpec
  have : (Rf.obj F).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have : (Rf.obj G).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have h := isQuasicoherent_cokernel_spec (R := Γ(X, U)) (Rf.map φ)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso Rf φ).symm h

instance isQuasicoherent_cokernel [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (cokernel φ).IsQuasicoherent :=
  isQuasicoherent_of_restrict (cokernel φ) (fun U : X.affineOpens => (U : X.Opens))
    (iSup_affineOpens_eq_top X)
    fun U => nonempty_presentation_restrict _ U.2 (isQuasicoherent_restrict_cokernel φ U.2)

lemma surjective_cokernel_π_app [F.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Surjective ((cokernel.π φ).app U) := by
  let Rf := Scheme.Modules.restrictFunctor hU.fromSpec
  have : (Rf.obj F).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have : (Rf.obj G).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have h1 := surjective_cokernel_π_app_top (R := Γ(X, U)) (Rf.map φ)
  have h2 : Rf.map (cokernel.π φ) = cokernel.π (Rf.map φ) ≫ (PreservesCokernel.iso Rf φ).inv := by
    rw [PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  have h3 : Function.Surjective ((Rf.map (cokernel.π φ)).app ⊤) := by
    rw [h2]
    exact (bijective_app_of_iso (PreservesCokernel.iso Rf φ).symm ⊤).2.comp h1
  rw [← fromSpec_image_top hU]
  exact h3

theorem isCoherent_cokernel [F.IsQuasicoherent] (hG : IsCoherent G) :
    IsCoherent (cokernel φ) := by
  have := hG.1
  refine ⟨inferInstance, fun U hU => ?_⟩
  have := hG.2 U hU
  let π' : Γ(G, U) →ₗ[Γ(X, U)] Γ(cokernel φ, U) :=
    { toFun := (cokernel.π φ).app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_surjective π' (surjective_cokernel_π_app φ hU)

end Scheme

section Sequences

variable {C : Type*} [Category C] [Abelian C] {P Q : C} (α : P ⟶ Q)

def kerCoimSC : ShortComplex C :=
  ShortComplex.mk (kernel.ι α) (Abelian.coimage.π α) (cokernel.condition _)

lemma kerCoimSC_shortExact : (kerCoimSC α).ShortExact :=
  ShortComplex.ShortExact.mk' ((kerCoimSC α).exact_of_g_is_cokernel
    (cokernelIsCokernel (kernel.ι α))) (inferInstanceAs (Mono (kernel.ι α)))
    (inferInstanceAs (Epi (Abelian.coimage.π α)))

def coimCokSC : ShortComplex C :=
  ShortComplex.mk (Abelian.factorThruCoimage α) (cokernel.π α) (by
    rw [← cancel_epi (Abelian.coimage.π α), ← Category.assoc, Abelian.coimage.fac, comp_zero,
      cokernel.condition])

def coimCokIsColimit :
    IsColimit (CokernelCofork.ofπ (f := Abelian.factorThruCoimage α) (cokernel.π α)
      (coimCokSC α).zero) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun b hb => cokernel.desc α b (by
      rw [← Abelian.coimage.fac α, Category.assoc, hb, comp_zero]))
    (fun b hb => cokernel.π_desc _ _ _)
    (fun b hb m hm => by
      exact (cancel_epi (cokernel.π α)).1 (by rw [hm, cokernel.π_desc]))

lemma coimCokSC_shortExact : (coimCokSC α).ShortExact :=
  ShortComplex.ShortExact.mk' ((coimCokSC α).exact_of_g_is_cokernel (coimCokIsColimit α))
    (inferInstanceAs (Mono (Abelian.factorThruCoimage α))) (inferInstanceAs (Epi (cokernel.π α)))

end Sequences

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MvPolynomial
open GroundTheory.Arith.Etale (pullbackUnitApp)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}


variable (A) in
abbrev cmap :
    C(ProjectiveSpectrum.top (grading B n), ProjectiveSpectrum.top (grading A n)) :=
  ProjectiveSpectrum.comap (gradedMap A B n) (irrelevant_le_map A B n)


variable (A) in
abbrev pt (y : ProjectiveSpectrum (grading B n)) : ProjectiveSpectrum (grading A n) :=
  ProjectiveSpectrum.comapFun (gradedMap A B n) (irrelevant_le_map A B n) y

def locMap (y : ProjectiveSpectrum (grading B n)) :
    ProjTwist.Loc (grading A n) (pt A y) →+* ProjTwist.Loc (grading B n) y :=
  Localization.localRingHom _ _
    (gradedMap A B n : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin (n + 1)) B) rfl

lemma locMap_mk (y : ProjectiveSpectrum (grading B n)) (r : MvPolynomial (Fin (n + 1)) A)
    (s : (pt A y).asHomogeneousIdeal.toIdeal.primeCompl) :
    locMap y (Localization.mk r s) =
      Localization.mk (gradedMap A B n r)
        (⟨gradedMap A B n s, s.2⟩ : y.asHomogeneousIdeal.toIdeal.primeCompl) :=
  Localization.localRingHom_mk _ _ _ _ _ _

variable (k : ℤ)

def twistPushSec {V : (projectiveSpace A n).Opens} (s : Γ(twistingSheaf (grading A n) k, V)) :
    Γ(twistingSheaf (grading B n) k, baseChangeMap A B n ⁻¹ᵁ V) :=
  ProjTwist.mkSection (fun y => locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩))
    (by
      intro y
      obtain ⟨W, hyW, iW, i, j, hij, r, t, hr, ht, htn, w⟩ :=
        ProjTwist.isLocallyFraction_val s ⟨pt A y.1, y.2⟩
      refine ⟨W.comap (cmap (B := B) A), hyW, homOfLE (fun z hz => (leOfHom iW) hz), i, j, hij,
        gradedMap A B n r, gradedMap A B n t, (gradedMap A B n).2 hr, (gradedMap A B n).2 ht,
        fun z => htn ⟨pt A z.1, z.2⟩, fun z => ?_⟩
      have e := w ⟨pt A z.1, z.2⟩
      change locMap z.1 (ProjTwist.val s ⟨pt A z.1, _⟩) = _
      change ProjTwist.val s ⟨pt A z.1, _⟩ = _ at e
      rw [e]
      exact locMap_mk _ _ _)

lemma val_app_apply {V : (projectiveSpace A n).Opens} (t : Γ(projectiveSpace A n, V))
    (y : baseChangeMap A B n ⁻¹ᵁ V) :
    ((((baseChangeMap A B n).app V t) : Γ(Proj (grading B n), _)).1 y).val =
      locMap y.1 ((t.1 ⟨pt A y.1, y.2⟩).val) := by
  have : y.1.asHomogeneousIdeal.toIdeal.IsPrime :=
    ProjectiveSpectrum.isPrime (y.1 : ProjectiveSpectrum (grading B n))
  show HomogeneousLocalization.val (HomogeneousLocalization.localRingHom (gradedMap A B n)
    (pt A y.1).asHomogeneousIdeal.toIdeal y.1.asHomogeneousIdeal.toIdeal rfl (t.1 ⟨pt A y.1, y.2⟩)) = _
  exact HomogeneousLocalization.val_localRingHom _

lemma twistPushSec_smul {V : (projectiveSpace A n).Opens} (t : Γ(projectiveSpace A n, V))
    (s : Γ(twistingSheaf (grading A n) k, V)) :
    twistPushSec (B := B) k (t • s) = (baseChangeMap A B n).app V t • twistPushSec (B := B) k s := by
  apply Subtype.ext
  funext y
  show locMap y.1 ((t.1 ⟨pt A y.1, y.2⟩).val * ProjTwist.val s ⟨pt A y.1, y.2⟩) =
    (((baseChangeMap A B n).app V t).1 y).val * locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩)
  exact (map_mul (locMap y.1) _ _).trans (congrArg (· * _) (val_app_apply t y).symm)

lemma twistPushSec_add {V : (projectiveSpace A n).Opens}
    (s s' : Γ(twistingSheaf (grading A n) k, V)) :
    twistPushSec (B := B) k (s + s') = twistPushSec k s + twistPushSec k s' := by
  apply Subtype.ext
  funext y
  show locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩ + ProjTwist.val s' ⟨pt A y.1, y.2⟩) =
    locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩) + locMap y.1 (ProjTwist.val s' ⟨pt A y.1, y.2⟩)
  exact map_add _ _ _

def twistToPushforward :
    twistingSheaf (grading A n) k ⟶
      (Scheme.Modules.pushforward (baseChangeMap A B n)).obj (twistingSheaf (grading B n) k) :=
  ⟨{ app V := ModuleCat.ofHom (X := (twistingSheaf (grading A n) k).val.obj V)
      (Y := ((Scheme.Modules.pushforward (baseChangeMap A B n)).obj
        (twistingSheaf (grading B n) k)).val.obj V)
      { toFun := fun s => twistPushSec k (V := V.unop) s
        map_add' := fun s s' => twistPushSec_add k s s'
        map_smul' := fun t s => twistPushSec_smul k t s }
     naturality := fun {V V'} i => by
      ext s
      exact Subtype.ext (funext fun y => rfl) }⟩

def pullbackTwistingSheafMap :
    (Scheme.Modules.pullback (baseChangeMap A B n)).obj (twistingSheaf (grading A n) k) ⟶
      twistingSheaf (grading B n) k :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap A B n)).homEquiv _ _).symm
    (twistToPushforward k)

lemma pullbackTwistingSheafMap_unit {V : (projectiveSpace A n).Opens}
    (s : Γ(twistingSheaf (grading A n) k, V)) :
    (pullbackTwistingSheafMap (B := B) k).app _ (pullbackUnitApp (baseChangeMap A B n) _ V s) =
      twistPushSec k s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap A B n)).homEquiv_unit
    (twistingSheaf (grading A n) k) (twistingSheaf (grading B n) k)
    (pullbackTwistingSheafMap k))
  rw [pullbackTwistingSheafMap, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun g => (Scheme.Modules.Hom.app g V) s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h2
  exact h2.symm

lemma twistPushSec_upow {u : MvPolynomial (Fin (n + 1)) A} (hu : u ∈ grading A n 1) :
    twistPushSec (B := B) k (ProjTwist.upow (grading A n) hu k) =
      ProjTwist.upow (grading B n) ((gradedMap A B n).2 hu) k := by
  apply Subtype.ext
  funext y
  change locMap y.1 (ProjTwist.val (ProjTwist.upow (grading A n) hu k) ⟨pt A y.1, y.2⟩) =
    ProjTwist.val (ProjTwist.upow (grading B n) ((gradedMap A B n).2 hu) k) ⟨y.1, y.2⟩
  erw [ProjTwist.val_upow, ProjTwist.val_upow]
  unfold ProjTwist.twistFrac
  refine (locMap_mk _ _ _).trans ?_
  congr 1
  · exact map_pow (gradedMap A B n) u _
  · exact Subtype.ext (map_pow (gradedMap A B n) u _)

instance isIso_pullbackTwistingSheafMap :
    IsIso (pullbackTwistingSheafMap (A := A) (B := B) (n := n) k) := by
  apply isIso_of_isBasisOn
  intro y
  obtain ⟨j, hj⟩ := exists_mem_stdOpen_proj ((baseChangeMap A B n).base y)
  refine ⟨baseChangeMap A B n ⁻¹ᵁ stdOpen A n j, hj,
    pullbackUnitApp (baseChangeMap A B n) _ (stdOpen A n j)
      (ProjTwist.upow (grading A n) (X_mem j) k),
    isBasisOn_pullbackUnitApp _ (ProjTwist.isBasisOn_upow _ (X_mem j) k), ?_⟩
  have key : ((preMod _).map (pullbackTwistingSheafMap (B := B) k)).app _
      (pullbackUnitApp (baseChangeMap A B n) _ (stdOpen A n j)
        (ProjTwist.upow (grading A n) (X_mem j) k)) =
      ProjTwist.upow (grading B n) ((gradedMap A B n).2 (X_mem j)) k :=
    (pullbackTwistingSheafMap_unit k _).trans (twistPushSec_upow k _)
  rw [key]
  exact ProjTwist.isBasisOn_upow _ _ k


variable (A B n) in
def pullbackTwistingSheafIso :
    (Scheme.Modules.pullback (baseChangeMap A B n)).obj (twistingSheaf (grading A n) k) ≅
      twistingSheaf (grading B n) k :=
  asIso (pullbackTwistingSheafMap k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

def Scheme.Modules.SupportedIn (F : X.Modules) (T : Set X) : Prop :=
  ∀ U : X.Opens, Disjoint (U : Set X) T → ∀ s : Γ(F, U), s = 0

namespace Scheme.Modules.SupportedIn

lemma mono {F : X.Modules} {T T' : Set X} (h : Scheme.Modules.SupportedIn F T) (hT : T ⊆ T') :
    Scheme.Modules.SupportedIn F T' :=
  fun U hU s => h U (hU.mono_right hT) s

lemma of_iso {F G : X.Modules} (e : F ≅ G) {T : Set X} (h : Scheme.Modules.SupportedIn F T) :
    Scheme.Modules.SupportedIn G T := by
  intro U hU s
  have h1 : e.inv.app U s = 0 := h U hU _
  have h2 : e.hom.app U (e.inv.app U s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [← h2, h1, map_zero]

lemma pushforward {Z : Scheme.{u}} (j : Z ⟶ X) {G : Z.Modules} {T' : Set Z}
    (h : Scheme.Modules.SupportedIn G T') :
    Scheme.Modules.SupportedIn ((Scheme.Modules.pushforward j).obj G) (j.base '' T') := by
  intro U hU s
  refine h (j ⁻¹ᵁ U) ?_ s
  rw [Set.disjoint_left]
  intro z hz hzT
  exact Set.disjoint_left.1 hU hz ⟨z, hzT, rfl⟩

end Scheme.Modules.SupportedIn

lemma isIso_of_bijective_app {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ U : X.Opens, Function.Bijective (φ.app U)) : IsIso φ := by
  have : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
    have : ∀ U : (X.Opens)ᵒᵖ, IsIso (((Scheme.Modules.toPresheaf X).map φ).app U) := fun U =>
      (ConcreteCategory.isIso_iff_bijective _).2 (h U.unop)
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)

lemma eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) (U : X.Opens) (s : Γ(F, U)) : s = 0 := by
  have : (𝟙 F : F ⟶ F).app U s = (0 : F ⟶ F).app U s := by rw [hF.eq_of_src (𝟙 F) 0]
  simpa using this

section Restrict

variable {F G : X.Modules} (φ : F ⟶ G) (W : X.Opens)

lemma kernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (kernel φ) (W : Set X)ᶜ := by
  intro U hU s
  have hUW : U ≤ W := fun x hx => by
    by_contra hxW
    exact Set.disjoint_left.1 hU hx hxW
  apply kernel_ι_app_injective φ U
  apply (h U hUW).1
  rw [map_zero, map_zero, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    kernel.condition]
  rfl

lemma cokernel_supportedIn (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (φ.app U)) :
    Scheme.Modules.SupportedIn (cokernel φ) (W : Set X)ᶜ := by
  intro U hU s
  have hUW : U ≤ W := fun x hx => by
    by_contra hxW
    exact Set.disjoint_left.1 hU hx hxW
  let R := Scheme.Modules.restrictFunctor W.ι
  have hφ : IsIso (R.map φ) := isIso_of_bijective_app _ fun V =>
    h _ ((W.ι.image_le_opensRange V).trans (by simp))
  have hZ : IsZero (R.obj (cokernel φ)) :=
    (isZero_cokernel_of_epi (R.map φ)).of_iso (PreservesCokernel.iso R φ)
  have hE : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hUW
  have h0 : (cokernel φ).presheaf.map (eqToHom hE).op s = 0 :=
    eq_zero_of_isZero hZ (W.ι ⁻¹ᵁ U) _
  have hinv : (cokernel φ).presheaf.map (eqToHom hE.symm).op
      ((cokernel φ).presheaf.map (eqToHom hE).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hinv, h0, map_zero]

end Restrict

end

end GroundTheory.Arith.SchemeCoh
end
