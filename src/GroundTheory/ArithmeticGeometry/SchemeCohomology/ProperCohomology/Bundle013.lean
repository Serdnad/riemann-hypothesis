module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdeal
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle012
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}
  (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

lemma embed_snd {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embed i ψ h hV ≫ pullback.snd _ _ = ψ ∣_ V ≫ hV.isoSpec.hom := by
  letI := baseAlgebra A hV
  rw [← cancel_mono hV.fromSpec, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι]
  have hc : pullback.snd (graph i ψ h) (overV (N := N) A hV) ≫ overV A hV =
      pullback.fst _ _ ≫ graph i ψ h := pullback.condition.symm
  have hp := pasteIso_hom_snd (N := N) A hV
  have hq : pullback.snd (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)))
      hV.fromSpec ≫ hV.fromSpec = overV A hV ≫ pullback.snd _ _ := pullback.condition.symm
  simp only [embed, Category.assoc]
  rw [reassoc_of% hp, hq, reassoc_of% hc, pullback.lift_snd, ← Category.assoc, restrictIso_hom_fst]

lemma app_eqToHom_apply {X X' : Scheme.{u}} (ψ : X' ⟶ X) {U U' : X.Opens} (hU : U' = U)
    {W W' : X'.Opens} (h1 : W = ψ ⁻¹ᵁ U') (h2 : W' = W) (b : Γ(X, U)) :
    X'.presheaf.map (eqToHom h2).op (X'.presheaf.map (eqToHom h1).op
      (ψ.app U' (X.presheaf.map (eqToHom hU).op b))) =
      X'.presheaf.map (eqToHom (h2.trans (h1.trans (by rw [hU])))).op (ψ.app U b) := by
  subst hU
  subst h1
  subst h2
  simp

attribute [local instance] algebraOfOver

lemma algebraMap_overBase {V : X.Opens} (hV : IsAffineOpen V) (b : Γ(X, V)) :
    letI := overBase i ψ h hV
    X'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((ψ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(X', (ψ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      ψ.app V b := by
  letI := overBase i ψ h hV
  have s1 : algebraMap Γ(X, V) Γ((ψ ⁻¹ᵁ V).toScheme, ⊤) b = (ψ ∣_ V).appTop (V.topIso.inv b) := by
    change (embed i ψ h hV ≫ pullback.snd _ _).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [embed_snd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (app_eqToHom_apply ψ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp


omit [X.Over (Spec (.of A))] in
lemma smul_restrict_top (M : X'.Modules) (U : X'.Opens) (a : Γ(U.toScheme, ⊤))
    (y : Γ(M.restrict U.ι, ⊤)) :
    M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
      ((modulesAbMap (smulHom (M.restrict U.ι) a)).hom.app (op ⊤) y) =
      X'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
        (a : Γ(X', U.ι ''ᵁ ⊤)) •
        M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
          (y : Γ(M, U.ι ''ᵁ ⊤)) := by
  have e1 : (modulesAbMap (smulHom (M.restrict U.ι) a)).hom.app (op ⊤) y =
      restrictTop (X := U.toScheme) ⊤ a • y := rfl
  have e2 : restrictTop (X := U.toScheme) ⊤ a = a := by
    simp [restrictTop]; rfl
  have e3 : (a • y : Γ(M.restrict U.ι, ⊤)) =
      ((U.ι.appIso ⊤).inv a • (@id Γ(M, U.ι ''ᵁ ⊤) y) : Γ(M, U.ι ''ᵁ ⊤)) := rfl
  rw [e1, e2, e3, Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact Scheme.Modules.map_smul M (eqToHom (Scheme.Opens.ι_image_top U).symm) a y

def H0ToSections {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    letI := overBase i ψ h hV
    Sheaf.H.{u} (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward ψ).obj M, V) :=
  letI := overBase i ψ h hV
  { toFun := fun x => M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op
      (Sheaf.H.equiv₀ (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) isTerminalTop x :
        Γ(M, (ψ ⁻¹ᵁ V).ι ''ᵁ ⊤))
    map_add' := fun x y => by
      rw [map_add (f := _)]
      exact map_add _ _ _
    map_smul' := fun b x => by
      rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
      refine (smul_restrict_top M (ψ ⁻¹ᵁ V) _ _).trans ?_
      refine (congrArg (· • _) (algebraMap_overBase i ψ h hV b)).trans ?_
      exact (smul_pushforward ψ M b _).symm }

lemma H0ToSections_bijective {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    Function.Bijective (H0ToSections i ψ h hV M) := by
  letI := overBase i ψ h hV
  exact (ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op)).comp
    (Sheaf.H.equiv₀ (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) isTerminalTop).bijective

theorem finite_sections_pushforward {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    letI := overBase i ψ h hV
    Module.Finite Γ(X, V) (Sheaf.H.{u} (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) 0) →
      Module.Finite Γ(X, V) Γ((Scheme.Modules.pushforward ψ).obj M, V) := by
  letI := overBase i ψ h hV
  intro hfin
  exact Module.Finite.of_surjective (H0ToSections i ψ h hV M) (H0ToSections_bijective i ψ h hV M).2

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {F : X.Modules} {V V' : X.Opens} (hle : V' ≤ V)

lemma algV_res (a : A) : resO hle (algV X V a) = algV X V' a := by
  have := Scheme.Hom.appLE_map (X ↘ Spec (.of A)) (U := ⊤) (le_top : V ≤ _) (homOfLE hle).op
  exact congrArg (fun f : Γ(Spec (.of A), ⊤) ⟶ Γ(X, V') => f.hom ((Scheme.ΓSpecIso (.of A)).inv a))
    this


variable (I) in
abbrev resS : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) →+* Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') :=
  resO (Scheme.Hom.preimage_mono _ hle)

lemma resS_reesInr (r : reesAlgebra I) : resS I hle (reesInr I V r) = reesInr I V' r := by
  have := Scheme.Hom.appLE_map (reesSnd I X) (U := ⊤) (le_top : reesPr I X ⁻¹ᵁ V ≤ _)
    (homOfLE (Scheme.Hom.preimage_mono _ hle)).op
  exact congrArg (fun f : Γ(Spec (.of (reesAlgebra I)), ⊤) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') =>
    f.hom ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv r)) this

lemma resS_prApp (c : Γ(X, V)) :
    resS I hle ((reesPr I X).app V c) = (reesPr I X).app V' (resO hle c) := by
  have := (reesPr I X).naturality (homOfLE hle).op
  exact (congrArg (fun f : Γ(X, V) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') => f.hom c) this).symm

lemma reesRingHom_res (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) :
    reesRingHom hV' (resS I hle s) = (reesRingHom hV s).map (resO hle) := by
  have h := (isPushout_rees (I := I) hV).hom_ext
    (k := CommRingCat.ofHom ((reesRingHom hV').comp (resS I hle)))
    (l := CommRingCat.ofHom ((Polynomial.mapRingHom (resO hle)).comp (reesRingHom hV)))
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      change reesRingHom hV' (resS I hle ((reesPr I X).app V c)) =
        (reesRingHom hV ((reesPr I X).app V c)).map (resO hle)
      rw [resS_prApp, reesRingHom_inl, reesRingHom_inl, Polynomial.map_C])
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
      change reesRingHom hV' (resS I hle (reesInr I V r)) =
        (reesRingHom hV (reesInr I V r)).map (resO hle)
      rw [resS_reesInr, reesRingHom_inr, reesRingHom_inr, Polynomial.map_map]
      congr 1
      exact RingHom.ext fun a => (algV_res hle a).symm)
  exact congrArg (fun f : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶
    CommRingCat.of (Polynomial Γ(X, V')) => f.hom s) h


variable (F) in
def resFA : Γ(F, V) →ₗ[A] Γ(F, V') where
  toFun := resF F hle
  map_add' := map_add _
  map_smul' a m := by
    change resF F hle (algV X V a • m) = algV X V' a • resF F hle m
    rw [resF_smul, algV_res]

lemma resFA_apply (m : Γ(F, V)) : resFA (A := A) F hle m = resF F hle m := rfl

lemma app_resF {M N : X.Modules} (φ : M ⟶ N) {U U' : X.Opens} (h : U' ≤ U) (y : Γ(M, U)) :
    φ.app U' (resF M h y) = resF N h (φ.app U y) := by
  have := φ.mapPresheaf.naturality (homOfLE h).op
  exact congrArg (fun f => f.hom y) this

variable (hF : IsCoherent F) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')

lemma theta₁_res_coeff
    (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) (n : ℕ) :
    (theta₁ hF hV' (resF _ (Scheme.Hom.preimage_mono _ hle) y)).coeff n =
      resF F hle ((theta₁ hF hV y).coeff n) := by
  have hy : y ∈ Submodule.span Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)
      (Set.range (unitPr I F V)) := by
    rw [(isBaseChangeAt_reesPr (I := I) hF hV).span_range]
    trivial
  induction hy using Submodule.span_induction generalizing n with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have hres : resF _ (Scheme.Hom.preimage_mono _ hle) (unitPr I F V m) =
        unitPr I F V' (resF F hle m) :=
      (Etale.pullbackUnitApp_res (reesPr I X) F (homOfLE hle) m).symm
    rw [hres, theta₁_unitPr, theta₁_unitPr, PolynomialModule.coeff_single,
      PolynomialModule.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs
    · rfl
    · exact (map_zero _).symm
  | zero => simp
  | add z z' _ _ hz hz' =>
    simp only [map_add (f := _), PolynomialModule.coeff_add, Finsupp.add_apply, hz, hz']
  | smul s z _ hz =>

    rw [Scheme.Modules.map_smul, theta₁_smul, theta₁_smul, reesRingHom_res hle hV hV',
    PolynomialModule.smul_apply, PolynomialModule.smul_apply, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Polynomial.coeff_map, hz, resF_smul]

theorem reesSectionsEquiv_res (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (reesSectionsEquiv I hF hV' (resF _ (Scheme.Hom.preimage_mono _ hle) x) :
      PolynomialModule A Γ(F, V')) =
      PolynomialModule.map A (resFA F hle) (reesSectionsEquiv I hF hV x : PolynomialModule A Γ(F, V)) := by
  obtain ⟨y, rfl⟩ := surjective_reesSheafπ_app hF (hV.preimage (reesPr I X)) x
  rw [← app_resF, reesSectionsEquiv_apply, reesSectionsEquiv_apply, reesSectionsMap_π,
    reesSectionsMap_π]
  apply PolynomialModule.coeff_injective
  ext n
  exact theta₁_res_coeff hle hF hV hV' y n

end

section Base

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Scheme.{u}) [X.Over (Spec (.of A))]

variable {I X}

end Base

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules}

omit [IsNoetherianRing A] in
lemma algV_eq_toFunctions (V : X.Opens) (a : A) : algV X V a = toFunctions V a := rfl

def powSmulTopΓ (V : X.Opens) (n : ℕ) : Submodule Γ(X, V) Γ(F, V) where
  carrier := (I ^ n • ⊤ : Submodule A Γ(F, V))
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
    · change c • (a • y) ∈ (I ^ n • ⊤ : Submodule A Γ(F, V))
      rw [sectionsModuleA_smul, smul_smul, mul_comm, ← smul_smul, ← sectionsModuleA_smul]
      exact Submodule.smul_mem_smul ha trivial
    · rw [smul_add]
      exact add_mem hy hz

lemma mem_pow_smul_top_iff {V : X.Opens} (n : ℕ) (m : Γ(F, V)) :
    m ∈ (I ^ n • ⊤ : Submodule A Γ(F, V)) ↔
      m ∈ (Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) := by
  constructor
  · intro hm
    refine Submodule.smul_induction_on hm (fun a ha x _ => ?_) (fun x y hx hy => add_mem hx hy)
    rw [sectionsModuleA_smul, algV_eq_toFunctions]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) trivial
  · intro hm
    have h : I ^ n ≤ ((powSmulTopΓ (F := F) I V n).colon (Set.univ)).comap (toFunctions V) := by
      intro a ha
      rw [Ideal.mem_comap, Submodule.mem_colon]
      intro x _
      change toFunctions V a • x ∈ (I ^ n • ⊤ : Submodule A Γ(F, V))
      rw [← algV_eq_toFunctions, ← sectionsModuleA_smul]
      exact Submodule.smul_mem_smul ha trivial
    have h' := Ideal.map_le_iff_le_comap.2 h
    have : (Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) ≤
        powSmulTopΓ I V n :=
      Submodule.smul_le.2 fun c hc x _ => Submodule.mem_colon.1 (h' hc) x trivial
    exact this hm

variable [F.IsQuasicoherent]

lemma mem_range_idealPowι_iff {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) (m : Γ(F, V)) :
    m ∈ Set.range ((idealPowι I F n).app V) ↔ m ∈ (I ^ n • ⊤ : Submodule A Γ(F, V)) := by
  rw [range_idealPowι_app I F hV n, mem_pow_smul_top_iff]
  rfl

variable (hF : IsCoherent F)

section Sections

variable {V : X.Opens} (hV : IsAffineOpen V)

def reesCoef (n : ℕ) : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ Γ(F, V) where
  toFun s := (reesSectionsMap I hF hV s).coeff n
  map_zero' := by rw [reesSectionsMap_zero]; rfl
  map_add' s s' := by rw [reesSectionsMap_add]; rfl

lemma reesCoef_mem (n : ℕ) (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV n s ∈ Set.range ((idealPowι I F n).app V) :=
  (mem_range_idealPowι_iff I hV n _).2 ((mem_reesSubmodule_iff.1 (reesSectionsMap_mem hF hV s)) n)

lemma idealPowι_app_injective (n : ℕ) : Function.Injective ((idealPowι I F n).app V) :=
  kernel_ι_app_injective _ V

def reesDeg (n : ℕ) : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ Γ(idealPow I F n, V) where
  toFun s := (Equiv.ofInjective _ (idealPowι_app_injective I n)).symm
    ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩
  map_zero' := by
    apply idealPowι_app_injective I n
    refine (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n) _).trans ?_
    change reesCoef I hF hV n 0 = _
    rw [map_zero, map_zero]
  map_add' s s' := by
    apply idealPowι_app_injective I n
    refine (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n) _).trans ?_
    change reesCoef I hF hV n (s + s') = _
    rw [map_add (f := _), map_add (f := _)]
    congr 1
    · exact (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n)
        ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩).symm
    · exact (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n)
        ⟨reesCoef I hF hV n s', reesCoef_mem I hF hV n s'⟩).symm

lemma idealPowι_reesDeg (n : ℕ) (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (idealPowι I F n).app V (reesDeg I hF hV n s) = reesCoef I hF hV n s :=
  Equiv.apply_ofInjective_symm (idealPowι_app_injective I n)
    ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩

include hV in
lemma lsingle_mem_reesSubmodule (n : ℕ) (g : Γ(idealPow I F n, V)) :
    PolynomialModule.lsingle A n ((idealPowι I F n).app V g) ∈ reesSubmodule I Γ(F, V) := by
  rw [mem_reesSubmodule_iff]
  intro k
  rw [PolynomialModule.lsingle_apply]
  split_ifs with h
  · subst h
    exact (mem_range_idealPowι_iff I hV n _).1 ⟨g, rfl⟩
  · exact zero_mem _


include hF hV in
def reesInc (n : ℕ) : Γ(idealPow I F n, V) →+ Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) :=
  (reesSectionsEquiv I hF hV).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict
      ((PolynomialModule.lsingle A n).toAddMonoidHom.comp ((idealPowι I F n).app V).hom)
      (reesSubmodule I Γ(F, V)).toAddSubmonoid (lsingle_mem_reesSubmodule I hV n))

lemma reesSectionsMap_reesInc (n : ℕ) (g : Γ(idealPow I F n, V)) :
    reesSectionsMap I hF hV (reesInc I hF hV n g) =
      PolynomialModule.lsingle A n ((idealPowι I F n).app V g) := by
  rw [← reesSectionsEquiv_apply]
  change ((reesSectionsEquiv I hF hV ((reesSectionsEquiv I hF hV).symm _)) :
    PolynomialModule A Γ(F, V)) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

lemma reesCoef_reesInc (n k : ℕ) (g : Γ(idealPow I F n, V)) :
    reesCoef I hF hV k (reesInc I hF hV n g) = if n = k then (idealPowι I F n).app V g else 0 := by
  change (reesSectionsMap I hF hV (reesInc I hF hV n g)).coeff k = _
  rw [reesSectionsMap_reesInc, PolynomialModule.lsingle_apply]

lemma reesDeg_reesInc (n : ℕ) (g : Γ(idealPow I F n, V)) :
    reesDeg I hF hV n (reesInc I hF hV n g) = g := by
  apply idealPowι_app_injective I n
  rw [idealPowι_reesDeg, reesCoef_reesInc, if_pos rfl]

lemma reesDeg_reesInc_of_ne {n k : ℕ} (h : n ≠ k) (g : Γ(idealPow I F n, V)) :
    reesDeg I hF hV k (reesInc I hF hV n g) = 0 := by
  apply idealPowι_app_injective I k
  rw [idealPowι_reesDeg, reesCoef_reesInc, if_neg h, map_zero]

end Sections

end

end GroundTheory.Arith.SchemeCoh
end
