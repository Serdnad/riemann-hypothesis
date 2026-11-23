module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import GroundTheory.LocalFields.LocalFourierHaar
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle126
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

section

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of R)) [Algebra R Γ(X, ⊤)]

theorem secMap_eq_restrictGlobal
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    (W : X.Opens) (r : R) :
    (GlobalTheory.CechDR.secMap s W).hom r = GlobalTheory.restrictGlobal X W (algebraMap R Γ(X, ⊤) r) := by
  rw [← GlobalTheory.map_restrictGlobal (homOfLE (le_top : W ≤ ⊤)) (algebraMap R Γ(X, ⊤) r),
    GlobalTheory.restrictGlobal_top, hs]
  rfl

def secRes (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W ≤ U) : GlobalTheory.CechDR.Sec s U →ₗ[R] GlobalTheory.sectionsOn (GlobalTheory.structureModule X) W where
  toFun x := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (X.presheaf.map (homOfLE h).op (x : Γ(X, U)))
  map_add' x y := map_add (X.presheaf.map (homOfLE h).op).hom (x : Γ(X, U)) (y : Γ(X, U))
  map_smul' r x := by
    apply (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective
    rw [RingHom.id_apply, GlobalTheory.sectionsOn.toΓ_smul, ← secMap_eq_restrictGlobal s hs W r]
    have e : (GlobalTheory.CechDR.secMap s W).hom r =
        X.presheaf.map (homOfLE h).op ((GlobalTheory.CechDR.secMap s U).hom r) :=
      (congrArg (fun q ↦ q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (s.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)).symm
    have key : ∀ y : Γ(X, U), X.presheaf.map (homOfLE h).op ((GlobalTheory.CechDR.secMap s U).hom r * y) =
        (GlobalTheory.CechDR.secMap s W).hom r * X.presheaf.map (homOfLE h).op y := fun y ↦ by
      rw [e]
      exact map_mul (X.presheaf.map (homOfLE h).op).hom _ y
    exact key x

private theorem sectionsOn_toΓ_secRes_eq_presheaf_map
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W ≤ U) (x : GlobalTheory.CechDR.Sec s U) :
    GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W (secRes s hs h x) =
      X.presheaf.map (homOfLE h).op (x : Γ(X, U)) :=
  AddEquiv.apply_symm_apply _ _

theorem secRes_bijective
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W = U) : Function.Bijective (secRes s hs h.le) := by
  subst h
  have key : ∀ x : GlobalTheory.CechDR.Sec s W, secRes s hs (le_refl W) x =
      (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (x : Γ(X, W)) := by
    intro x
    have hx : X.presheaf.map (homOfLE (le_refl W)).op (x : Γ(X, W)) = (x : Γ(X, W)) := by
      change (X.presheaf.map (𝟙 (op W))) (x : Γ(X, W)) = x
      rw [X.presheaf.map_id]
      rfl
    exact congrArg (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm hx
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · rw [key, key] at hxy
    exact (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm.injective hxy
  · refine ⟨(show GlobalTheory.CechDR.Sec s W from GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W y), ?_⟩
    rw [key]
    exact (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm_apply_apply y

private theorem sectionsOn_toΓ_res_eq_presheaf_map {U V : X.Opens} (h : V ≤ U)
    (y : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) U) :
    GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) V (GlobalTheory.sectionsOn.res R (GlobalTheory.structureModule X) h y) =
      (GlobalTheory.structureModule X).presheaf.map (homOfLE h).op (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) U y) :=
  GlobalTheory.WithAction.toBase_linearMap _ _ R _ _ y

theorem secRes_square
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U V V' W : X.Opens} (a : V ≤ U) (b : W ≤ V) (c : V' ≤ U) (d : W ≤ V') (x : GlobalTheory.CechDR.Sec s U) :
    secRes s hs b (GlobalTheory.CechDR.Sec.res s a x) =
      GlobalTheory.sectionsOn.res R (GlobalTheory.structureModule X) d (secRes s hs c x) := by
  apply (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective
  rw [sectionsOn_toΓ_secRes_eq_presheaf_map, sectionsOn_toΓ_res_eq_presheaf_map, sectionsOn_toΓ_secRes_eq_presheaf_map]
  change (X.presheaf.map (homOfLE b).op) ((X.presheaf.map (homOfLE a).op) (x : Γ(X, U))) =
    (X.presheaf.map (homOfLE d).op) ((X.presheaf.map (homOfLE c).op) (x : Γ(X, U)))
  have h1 : X.presheaf.map (homOfLE a).op ≫ X.presheaf.map (homOfLE b).op =
      X.presheaf.map (homOfLE c).op ≫ X.presheaf.map (homOfLE d).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (fun f : X.presheaf.obj (op U) ⟶ X.presheaf.obj (op W) => f (x : Γ(X, U))) h1

end

section

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of R)) [Algebra R Γ(X, ⊤)]
  {P : Type} [SemilatticeInf P] (S : MainStatements.Hodge.Sys X P) {κ : Type} (e : κ → P)

theorem sys_inf' (t : Finset κ) (ht : t.Nonempty) :
    (S.u (t.inf' ht e)).1 = ⊤ ⊓ ⨅ i ∈ t, (S.u (e i)).1 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · rw [Finset.inf'_insert hs, S.map_inf, ih hs, Finset.iInf_insert]
      simp only [top_inf_eq]
    · obtain rfl : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp

variable (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))

def sysVertex (t : Finset κ) :
    (cubeOf e (toMod (MainStatements.Hodge.OSys s S))).obj t →ₗ[R]
      (GlobalTheory.cechCube R (GlobalTheory.structureModule X) ⊤ fun i ↦ (S.u (e i)).1).obj t :=
  if ht : t.Nonempty then
    (secRes s hs (sys_inf' S e t ht).ge) ∘ₗ
      LinearMap.proj (R := R) (φ := fun h : PLift t.Nonempty ↦
        ((toMod (MainStatements.Hodge.OSys s S)).obj (op (t.inf' h.down e)) : Type)) ⟨ht⟩
  else 0

theorem sysVertex_apply (t : Finset κ) (ht : t.Nonempty) (x : (cubeOf e (toMod (MainStatements.Hodge.OSys s S))).obj t) :
    sysVertex s S e hs t x = secRes s hs (sys_inf' S e t ht).ge (x ⟨ht⟩) := by
  unfold sysVertex
  rw [dite_eq_left ht]
  rfl

theorem sysVertex_of_not_nonempty (t : Finset κ) (ht : ¬ t.Nonempty) : sysVertex s S e hs t = 0 := by
  unfold sysVertex
  rw [dite_eq_right ht]

theorem sysVertex_bijective (t : Finset κ) (ht : t.Nonempty) : Function.Bijective (sysVertex s S e hs t) := by
  have hf : ⇑(sysVertex s S e hs t) = (secRes s hs (sys_inf' S e t ht).ge) ∘ (fun x => x ⟨ht⟩) :=
    funext fun x => sysVertex_apply s S e hs t ht x
  rw [hf]
  refine (secRes_bijective s hs (sys_inf' S e t ht).symm).comp ⟨fun x y hxy => ?_, fun y => ?_⟩
  · funext h
    obtain ⟨h⟩ := h
    exact hxy
  · exact ⟨fun _ => y, rfl⟩

def sysCube : cubeOf e (toMod (MainStatements.Hodge.OSys s S)) ⟶
    GlobalTheory.cechCube R (GlobalTheory.structureModule X) ⊤ fun i ↦ (S.u (e i)).1 :=
  GlobalTheory.Cube.homMk κ R (sysVertex s S e hs) fun {t t'} h x ↦ by
    by_cases ht : t.Nonempty
    · have ht' : t'.Nonempty := ht.mono h
      rw [sysVertex_apply s S e hs t' ht', sysVertex_apply s S e hs t ht]
      have e1 := cubeRes_apply e (toMod (MainStatements.Hodge.OSys s S)) h x ht ⟨ht'⟩
      refine (congrArg (secRes s hs (sys_inf' S e t' ht').ge) e1).trans ?_
      exact secRes_square s hs _ _ _ _ (x ⟨ht⟩)
    · rw [sysVertex_of_not_nonempty s S e hs t ht, LinearMap.zero_apply, map_zero]
      by_cases ht' : t'.Nonempty
      · rw [sysVertex_apply s S e hs t' ht']
        have e1 := cubeRes_empty e (toMod (MainStatements.Hodge.OSys s S)) h x ht ⟨ht'⟩
        exact (congrArg (secRes s hs (sys_inf' S e t' ht').ge) e1).trans (map_zero _)
      · rw [sysVertex_of_not_nonempty s S e hs t' ht', LinearMap.zero_apply]

theorem isIso_sysCube [LinearOrder κ] : IsIso (GlobalTheory.cechComplexMap (sysCube s S e hs)) := by
  apply GlobalTheory.isIso_cechComplexMap
  intro t ht
  rw [sysCube, GlobalTheory.Cube.homMk_app, ModuleCat.hom_ofHom]
  exact sysVertex_bijective s S e hs t ht

end

theorem cech_OSys_homology_equiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) := by
  intro R _ X s P _ S κ _ e n
  letI := GlobalTheory.algebraΓOfHom s
  have hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) :=
    fun r => rfl
  haveI := isIso_sysCube s S e hs
  exact ⟨((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (asIso (GlobalTheory.cechComplexMap (sysCube s S e hs)))).toLinearEquiv⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Low

variable {R : Type} [CommRing R]

theorem homology_equiv {A B D : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] [Module R A] [Module R B]
    [Module R D] (a : A →ₗ[R] B) (b : B →ₗ[R] D)
    (w : ModuleCat.ofHom a ≫ ModuleCat.ofHom b = 0) :
    Nonempty ((LinearMap.ker b ⧸ (LinearMap.range a).comap (LinearMap.ker b).subtype) ≃ₗ[R]
      (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).homology) := by
  have heq : (LinearMap.range a).comap (LinearMap.ker b).subtype =
      LinearMap.range (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).moduleCatToCycles := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ heq).trans
    (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).moduleCatHomologyIso.symm.toLinearEquiv⟩

variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev nerveComplex : CochainComplex (ModuleCat.{0} R) ℕ :=
  nerveCx.obj (F ⋙ forget₂ (CommAlgCat.{0} R) (AlgCat.{0} R) ⋙ forget₂ (AlgCat.{0} R) (ModuleCat.{0} R))

theorem d_eq (n : ℕ) : (nerveComplex F).d n (n + 1) = ModuleCat.ofHom (MainStatements.Hodge.dn F n) :=
  nerveCx_d _ n

theorem d_zero : (nerveComplex F).d 0 0 = ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0) :=
  ((nerveComplex F).shape 0 0 (by simp)).trans ModuleCat.ofHom_zero.symm

theorem comp_eq (n : ℕ) :
    ModuleCat.ofHom (MainStatements.Hodge.dn F n) ≫ ModuleCat.ofHom (MainStatements.Hodge.dn F (n + 1)) = 0 := by
  simpa only [d_eq] using! (nerveComplex F).d_comp_d n (n + 1) (n + 1 + 1)

theorem comp_zero_eq :
    ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0) ≫ ModuleCat.ofHom (MainStatements.Hodge.dn F 0) = 0 := by
  rw [ModuleCat.ofHom_zero, zero_comp]

def scIso (n : ℕ) : (nerveComplex F).sc' n (n + 1) (n + 2) ≅
    ShortComplex.mk (ModuleCat.ofHom (MainStatements.Hodge.dn F n)) (ModuleCat.ofHom (MainStatements.Hodge.dn F (n + 1))) (comp_eq F n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((d_eq F n).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((d_eq F (n + 1)).symm.trans (Category.comp_id _).symm))

def scIso0 : (nerveComplex F).sc' 0 0 1 ≅
    ShortComplex.mk (ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0)) (ModuleCat.ofHom (MainStatements.Hodge.dn F 0))
      (comp_zero_eq F) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((d_zero F).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((d_eq F 0).symm.trans (Category.comp_id _).symm))

theorem homology_nerveCx :
    ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveComplex F).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveComplex F).homology (n + 1)) := by
  intro R _ C _ F
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨e⟩ := GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_equiv
      (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0)
      (MainStatements.Hodge.dn F 0) (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.comp_zero_eq F)
    have hbot : (LinearMap.range (0 : MainStatements.Hodge.Cn F 0 →ₗ[R]
        MainStatements.Hodge.Cn F 0)).comap
        (LinearMap.ker (MainStatements.Hodge.dn F 0)).subtype = ⊥ := by
      simp
    exact ⟨((Submodule.quotEquivOfEqBot _ hbot).symm.trans e).trans
      (((nerveComplex F).homologyIsoSc'
        0 0 1 (by simp) (by simp)) ≪≫
        ShortComplex.homologyMapIso (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.scIso0 F)).symm.toLinearEquiv⟩
  · obtain ⟨e⟩ := GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_equiv
      (MainStatements.Hodge.dn F n) (MainStatements.Hodge.dn F (n + 1))
      (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.comp_eq F n)
    exact ⟨e.trans
      (((nerveComplex F).homologyIsoSc'
        n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
        ShortComplex.homologyMapIso (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.scIso F n)).symm.toLinearEquiv⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve.Low
end
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_mem_twKer_box (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V)
    (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V)
    (hv : v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype)) :
    ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  classical
  have hmem : ∀ x : Multiplicative (Fin n → k), ∃ N : ℤ, x ∈ box k n N := by
    intro x
    choose m hm using fun i => exists_mem_valBall_neg_nat (K := k) (Multiplicative.toAdd x i)
    refine ⟨-((∑ i, m i : ℕ) : ℤ), (mem_box k).2 fun i => ?_⟩
    have h1 := hm i
    have hle : m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
    change normalizedValuation k _ ≤ WithZero.exp (-(-((m i : ℕ) : ℤ))) at h1
    change normalizedValuation k _ ≤ WithZero.exp (-(-((∑ j, m j : ℕ) : ℤ)))
    refine h1.trans (WithZero.exp_le_exp.2 ?_)
    simp only [neg_neg]
    exact_mod_cast hle
  unfold GlobalTheory.PRep.twKer at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, u, rfl⟩ := hx
    obtain ⟨N, hN⟩ := hmem g.1
    exact ⟨N, fun j' hj' => Submodule.subset_span ⟨⟨g.1, box_antitone k n hj' hN⟩, u, rfl⟩⟩
  | zero => exact ⟨0, fun j' _ => Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, fun j' hj' => Submodule.add_mem _ (ha j' (hj'.trans (min_le_left _ _)))
      (hb j' (hj'.trans (min_le_right _ _)))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, fun j' hj' => Submodule.smul_mem _ c (ha j' hj')⟩

end GlobalTheory.CompanionTheory.MirFourier
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

theorem _root_.GlobalTheory.T.mirabolic_restriction_unipotent_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir | exact GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir | (intros; apply GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Smooth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

theorem isSmoothChar_fibChar {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) :
    IsSmoothChar (fibChar (k := k) a c d μ) := by
  have hA : ∀ s : ℂ, IsSmoothChar (absPow k s) := fun s => isSmoothChar_of_isUnram (isUnram_absPow k s)
  refine IsSmoothChar.mul (IsSmoothChar.mul ?_ ?_) ?_
  · exact (IsSmoothChar.detChar (hμ.inv.mul (hA _))).comp _ continuous_fst
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_fst.comp continuous_snd)
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_snd.comp continuous_snd)

private theorem isSmooth_sbRep_of_continuous_action {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (r : X → Γ → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ (x : X) (g h : Γ), r x (g * h) = r (r x g) h)
    (hc : ∀ g, Continuous fun x => r x g) (hj : Continuous fun p : X × Γ => r p.1 p.2) :
    IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep r h1 hm hc) := by
  apply GlobalTheory.SmGL.isSmooth_of_nhds
  intro φ
  obtain ⟨hlc, hcs⟩ := φ.2
  have hopen : IsOpen {z : Γ × X | (φ : X → ℂ) (r z.2 z.1) = (φ : X → ℂ) z.2} := by
    have h1lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) (r z.2 z.1)) :=
      hlc.comp_continuous (hj.comp continuous_swap)
    have h2lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) z.2) :=
      hlc.comp_continuous continuous_snd
    have := (h1lc.comp₂ h2lc (fun u v => u - v)).isOpen_fiber 0
    simpa only [sub_eq_zero] using this
  have hev : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ), (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x := by
    refine IsCompact.eventually_forall_of_forall_eventually hcs ?_
    intro x _
    exact hopen.mem_nhds (by simp only [Set.mem_ofPred_eq, h1])
  have hev' : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ),
      (φ : X → ℂ) (r x γ⁻¹) = (φ : X → ℂ) x := by
    have ht : Filter.Tendsto (fun γ : Γ => γ⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : Γ))
    exact ht.eventually hev
  filter_upwards [hev, hev'] with γ hγ hγ'
  apply Subtype.ext
  funext x
  show (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x
  by_cases hx : x ∈ tsupport (φ : X → ℂ)
  · exact hγ x hx
  · by_cases hy : r x γ ∈ tsupport (φ : X → ℂ)
    · have e := hγ' _ hy
      rw [← hm, mul_inv_cancel, h1] at e
      exact e.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

private theorem isSmooth_fibBase (κ : ℕ) : IsSmooth (fibBase (k := k) a c κ) := by
  show IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep _ _ _ _)
  apply isSmooth_sbRep_of_continuous_action
  apply Continuous.subtype_mk
  have hinv : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (((p.2.2)⁻¹ : GL c k) : Matrix c c k) :=
    Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_snd))
  have hx : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (p.1 : Matrix c a k) :=
    continuous_subtype_val.comp continuous_fst
  have hg : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      ((p.2.1 : GL a k) : Matrix a a k) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  exact (hinv.matrix_mul hx).matrix_mul hg

theorem isSmooth_fibRep_levi (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (κ : ℕ) :
    IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  have hB := isSmooth_fibBase (k := k) a c κ
  have hρ := isSmooth_comp hB ((MonoidHom.id (GL a k)).prodMap (MonoidHom.fst (GL c k) (GL d k)))
    (continuous_id.prodMap continuous_fst)
  have ht := isSmooth_twist hρ (isSmoothChar_fibChar a c d hμ)
  exact isSmooth_comp ht (MonoidHom.inr (GL a k) (GL c k × GL d k)) (continuous_const.prodMk continuous_id)

end Smooth

end GlobalTheory.CompanionTheory.ThetaGLLen

namespace GlobalTheory.CompanionTheory.ThetaGLLen

theorem isSmooth_fibRep_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  intro k _ _ _ _ a c d _ _ _ _ _ _ μ hμ κ
  exact isSmooth_fibRep_levi a c d μ hμ κ

end GlobalTheory.CompanionTheory.ThetaGLLen
end

section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_coordinates : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  first | exact @GlobalTheory.CompanionTheory.SW.CoordR.coordInf | exact GlobalTheory.CompanionTheory.SW.CoordR.coordInf | (intros; apply GlobalTheory.CompanionTheory.SW.CoordR.coordInf <;> assumption)
end
end

section

open ReciprocityTheory.Ty.Fin

theorem _root_.GlobalTheory.T.separable_irreducible : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  first | exact @GlobalTheory.CompanionTheory.FinRep.sepIrr | exact GlobalTheory.CompanionTheory.FinRep.sepIrr | (intros; apply GlobalTheory.CompanionTheory.FinRep.sepIrr <;> assumption)
end
