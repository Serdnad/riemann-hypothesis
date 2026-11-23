module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

theorem unipAt_inv_liftLa : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (I : Ideal (𝓞 E)) («γ» : LevelAut Dw l), l.Mb ≤ I → UnipAt I «γ» → ∃ m : ℕ, ∀ x : Dw.La, ((liftLa «γ»⁻¹ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  intro E _ _ _ H Dw l I γ hI hU
  obtain ⟨m, hm⟩ := hU
  set M : Submodule (𝓞 E) Dw.La := I • ⊤ with hMdef
  set f := liftLa γ with hfdef
  set g := liftLa γ⁻¹ with hgdef
  have hN : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤ M := Submodule.smul_mono_left hI
  have hpres : ∀ φ : Dw.La →ₗ[𝓞 E] Dw.La, M ≤ M.comap φ := by
    intro φ
    rw [← Submodule.map_le_iff_le_comap, hMdef, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have hgf : ∀ x, g (f x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec (γ⁻¹) (f x)
    have h2 := liftLa_spec γ x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hgdef, h1, hfdef, h2]
    exact γ.symm_apply_apply _
  have hfg : ∀ x, f (g x) - x ∈ M := by
    intro x
    apply hN
    rw [← Submodule.Quotient.eq]
    have h1 := liftLa_spec γ (g x)
    have h2 := liftLa_spec (γ⁻¹) x
    simp only [Submodule.mkQ_apply] at h1 h2
    rw [hfdef, h1, hgdef, h2]
    exact γ.apply_symm_apply _
  let A := M.mapQ M f (hpres f)
  let B := M.mapQ M g (hpres g)
  have hBA : B * A = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hgf x)
  have hAB : A * B = 1 := by
    ext x
    simp only [Module.End.mul_apply, A, B, Submodule.mapQ_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq M).2 (hfg x)
  have hdesc : ∀ (φ : Dw.La →ₗ[𝓞 E] Dw.La) (k : ℕ) (x : Dw.La),
      M.mkQ (((φ - 1) ^ k) x) = ((M.mapQ M φ (hpres φ) - 1) ^ k) (M.mkQ x) := by
    intro φ k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
  have hA0 : (A - 1) ^ m = 0 := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [← Submodule.mkQ_apply, ← hdesc f m x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hm x
  have hcomm : Commute B (1 - A) := by
    refine Commute.sub_right (Commute.one_right B) ?_
    exact (hBA.trans hAB.symm)
  have hB0 : (B - 1) ^ m = 0 := by
    have e : B - 1 = B * (1 - A) := by rw [mul_sub, mul_one, hBA]
    rw [e, hcomm.mul_pow, show (1 - A) = -(A - 1) by abel, neg_pow, hA0, mul_zero, mul_zero]
  refine ⟨m, fun x => ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hdesc g m x, hB0, LinearMap.zero_apply]

end GlobalTheory.OrbitSep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

theorem algebraMap_stalkCongr_of_eq {X : Scheme.{0}} [IsIntegral X] {x y : X} (h : x = y)
    (a : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk y) X.functionField ((X.presheaf.stalkCongr (.of_eq h)).hom a) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
  subst h
  simp

theorem fromSpecResidueField_comp_eq_of_fixes (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ]
    (ρ : Γ →* Aut X) (γ : Γ) (x : X) (hx : (ρ γ).asIso.hom x = x)
    (h : ∀ u : X.functionFieldˣ, RegAt x u → ZeroAt x ((fnAct ρ γ u : X.functionField) - u)) :
    X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x := by
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  set φ := (ρ γ).asIso.hom with hφ
  have key : (X.residueFieldCongr hx.symm).hom ≫ φ.residueFieldMap x = 𝟙 _ := by
    rw [← cancel_epi (X.residue x), Category.comp_id, X.residue_residueFieldCongr_assoc,
      Scheme.residue_residueFieldMap]
    ext a
    change IsLocalRing.residue _ (φ.stalkMap x ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom a)) =
      IsLocalRing.residue _ a
    set b := (X.presheaf.stalkCongr (.of_eq hx.symm)).hom a with hb
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    by_cases ha : a = 0
    · rw [hb, ha, map_zero, map_zero, sub_zero]
      exact zero_mem _
    · have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
      obtain ⟨c, hc, e⟩ := h (Units.mk0 _ hne) ⟨a, rfl⟩
      have e2 : ((fnAct ρ γ (Units.mk0 _ hne) : X.functionFieldˣ) : X.functionField) =
          GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) := rfl
      have e4 : GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) =
          algebraMap (X.presheaf.stalk x) X.functionField (φ.stalkMap x b) := by
        rw [← algebraMap_stalkCongr_of_eq hx.symm a, ← hb]
        exact GlobalTheory.functionFieldMap_algebraMap φ x b
      rw [e2, Units.val_mk0, e4, ← map_sub] at e
      rwa [← IsFractionRing.injective _ _ e]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← X.residueFieldCongr_fromSpecResidueField hx.symm, ← Category.assoc, ← Spec.map_comp, key,
    Spec.map_id, Category.id_comp]

end GlobalTheory.OrbitSep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut LevelMod)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev pullG (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) : Over X' :=
  (Over.pullback (φ ≫ (barComp TF.Y Z).ι)).obj TF.Y.t.G

abbrev pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    (pullG TF Z φ).left ⟶ TF.Y.t.G.left :=
  pullback.fst _ _

abbrev pullAct (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    OAct (𝓞 E) (pullG TF Z φ) :=
  OAct.pullback (φ ≫ (barComp TF.Y Z).ι) TF.Y.t.G TF.Y.t.act

instance grpObj_pullG (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    GrpObj (pullG TF Z φ) :=
  inferInstance

theorem isGrpPullback_pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    IsGrpPullback (pullG TF Z φ) TF.Y.t.G (φ ≫ (barComp TF.Y Z).ι) (pullψ TF Z φ) :=
  isGrpPullback_pullback _ _

theorem pullAct_pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (a : 𝓞 E) :
    ((pullAct TF Z φ).act a).left ≫ pullψ TF Z φ = pullψ TF Z φ ≫ (TF.Y.t.act.act a).left :=
  pullback.lift_fst _ _ _

variable {Γ : Type} [Group Γ]

def IsEqvAct {X' : Scheme.{0}} (ρ' : Γ →* Aut X') (G' : Over X') [GrpObj G'] (act' : OAct (𝓞 E) G')
    (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  (∀ γ, IsGrpPullback G' G' (ρ' γ).asIso.hom (m γ)) ∧ (∀ γ a, (act'.act a).left ≫ m γ = m γ ≫ (act'.act a).left) ∧
    ∀ γ₁ γ₂, m (γ₁ * γ₂) = m γ₂ ≫ m γ₁

def MovesEta (TF : TorFlag Xo c) (Z : Comp Xo c) (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z))
    {X' : Scheme.{0}} (ℓ : V₀ TF.Y Z ⟶ X') (G' : Over X') (ψ : G'.left ⟶ TF.Y.t.G.left)
    (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  ∀ (γ : Γ) (a b : Dw.La), (Submodule.Quotient.mk b : LevelMod Dw l) = (ι γ)⁻¹ (Submodule.Quotient.mk a) →
    ∀ w w' : V₀ TF.Y Z ⟶ G'.left, w ≫ G'.hom = ℓ → w' ≫ G'.hom = ℓ →
      w ≫ ψ = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ →
      w' ≫ ψ = i₀ TF.Y Z ≫ (TF.Y.oF.eta a).left ≫ TF.Y.m.φ →
      w ≫ m γ = (ρ γ).asIso.hom ≫ w'

def IsTorsI (I : Ideal (𝓞 E)) {X' : Scheme.{0}} {G' : Over X'} [GrpObj G'] (act' : OAct (𝓞 E) G') {T : Over X'}
    (P : T ⟶ G') : Prop :=
  ∀ a ∈ I, P ≫ act'.act a = 1

def TorsLevel (I : Ideal (𝓞 E)) (ι : Γ →* LevelAut Dw l) {X' : Scheme.{0}} (ρ' : Γ →* Aut X') (G' : Over X')
    [GrpObj G'] (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X'), ∃ e : (Over.mk t ⟶ G') → LevelMod Dw l,
    (∀ P Q, IsTorsI I act' P → IsTorsI I act' Q → e (P * Q) = e P + e Q) ∧
    (∀ P (a : 𝓞 E), IsTorsI I act' P → e (P ≫ act'.act a) = a • e P) ∧
    (∀ P Q, IsTorsI I act' P → IsTorsI I act' Q → e P = e Q → P = Q) ∧
    ∀ γ, t ≫ (ρ' γ).asIso.hom = t → ∀ P Q : Over.mk t ⟶ G', IsTorsI I act' P → Q.left = P.left ≫ m γ →
      e Q = ι γ (e P)

end GlobalTheory.EqvAct
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.GenInterior

theorem exists_j₀_eq_genericPoint (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] :
    ∃ v : V₀ TF.Y Z, j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  obtain ⟨x, hx⟩ := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  have hxm : TF.Y.j x ∈ barComp TF.Y Z := (j_mem_barComp Z x).2 hx
  let v : V₀ TF.Y Z := ⟨x, hxm⟩
  have hU : IsOpen (Set.range (j₀ TF.Y Z)) := (j₀ TF.Y Z).isOpenEmbedding.isOpen_range
  exact ((genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff hU).2 ⟨j₀ TF.Y Z v, trivial, v, rfl⟩

end GlobalTheory.GenInterior
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open TopForm

section Pair

variable {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}

def topPair (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) : Forms α n →ₗ[A] A :=
  letI := α.toAlgebra
  exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap
    (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)))

end Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev PairIx (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) : Type :=
  Σ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, Fin (Dw.mult τ.1) × Fin (Dw.mult ((starRingEnd ℂ).comp τ.1))

def symPair {R : Type} [CommRing R] {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : PairIx H Dw) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b =>
    (if a = e ⟨P.1.1, P.2.1⟩ ∧ b = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ then 1 else 0) +
      (if a = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ b = e ⟨P.1.1, P.2.1⟩ then 1 else 0)

abbrev genPt (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z :=
  (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))

abbrev GenDer (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Type :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField

def GenKS (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left))
    (D : Fin Dw.dim → GenDer TF Z) : Prop :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (ε : Fin Dw.dim ≃ PairIx H Dw)
    (Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U),
    spMap ρ ≫ LogKS.chart U = genPt TF Z ≫ (barComp TF.Y Z).ι ∧
    (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧
    (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧
    (∀ τ i, w τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧
    (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (Dl j).1 (symPair e (ε j))) ∧
    ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r)

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

open TopForm

theorem topPair_dForm {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) (f : Fin n → A) :
    topPair α D (dForm α f) = (Matrix.of fun i j => (letI := α.toAlgebra; (D j : Derivation k A A)) (f i)).det := by
  letI := α.toAlgebra
  rw [dForm_eq, topPair, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  change Matrix.det (Matrix.of _) = _
  congr 1
  ext i j
  exact Derivation.liftKaehlerDifferential_comp_D (D j) (f i)

end GlobalTheory.LogKSDiv
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

theorem functionFieldMap_germToFunctionField {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ X') [IsDominant f] (V : X'.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) [Nonempty U]
    [Nonempty V] (s : Γ(X', V)) :
    functionFieldMap f (X'.germToFunctionField V s) = X.germToFunctionField U (f.appLE V U e s) := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hfx : f (genericPoint X) ∈ V := e hx
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X') hfx, functionFieldMap_algebraMap,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx]
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply f V _ hfx s).trans
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE e) _ hx (f.app V s)).symm

theorem exists_functionFieldMap_eq_of_invariant (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W]
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q]
    (h : IsAffineQuotient ρ q) (u : X.functionFieldˣ) (hu : ∀ γ, fnAct ρ γ u = u) :
    ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  classical
  have := Fintype.ofFinite Γ
  have := h.isAffineHom
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  haveI : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := (show IsAffineOpen V from hV).preimage q
  obtain ⟨x, hx⟩ := q.denseRange.exists_mem_open V.isOpen ⟨_, hyV⟩
  haveI : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  have hst := h.preimage_le V
  haveI (γ : Γ) : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  let σ : Γ → Γ(X, q ⁻¹ᵁ V) →+* Γ(X, q ⁻¹ᵁ V) := fun γ ↦ ((ρ γ).asIso.hom.appLE _ _ (hst γ)).hom
  have hσ (γ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) :
      functionFieldMap (ρ γ).asIso.hom (algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField s) =
        algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField (σ γ s) :=
    functionFieldMap_germToFunctionField _ _ _ (hst γ) s
  have hσ1 (s : Γ(X, q ⁻¹ᵁ V)) : σ 1 s = s := by
    have e1 : (ρ 1).asIso.hom = 𝟙 X := by rw [map_one]; rfl
    change (ρ 1).asIso.hom.appLE _ _ (hst 1) s = s
    simp only [e1]
    exact congr($(X.presheaf.map_id (Opposite.op (q ⁻¹ᵁ V))) s)
  have hσmul (γ δ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) : σ δ (σ γ s) = σ (γ * δ) s := by
    have e2 : (ρ (γ * δ)).asIso.hom = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom := by rw [map_mul]; rfl
    change (ρ δ).asIso.hom.appLE _ _ (hst δ) ((ρ γ).asIso.hom.appLE _ _ (hst γ) s) =
      (ρ (γ * δ)).asIso.hom.appLE _ _ (hst (γ * δ)) s
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, e2]
  set e := algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField with he_def
  have einj : Function.Injective e := IsFractionRing.injective _ _
  have hfu (δ : Γ) : functionFieldMap (ρ δ).asIso.hom (u : X.functionField) = u :=
    congrArg Units.val (hu δ)
  obtain ⟨a, t, ht, hat⟩ := IsFractionRing.div_surjective (A := Γ(X, q ⁻¹ᵁ V)) (u : X.functionField)
  have ht0 : e t ≠ 0 := by
    rw [Ne, ← map_zero e]
    exact fun h0 ↦ nonZeroDivisors.ne_zero ht (einj h0)
  let N := ∏ γ, σ γ t
  have hN (δ : Γ) : σ δ N = N := by
    simp only [N, map_prod, hσmul]
    exact Fintype.prod_equiv (Equiv.mulRight δ) _ _ (fun _ ↦ rfl)
  have hNe : e N ≠ 0 := by
    simp only [N, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun γ _ ↦ ?_
    rw [← hσ]
    exact (map_ne_zero _).mpr ht0
  let c := a * ∏ γ ∈ Finset.univ.erase 1, σ γ t
  have hc : e c = u * e N := by
    have hsplit : N = t * ∏ γ ∈ Finset.univ.erase 1, σ γ t := by
      simp only [N]
      rw [← Finset.mul_prod_erase Finset.univ (fun γ ↦ σ γ t) (Finset.mem_univ 1), hσ1]
    rw [← he_def] at hat
    rw [hsplit]
    simp only [c, map_mul]
    rw [← hat]
    field_simp
  have hcinv (δ : Γ) : σ δ c = c := by
    apply einj
    rw [← hσ, hc, map_mul, hfu, hσ, hN]
  obtain ⟨bc, hbc⟩ := h.mem_range_app V c fun δ ↦ ⟨hst δ, hcinv δ⟩
  obtain ⟨bN, hbN⟩ := h.mem_range_app V N fun δ ↦ ⟨hst δ, hN δ⟩
  have hq (b : Γ(W, V)) : functionFieldMap q (W.germToFunctionField V b) = e (q.app V b) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact functionFieldMap_germToFunctionField q V (q ⁻¹ᵁ V) le_rfl b
  have hbN0 : W.germToFunctionField V bN ≠ 0 := by
    intro h0
    apply hNe
    rw [← hbN, ← hq, h0, map_zero]
  have hbc0 : W.germToFunctionField V bc ≠ 0 := by
    intro h0
    apply mul_ne_zero u.ne_zero hNe
    rw [← hc, ← hbc, ← hq, h0, map_zero]
  refine ⟨Units.mk0 (W.germToFunctionField V bc / W.germToFunctionField V bN)
    (div_ne_zero hbc0 hbN0), Units.ext ?_⟩
  simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_div₀, hq, hbc, hbN, hc]
  field_simp

end GlobalTheory.OrbitSep
end
end
