module

public import Mathlib.RingTheory.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows

open AlgebraicGeometry CategoryTheory Opposite NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped MonObj

section Der

variable {g : ℕ} {Y : Scheme.{0}}

instance isLocalHom_fst : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩

instance isLocalHom_epsMul (cc : ℂ) : IsLocalHom (epsMul cc) :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by
    have := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha
    simpa [epsMul] using this)⟩

instance isLocalHom_fst' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) :=
  isLocalHom_fst

theorem dual_top_le (W : (Spec (CommRingCat.of (DualNumber ℂ))).Opens)
    (hW : IsLocalRing.closedPoint (DualNumber ℂ) ∈ W) : ⊤ ≤ W := by
  intro x _
  have hs : (x : PrimeSpectrum (DualNumber ℂ)) ⤳ IsLocalRing.closedPoint (DualNumber ℂ) := by
    first
    | exact IsLocalRing.specializes_closedPoint _
    | exact (PrimeSpectrum.le_iff_specializes _ _).1
        (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum (DualNumber ℂ)).2.ne_top)
  exact hs.mem_open W.isOpen hW

theorem fst_appLE {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (hU : ⊤ ≤ (e 0) ⁻¹ᵁ U) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(Y, U)) :
    TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h f)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ hU f) := by
  have he : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := hv.1
  have hh : ∀ {a b : Sp ℂ ⟶ Y} (_ : a = b) (h1 : ⊤ ≤ a ⁻¹ᵁ U) (h2 : ⊤ ≤ b ⁻¹ᵁ U),
      a.appLE U ⊤ h1 = b.appLE U ⊤ h2 := by
    intro a b hab h1 h2
    subst hab
    rfl
  have h0 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
    rw [he]
    exact hU
  have key := specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h
  rw [← hh he h0 hU]
  have key2 := congrArg (fun φ => φ.hom f) key
  first
  | exact key2.symm
  | simpa using key2.symm

theorem tangent_open_preimage_zero {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) : ⊤ ≤ (e 0) ⁻¹ᵁ U := by
  intro x _
  rw [← hv.1]
  have hx := h (show (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
  first
  | exact hx
  | (simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; exact hx)

theorem isDerivAt0_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (hv' : IsDerivAt0 e w v') : v = v' := by
  apply hom_ext_of_local
  · have hc : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base (IsLocalRing.closedPoint ℂ) =
        IsLocalRing.closedPoint (DualNumber ℂ) :=
      IsLocalRing.comap_closedPoint _
    have e1 := congrArg (fun φ => φ.base (IsLocalRing.closedPoint ℂ)) (hv.1.trans hv'.1.symm)
    have e2 : v ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) =
        v' ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) := e1
    rw [hc] at e2
    exact e2
  · intro U h₁ h₂
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]
    ext f
    have hU := tangent_open_preimage_zero hv U h₁
    · exact (fst_appLE hv U hU h₁ f).trans (fst_appLE hv' U hU h₂ f).symm
    · exact (hv.2 U h₁ f).trans (hv'.2 U h₂ f).symm

theorem isDerivAt0_comp_hom {Y' : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e w v) (φ : Y ⟶ Y') :
    IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨by rw [← Category.assoc, hv.1], fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
  have key := hv.2 (φ ⁻¹ᵁ U) h' (φ.app U f)
  simp only [← valAt'_comp]
  rw [← key]
  have hc : (v ≫ φ).appLE U ⊤ h = φ.app U ≫ v.appLE (φ ⁻¹ᵁ U) ⊤ h' := by
    first
    | exact Scheme.comp_appLE v φ U ⊤ h
    | exact Scheme.Hom.comp_appLE v φ U ⊤ h
    | simp [Scheme.Hom.appLE]
  rw [hc]
  rfl

theorem isDerivAt0_smul {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (cc : ℂ) : IsDerivAt0 e (cc • w) (spMap (epsMul cc) ≫ v) := by
  have hcomp : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsMul cc) =
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
    RingHom.ext fun x => by simp [epsMul]
  refine ⟨?_, fun U h f => ?_⟩
  · rw [← Category.assoc, ← hv.1]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  · have hp : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ U := by
      have hx := h (show IsLocalRing.closedPoint (DualNumber ℂ) ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
      have hc : (spMap (epsMul cc)).base (IsLocalRing.closedPoint (DualNumber ℂ)) =
          IsLocalRing.closedPoint (DualNumber ℂ) :=
        IsLocalRing.comap_closedPoint (epsMul cc)
      first
      | (rw [← hc]; exact hx)
      | (simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; rwa [hc] at hx)
    have hq : ⊤ ≤ v ⁻¹ᵁ U := dual_top_le _ hp
    have key := congrArg (fun φ => φ.hom f) (specMap_comp_appLE (CommRingCat.ofHom (epsMul cc)) v U h hq)
    have hd := hv.2 U hq f
    simp only at key
    rw [map_smul, ← hd]
    show TrivSqZeroExt.snd (((spMap (epsMul cc) ≫ v).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom).hom f) = _
    rw [key]
    first
    | simp [epsMul]
    | rfl

theorem isDerivAt0_comp_lin {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (hol : IsHolFam e) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e (D w) v) :
    IsDerivAt0 (fun z => e (D z)) w v := by
  refine ⟨by show _ = e (D 0); rw [map_zero]; exact hv.1, fun U h f => ?_⟩
  rw [hv.2 U h f]
  have h0 : (0 : Fin g → ℂ) ∈ {z | ⊤ ≤ e z ⁻¹ᵁ U} := tangent_open_preimage_zero hv U h
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (D 0) := by
    rw [map_zero]
    exact ((hol U f).2 0 h0).differentiableAt ((hol U f).1.mem_nhds h0)
  have hc := fderiv_comp (0 : Fin g → ℂ) hd D.differentiableAt
  show _ = fderiv ℂ ((fun z => valAt' (e z) U f) ∘ D) 0 w
  rw [hc, ContinuousLinearMap.fderiv, map_zero]
  rfl

end Der

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

def tyD (ty : Fin g → (E →+* ℂ)) (a : NumberField.RingOfIntegers E) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z k => ty k (a : E) * z k
      map_add' := fun z z' => by funext k; simp [mul_add]
      map_smul' := fun t z => by funext k; simp; ring }

theorem tyD_apply (a : NumberField.RingOfIntegers E) (z : Fin g → ℂ) : tyD ty a z = fun k => ty k (a : E) * z k := rfl

theorem derivAt_over (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left}
    (hv : IsDerivAt0 (fun z => (F.ex i P z).left) w v) :
    v ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ F.u i P := by
  obtain ⟨v0, hv0, -⟩ := (F.ex_diff i P hP).1 w
  rw [isDerivAt0_unique hv hv0, Over.w v0]
  first
  | rfl
  | simp [epsPt]

end Tan

end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Units

variable {Z Z' : Scheme.{0}}

private lemma ringHom_units_zpow_lemma {R S : Type*} [CommRing R] [Field S] (f : R →+* S) (u : Rˣ) (k : ℤ) :
    f ↑(u ^ k) = (f ↑u) ^ k := by
  have hk : ((Units.map (f : R →* S) (u ^ k) : Sˣ) : S) = ((Units.map (f : R →* S) u ^ k : Sˣ) : S) := by
    rw [map_zpow]
  rw [Units.val_zpow_eq_zpow_val] at hk
  exact hk

theorem vtf_valU (p : Sp ℂ ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, V)ˣ) (k : ℤ) :
    valAt' p V ((u ^ k : Γ(Z, V)ˣ) : Γ(Z, V)) = valAt' p V (u : Γ(Z, V)) ^ k := by
  rw [valAt', valAt', dite_eq_left h, dite_eq_left h]
  delta valAt
  exact ringHom_units_zpow_lemma ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (p.appLE V ⊤ h).hom) u k

theorem vtf_val_res (p : Sp ℂ ⟶ Z) {U V : Z.Opens} (hVU : V ≤ U) (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, U)ˣ) :
    valAt' p V (res hVU u : Γ(Z, V)) = valAt' p U (u : Γ(Z, U)) := by
  have h' : ⊤ ≤ p ⁻¹ᵁ U := h.trans (fun x hx => hVU hx)
  rw [valAt', valAt', dite_eq_left h, dite_eq_left h']
  delta valAt res
  congr 1
  first
  | (rw [Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE])
  | simp [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem vtf_val_pullU (p : Sp ℂ ⟶ Z) (f : Z ⟶ Z') (U : Z'.Opens) (u : Γ(Z', U)ˣ) :
    valAt' p (f ⁻¹ᵁ U) (pullU f U u : Γ(Z, f ⁻¹ᵁ U)) = valAt' (p ≫ f) U (u : Γ(Z', U)) := by
  by_cases hc : ⊤ ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have hc' : ⊤ ≤ (p ≫ f) ⁻¹ᵁ U := fun x hx => hc hx
    rw [valAt', valAt', dite_eq_left hc, dite_eq_left hc']
    delta valAt pullU
    congr 1
  · have hc' : ¬ ⊤ ≤ (p ≫ f) ⁻¹ᵁ U := fun h' => hc (fun x hx => h' hx)
    rw [valAt', valAt', dite_eq_right hc, dite_eq_right hc']

end Units

section Rd

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}

abbrev vtfQ (a : Over.mk x0 ⟶ A) : Over.mk x0 ⟶ Over.mk x0 ⊗ A := lift (𝟙 _) a

theorem vtfQ_snd (a : Over.mk x0 ⟶ A) : (vtfQ A a).left ≫ (snd (Over.mk x0) A).left = a.left := by
  show (lift (𝟙 _) a ≫ snd (Over.mk x0) A).left = a.left
  rw [lift_snd]

theorem vtfQ_fst (a : Over.mk x0 ⟶ A) : (vtfQ A a).left ≫ (fst (Over.mk x0) A).left = 𝟙 _ := by
  show (lift (𝟙 _) a ≫ fst (Over.mk x0) A).left = 𝟙 _
  rw [lift_fst]
  rfl

theorem vtf_pt_uniq (a : Over.mk x0 ⟶ A) (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left)
    (h1 : pt ≫ (snd (Over.mk x0) A).left = a.left) (h2 : pt ≫ (fst (Over.mk x0) A).left = 𝟙 _) :
    pt = (vtfQ A a).left := by
  have hw : pt ≫ (Over.mk x0 ⊗ A).hom = x0 := by
    rw [← Over.w (fst (Over.mk x0) A), ← Category.assoc, h2, Category.id_comp]
    rfl
  let q : Over.mk x0 ⟶ Over.mk x0 ⊗ A := Over.homMk pt hw
  have hq : q = vtfQ A a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [vtfQ, lift_fst]
      ext
      exact h2
    · simp only [vtfQ, lift_snd]
      ext
      exact h1
  exact congrArg CommaMorphism.left hq

theorem vtf_chart (k : ℤ) (a : Over.mk x0 ⟶ A) (i : Fin 1 → L.ι) (h : ⊤ ≤ a.left ⁻¹ᵁ L.U (i 0)) :
    ⊤ ≤ (vtfQ A a).left ⁻¹ᵁ (LPow A L k (Over.mk x0)).U i := by
  intro x _
  have hx : a.left.base x ∈ L.U (i 0) := h (by trivial)
  have hx' : (snd (Over.mk x0) A).left.base ((vtfQ A a).left.base x) ∈ L.U (i 0) := by
    have e : ((vtfQ A a).left ≫ (snd (Over.mk x0) A).left).base x = a.left.base x := by
      rw [vtfQ_snd]
    change ((vtfQ A a).left ≫ (snd (Over.mk x0) A).left).base x ∈ L.U (i 0)
    rw [e]
    exact hx
  refine Set.mem_iInter.mpr fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact hx'

theorem vtf_val_g {k : ℤ} (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (i i' : Fin 1 → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U i ⊓ (LPow A L k (Over.mk x0)).U i')) :
    valAt' p _ ((LPow A L k (Over.mk x0)).g i i').val =
      valAt' (p ≫ (snd (Over.mk x0) A).left) (L.U (i 0) ⊓ L.U (i' 0)) (L.g (i 0) (i' 0)).val ^ k := by
  delta LPow LB.LinComb at h ⊢
  dsimp only at h ⊢
  rw [Fin.prod_univ_one, vtf_valU p h]
  congr 1
  exact (vtf_val_res p _ h _).trans (vtf_val_pullU p (snd (Over.mk x0) A).left _ (L.g (i 0) (i' 0)))

theorem vtf_read {k : ℤ} (F : LB.Sec (LPow A L k (Over.mk x0))) (a : Over.mk x0 ⟶ A) (fr : L.ι → ℂ)
    (hfr : ∀ j j', ⊤ ≤ a.left ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j = valAt' a.left _ (L.g j j' : Γ(A.left, L.U j ⊓ L.U j')) * fr j')
    (j j' : L.ι) (hj : ⊤ ≤ a.left ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ a.left ⁻¹ᵁ L.U j') (θ : ℂ)
    (h : valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ * fr j ^ k) :
    valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j')) (F.f (fun _ => j')) = θ * fr j' ^ k := by
  have hjj : ⊤ ≤ a.left ⁻¹ᵁ (L.U j' ⊓ L.U j) := fun q hq => ⟨hj' hq, hj hq⟩
  have hp : ⊤ ≤ (vtfQ A a).left ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U (fun _ => j') ⊓
      (LPow A L k (Over.mk x0)).U (fun _ => j)) :=
    fun q hq => ⟨vtf_chart A L k a _ hj' hq, vtf_chart A L k a _ hj hq⟩
  have e := congrArg (valAt' (vtfQ A a).left _) (F.compat (fun _ => j') (fun _ => j))
  rw [valAt'_mul] at e
  have e1 : valAt' (vtfQ A a).left _ (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (inf_le_left :
      (LPow A L k (Over.mk x0)).U (fun _ => j') ⊓ (LPow A L k (Over.mk x0)).U (fun _ => j) ≤ _)).op).hom
      (F.f (fun _ => j'))) = valAt' (vtfQ A a).left _ (F.f (fun _ => j')) := by
    exact valAt'_res _ _ hp _
  have e2 : valAt' (vtfQ A a).left _ (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (inf_le_right :
      (LPow A L k (Over.mk x0)).U (fun _ => j') ⊓ (LPow A L k (Over.mk x0)).U (fun _ => j) ≤ _)).op).hom
      (F.f (fun _ => j))) = valAt' (vtfQ A a).left _ (F.f (fun _ => j)) := by
    exact valAt'_res _ _ hp _
  rw [e1, e2, vtf_val_g A L _ _ _ hp, vtfQ_snd, h] at e
  rw [e, hfr j' j hjj, mul_zpow]
  ring

theorem vtf_twist {a b : ℤ} {ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A} {m : Over.mk x0 ⊗ A ⟶ A}
    {hm : ψ ≫ snd (Over.mk x0) A = m}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b (Over.mk x0))} {s' : LB.Sec (LPow A L a (Over.mk x0))}
    (h : IsTwistPull A L ψ m hm a b α s s') (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (j : Fin 2 → L.ι)
    (hp : ⊤ ≤ p ⁻¹ᵁ LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) :
    valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0)) =
      valAt' p _ (α.s j).val *
        valAt' (p ≫ ψ.left) ((LPow A L b (Over.mk x0)).U (fun _ => j 1)) (s.f (fun _ => j 1)) := by
  calc valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0))
      = valAt' p (LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j)
          (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L m j)).op).hom
            (s'.f (fun _ => j 0))) := by
        exact (valAt'_res p (chart_le_zero A L m j) hp _).symm
    _ = valAt' p (LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j)
          ((show Γ((Over.mk x0 ⊗ A).left, LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) from (α.s j).val) *
            ((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (chart_le_pull A L ψ m hm j)).op).hom
              ((ψ.left.app _).hom (s.f (fun _ => j 1)))) := by rw [h j]
    _ = _ := by
        rw [valAt'_mul]
        refine congrArg₂ (· * ·) rfl ?_
        calc _ = valAt' p (ψ.left ⁻¹ᵁ (LPow A L b (Over.mk x0)).U (fun _ => j 1))
              ((ψ.left.app _).hom (s.f (fun _ => j 1))) := by
              exact valAt'_res p (chart_le_pull A L ψ m hm j) hp _
          _ = _ := by exact valAt'_comp p ψ.left _ _

end Rd

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

variable {g : ℕ} {Y Y' : Scheme.{0}}

theorem isHolFam_const (u : Sp ℂ ⟶ Y) : IsHolFam (g := g) (fun _ => u) := by
  intro U f
  exact ⟨isOpen_const, differentiableOn_const _⟩

def jetZero (m : ℕ) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m :=
  jetMap (fun _ => 0) fun _ => Ideal.zero_mem _

theorem jetZero_eq (m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) :
    jetZero m a = algebraMap ℂ _ ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) a) := by
  have h : (jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) =
      (Algebra.ofId ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp jetAug := by
    apply Ideal.Quotient.algHom_ext
    simp only [jetZero, jetMap, jetAug, liftJet, AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [h]
  rfl

theorem jetPt_const (u : Sp ℂ ⟶ Y) (m : ℕ) :
    spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ u = jetPt (fun _ => u) (isHolFam_const u) m := by
  have hl : IsLocalHom ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) :=
    isLocalHom_jetMap (m := m) (fun _ => 0) (fun _ => Ideal.zero_mem _)
  have h1 := jetPt_precomp (fun _ => u) (fun _ => u) (isHolFam_const u) (isHolFam_const u) rfl m
    ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m)
    (fun U _ f => by simp only [jetOf_const, AlgHom.coe_toRingHom, AlgHom.commutes])
  rw [← h1]
  have h2 : ((jetZero m : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) =
      (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) := by
    exact RingHom.ext fun a => jetZero_eq m a
  have h3 : spMap ((algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)).comp
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) =
      spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫
        spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) := by
    first
    | rfl
    | (simp only [spMap]; rw [← Spec.map_comp]; rfl)
    | (unfold spMap; rw [← Spec.map_comp]; rfl)
  rw [h2, h3, Category.assoc, jetPt_aug]

theorem jetPt_over (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (p : Y ⟶ Y') (u : Sp ℂ ⟶ Y')
    (he : ∀ z, e z ≫ p = u) (m : ℕ) :
    jetPt e hol m ≫ p = spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ u := by
  rw [jetPt_comp e hol p (fun _ => u) (isHolFam_const u) he m, ← jetPt_const u m]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
