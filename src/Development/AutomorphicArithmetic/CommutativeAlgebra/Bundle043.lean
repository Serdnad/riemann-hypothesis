module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle019
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle011
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem mDR_alg_eq_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] (w : DR k K) :
    (semiHom_algebraMap k K L).mDR w = GlobalTheory.W1.mapDR k K L w := by
  induction w using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [SemiHom.mDR_algebraMap, AlgHom.commutes]
    rfl
  | ι x =>
    have h1 := SemiHom.mDR_ι (semiHom_algebraMap k K L) x
    simp only [ι1] at h1
    rw [h1, SemiHom.oneFormMap_eq_kaehlerDifferential_map _ (fun _ => rfl)]
    simp only [GlobalTheory.W1.mapDR, ExteriorAlgebra.lift_ι_apply, GlobalTheory.W1.map1, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, ι1]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

private theorem mDR_square {k B B' K L : Type} [Field k] [Field K] [Field L] [CommRing B] [CommRing B']
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Algebra k B] [Algebra k B']
    {α : B →+* K} {β : B →+* B'} {γ : B' →+* L} (hα : SemiHom (RingHom.id k) α)
    (hβ : SemiHom (RingHom.id k) β) (hγ : SemiHom (RingHom.id k) γ)
    (h : ∀ b, γ (β b) = algebraMap K L (α b)) {j : ℕ} (x : Om k B j) :
    hγ.mDR (hβ.mDR (x : DR k B)) = GlobalTheory.W1.mapDR k K L (hα.mDR (x : DR k B)) := by
  rw [← SemiHom.coe_mOm hβ, ← SemiHom.coe_mOm hγ, ← mDR_alg_eq_mapDR, ← SemiHom.coe_mOm hα,
    ← SemiHom.coe_mOm (semiHom_algebraMap k K L),
    SemiHom.mOm_mOm hβ hγ (hβ.comp hγ) (fun _ => rfl),
    SemiHom.mOm_mOm hα (semiHom_algebraMap k K L) (hβ.comp hγ) (fun b => (h b).symm)]

private theorem formGerm_toOm {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Sp k) (j : ℕ)
    {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) (x : OmU s V j) :
    letI := algΓ s; letI := ffAlg s
    formGerm s j hV hη (toOm s j V x) = (semiHom_germSec s hη).mDR (x : DR k (Sec s V)) := by
  letI := algΓ s; letI := ffAlg s
  change (semiHom_germSec s hη).mDR (((toOmEquiv s j hV).symm (toOm s j V x) : OmU s V j) : DR k (Sec s V)) = _
  rw [← toOmEquiv_apply s j hV, LinearEquiv.symm_apply_apply]

theorem UpperTheory.functionField_of_finite_etale_cover :
    ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p'), (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) → FiniteDimensional Z.functionField Y.functionField → ∀ (a : ℕ) (V : Z.Opens) (hV : IsAffineOpen V) (hη : genericPoint Z ∈ V) (hη' : genericPoint Y ∈ c ⁻¹ᵁ V) (y : Γ(Omega p' a, c ⁻¹ᵁ V)), letI := algΓ p; letI := algΓ p'; formGermI p a hV hη hinst ((omegaTrace hc a).app V y) = GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField (formGermI p' a (hV.preimage c) hη' hinst' y) := by
  intro Z Y _ _ p p' c hc _ _ inst inst' _ _ hinst hinst' hg hfd a V hV hη hη' y
  subst hinst hinst'
  letI := ffAlg p; letI := ffAlg p'
  haveI : CharZero Z.functionField := charZero_of_injective_algebraMap (algebraMap ℂ Z.functionField).injective
  haveI : Algebra.IsSeparable Z.functionField Y.functionField := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hT := UpperTheory.exists_deRhamTrace_of_separable ℂ Z.functionField Y.functionField
  have hspec : GlobalTheory.W1.IsTrDR ℂ Z.functionField Y.functionField (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField) := by
    unfold GlobalTheory.W1.trDR; rw [dite_eq_left hT]; exact hT.choose_spec
  obtain ⟨z, rfl⟩ := toOm_surjective (s := p') (j := a) (hV.preimage c) y
  change formGerm p a hV hη _ = GlobalTheory.W1.trDR ℂ _ _ (formGerm p' a (hV.preimage c) hη' _)
  rw [omegaTrace_app_toOm hc a hV, formGerm_toOm, formGerm_toOm]
  refine formOm_induction (P := fun z ↦ (semiHom_germSec p hη).mDR
      ((formTraceU hc hV a z : OmU p V a) : DR ℂ (Sec p V)) =
    GlobalTheory.W1.trDR ℂ _ _ ((semiHom_germSec p' hη').mDR (z : DR ℂ (Sec p' (c ⁻¹ᵁ V))))) hc hV ?_ ?_ ?_ z
  · simp only [map_zero, ZeroMemClass.coe_zero]
  · intro y z hy hz
    simp only [map_add (f := _), Submodule.coe_add, hy, hz]
  · intro b' x
    have e : ((formPull hc V a x : OmU p' (c ⁻¹ᵁ V) a) : DR ℂ (Sec p' (c ⁻¹ᵁ V))) =
        (semiHom_appSec hc V).mDR (x : DR ℂ (Sec p V)) := SemiHom.coe_mOm _ x
    rw [formTraceU_smul_formPull, Submodule.coe_smul, Submodule.coe_smul, SemiHom.mDR_smul,
      SemiHom.mDR_smul, e, mDR_square (semiHom_germSec p hη) (semiHom_appSec hc V)
        (semiHom_germSec p' hη') (fun b ↦ hg V hη hη' b), hspec]
    exact congrArg (· • _) (UpperTheory.Cb.germ_comap_eq_algebraMap_germ_of_finite_etale Z Y p p' c hc hg V hV hη hη' b')
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

theorem UpperTheory.complexPoint_eval_pullback_section :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) (h : c ≫ s = s') (V : Z.Opens) (f : Γ(Z, V)) (y : CxPts s' (RingHom.id ℂ)), y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c ⁻¹ᵁ V) → CxPts.ev s' (RingHom.id ℂ) (c ⁻¹ᵁ V) ((c.app V).hom f) y = CxPts.ev s (RingHom.id ℂ) V f (UpperTheory.A.zpt c h y) := by
  intro Z Y s s' c h V f y _
  exact (GlobalTheory.Points.valR_comp y.1 c V f).symm
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.TopForm ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi in
private theorem germ_algX {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (V : X.Opens) (hg : genericPoint X ∈ V) (a : ℂ) :
    (X.presheaf.germ V (genericPoint X) hg).hom (algX p V a) = @algebraMap ℂ X.functionField _ _ (ffAlg p) a := by
  have h := congrArg (fun φ => φ a) (GlobalTheory.TopForm.resG_comp_algX p (le_top : V ≤ ⊤))
  simp only [RingHom.comp_apply] at h
  rw [← h]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, TopCat.Presheaf.germ_res_apply]
  simp only [algX, GlobalTheory.PD.ffAlg, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Scheme.Hom.appLE]
  simp only [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  rfl

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue in
theorem UpperTheory.complexPoints_bijective_algHom_affineOpen :
    ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (V : X.Opens), IsAffineOpen V → ∀ (hg : genericPoint X ∈ V) (B : Subalgebra ℂ X.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y) → (∀ e : B →ₐ[ℂ] ℂ, ∃! y : CxPts p (RingHom.id ℂ), UpperTheory.A.Mt p V hg B e y) ∧ (∀ y ∈ CxPts.ptsIn p (RingHom.id ℂ) V, ∃! e : B →ₐ[ℂ] ℂ, UpperTheory.A.Mt p V hg B e y) := by
  intro X _ p inst hinst V hV hg B hB
  subst hinst
  set g := (X.presheaf.germ V (genericPoint X) hg).hom with hgdef
  have ginj : Function.Injective g := germ_injective_of_isIntegral X (genericPoint X) hg
  have gB : ∀ f, g f ∈ B := fun f => (hB _).2 ⟨f, rfl⟩
  let gr : Γ(X, V) →+* B := g.codRestrict B gB
  have grbij : Function.Bijective gr := by
    refine ⟨fun x y hxy => ginj (congrArg Subtype.val hxy), fun b => ?_⟩
    obtain ⟨f, hf⟩ := (hB b.1).1 b.2
    exact ⟨f, Subtype.ext hf⟩
  let eqv : Γ(X, V) ≃+* B := RingEquiv.ofBijective gr grbij
  have eqv_apply : ∀ f, eqv f = ⟨g f, gB f⟩ := fun f => rfl
  have alg_eq : ∀ a : ℂ, (algebraMap ℂ B a) = eqv (algX p V a) := by
    intro a
    apply Subtype.ext
    rw [eqv_apply]
    exact (germ_algX p V hg a).symm
  constructor
  · intro e
    let φ : Γ(X, V) →+* ℂ := (e : B →+* ℂ).comp (eqv : Γ(X, V) →+* B)
    have hφ : ∀ a : ℂ, φ (algX p V a) = RingHom.id ℂ a := by
      intro a
      change e (eqv (algX p V a)) = a
      rw [← alg_eq]
      exact e.commutes a
    refine ⟨CxPts.ofHom hV φ hφ, ⟨CxPts.ofHom_mem hV φ hφ, fun f hf => ?_⟩, ?_⟩
    · rw [CxPts.ev_ofHom]
      rfl
    · rintro y ⟨hy, hye⟩
      apply Subtype.ext
      apply GlobalTheory.Points.ext_of_valR hV hy (CxPts.ofHom_mem hV φ hφ)
      intro f
      change CxPts.ev p (RingHom.id ℂ) V f y = CxPts.ev p (RingHom.id ℂ) V f (CxPts.ofHom hV φ hφ)
      rw [CxPts.ev_ofHom, ← hye f (gB f)]
      rfl
  · intro y hy
    let e0 : B →+* ℂ := (CxPts.evHom hy).comp (eqv.symm : B →+* Γ(X, V))
    have he0 : ∀ a : ℂ, e0 (algebraMap ℂ B a) = algebraMap ℂ ℂ a := by
      intro a
      change CxPts.evHom hy (eqv.symm (algebraMap ℂ B a)) = a
      rw [alg_eq, RingEquiv.symm_apply_apply, ← CxPts.ev_eq hy, CxPts.ev_algX hy]
      rfl
    let e : B →ₐ[ℂ] ℂ := { e0 with commutes' := he0 }
    refine ⟨e, ⟨hy, fun f hf => ?_⟩, ?_⟩
    · change CxPts.evHom hy (eqv.symm ⟨g f, hf⟩) = _
      rw [show (⟨g f, hf⟩ : B) = eqv f from rfl, RingEquiv.symm_apply_apply, CxPts.ev_eq hy]
    · rintro e' ⟨_, he'⟩
      apply AlgHom.ext
      intro b
      obtain ⟨f, hf⟩ := (hB b.1).1 b.2
      have hb : b = ⟨g f, gB f⟩ := Subtype.ext hf.symm
      subst hb
      rw [he' f (gB f)]
      change _ = CxPts.evHom hy (eqv.symm (eqv f))
      rw [RingEquiv.symm_apply_apply, CxPts.ev_eq hy]
end
