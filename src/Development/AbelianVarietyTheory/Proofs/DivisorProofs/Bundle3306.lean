module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3222
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3175
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitModulusRationalPhaseMemCoefficientField
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3294
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3295
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep

theorem exists_ringHom_val_of_regAt' : ∀ (X₂ : GSet) (z : X₂.M.Z) {V : Type} [CommRing V] [IsDomain V] (ev : X₂.M.Z.presheaf.stalk z →+* V), RegAt X₂ z ev → ∃ yK : X₂.S.R →+* FractionRing V, ∀ a : X₂.S.R, yK a = X₂.M.val (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) a := by
  intro X₂ z V _ _ ev hr
  have hR : X₂.S.R ≤ X₂.M.O ((jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))) :=
    fun a ha => hr a ha
  exact ⟨(RatModel.valHomOf (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) _
    (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₂.M) (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))))).comp
      (Subalgebra.inclusion hR).toRingHom, fun a => rfl⟩

theorem Tower.comp_act₂_of_comp_act' : ∀ {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) (y₂ : 𝔗.X₂.S.R →+* K) (φ₂ : A'.left ⟶ 𝔗.X₂.ρ.P.A.left), φ₂ ≫ 𝔗.X₂.ρ.P.A.hom = A'.hom ≫ spMap y₂ → ∀ (e : A' ⟶ A') (a : I), e.left ≫ φ₂ ≫ 𝔗.φ = φ₂ ≫ 𝔗.φ ≫ (act a).left → e.left ≫ φ₂ = φ₂ ≫ (𝔗.act₂ a).left := by
  intro I X₁ act 𝔗 K _ A' y₂ φ₂ hφ e a h
  refine 𝔗.cart.1.hom_ext ?_ ?_
  · simp only [Category.assoc, 𝔗.act_eq a]
    simpa only [Category.assoc] using h
  · simp only [Category.assoc, Over.w (𝔗.act₂ a), hφ]
    rw [← Category.assoc, Over.w e]

theorem Tower.pt_iff_pt_gl' : ∀ {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) [GrpObj A'] (ya yb : 𝔗.X₂.S.R →+* K) (φa φb : A'.left ⟶ 𝔗.X₂.ρ.P.A.left) (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap ya) φa → IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap yb) φb → φa ≫ 𝔗.φ = φb ≫ 𝔗.φ → ya = yb.comp (𝔗.sR σ) → ∀ {L : Type} [Field L] (j : K →+* L) (x : Sp L ⟶ A'.left), x ≫ A'.hom = spMap j → ∀ a, (x ≫ φa = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ↔ x ≫ φb = spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) := by
  intro I X₁ act 𝔗 K _ A' _ ya yb φa φb σ ha hb hab hy L _ j x hx a
  have hc := 𝔗.cart.1
  have hsec : ∀ b, (𝔗.X₂.ρ.pt b).left ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ := fun b => Over.w (𝔗.X₂.ρ.pt b)
  have hsp : ∀ y : 𝔗.X₂.S.R →+* K, spMap j ≫ spMap y = spMap (j.comp y) := fun y => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hxa : (x ≫ φa) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hx, hsp]
  have hxb : (x ≫ φb) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hb.1.w, ← Category.assoc, hx, hsp]
  have hra : (spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hrb : (spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hg : spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left ≫ 𝔗.φ = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ≫ 𝔗.φ := by
    rw [𝔗.gl_pt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, ← hy]
  constructor
  · intro h1
    refine hc.hom_ext ?_ (hxb.trans hrb.symm)
    rw [Category.assoc, ← hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]
  · intro h1
    refine hc.hom_ext ?_ (hxa.trans hra.symm)
    rw [Category.assoc, hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]

theorem exists_baseChange_gMem_of_tower : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  intro I X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv
  obtain ⟨eps, heps⟩ := GlobalTheory.T.galoisTower_thetaMember_terms_baseChange X₁ act 𝔗 z₁ z₂ hz₂ x₀ hdiv
  refine ⟨eps, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab T hT V' _ _ _ io hcn hinj hfin
  have hle : nonZeroDivisors V ≤ (nonZeroDivisors V').comap io :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hinj
  let f : FractionRing V →+* FractionRing V' := IsLocalization.map (FractionRing V') io hle
  have hf : ∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v) :=
    fun v => IsLocalization.map_eq hle v
  obtain ⟨D', e₈', G', _, _, A', U', ψ, hD, bc, hsemi, hψ, hw, hbc, hPU, hxe, hgen, hE, hpsi⟩ :=
    GlobalTheory.T.exists_uniformisation_baseChange_finite_injective X₁ z₁ act V ev X t δ 𝔪 V' io f hf hcn hinj hfin
  have hreg : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → RegAt 𝔗.X₂ z₂ ev₂ :=
    fun ev₂ h => GlobalTheory.T.thetaRing_regular_at_extension_point 𝔗 hz₂ ev io ev₂ hinj h 𝔪.reg
  choose yK hyK using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    exists_ringHom_val_of_regAt' 𝔗.X₂ z₂ ev₂ (hreg ev₂ h)
  have hyKc : ∀ ev₂ h, (yK ev₂ h).comp 𝔗.om = f.comp 𝔪.yK := by
    intro ev₂ h
    ext a
    simp only [RingHom.comp_apply]
    rw [hyK, 𝔪.yK_eq]
    exact GlobalTheory.T.val_extensionPoint_eq_image_of_val 𝔗 hz₂ ev io ev₂ f hf hinj h 𝔪.reg a
  have hsq : ∀ ev₂ h, spMap (yK ev₂ h) ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK := by
    intro ev₂ h
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hyKc ev₂ h]
  choose φ₂ hφ₂ using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.isGrpPullback_paste_factorisation X₁.ρ.P.A 𝔗.X₂.ρ.P.A 𝔪.A.A A'.A (spMap 𝔗.om) (spMap 𝔪.yK) (spMap f) (spMap (yK ev₂ h)) 𝔗.φ 𝔪.φ ψ
      𝔗.cart 𝔪.cart hψ (hsq ev₂ h)
  choose wl hwl using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.exists_lineBundleIso_pullback_commSquare A'.L 𝔪.A.L X₁.ρ.P.L 𝔗.X₂.ρ.P.L ψ 𝔪.φ (φ₂ ev₂ h) 𝔗.φ A'.isLB 𝔪.A.isLB X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB
      (hφ₂ ev₂ h).2.symm hw ⟨𝔪.wl, 𝔪.wl_gen⟩ 𝔗.lb
  let 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ →
      GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ := fun ev₂ h =>
    { cn := hcn
      loc := h.1
      reg := hreg ev₂ h
      yK := yK ev₂ h
      yK_eq := hyK ev₂ h
      D := D'
      e₈ := e₈'
      G := G'
      semi := hsemi
      A := A'
      U := U'
      φ := φ₂ ev₂ h
      cart := (hφ₂ ev₂ h).1
      wl := wl ev₂ h
      wl_gen := hwl ev₂ h
      equiv := fun a => by
        obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a
        obtain ⟨E', hE'1, hE'2⟩ := hE E
        refine ⟨E', ?_, fun mu => hD.xe.injective ?_⟩
        · have e2 := (hφ₂ ev₂ h).2
          refine Tower.comp_act₂_of_comp_act' 𝔗 A'.A (yK ev₂ h) (φ₂ ev₂ h) (hφ₂ ev₂ h).1.1.w E'.aA a ?_
          calc E'.aA.left ≫ φ₂ ev₂ h ≫ 𝔗.φ = E'.aA.left ≫ ψ ≫ 𝔪.φ := by rw [e2]
            _ = ψ ≫ E.aA.left ≫ 𝔪.φ := by rw [← Category.assoc, hE'1, Category.assoc]
            _ = ψ ≫ 𝔪.φ ≫ (act a).left := by rw [hE1]
            _ = φ₂ ev₂ h ≫ 𝔗.φ ≫ (act a).left := by rw [← Category.assoc, ← e2, Category.assoc]
        · rw [hE'2, hxe, hE2, hxe]
      psi := hpsi }
  refine ⟨𝔪₂, ?_, ?_⟩
  · intro ev₂ h zt hzt
    exact heps V ev X t δ 𝔪 C lab T hT V' io f hf hinj hfin ev₂ (𝔪₂ ev₂ h) ψ hD bc h (hyKc ev₂ h) hψ hw
      (hφ₂ ev₂ h).2 hbc hPU hxe hgen zt hzt
  · intro ev₂ h ev₂' h' σ h1 h2 a mu
    have hy : yK ev₂' h' = (yK ev₂ h).comp (𝔗.sR σ) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hyK, hyK]
      exact GlobalTheory.T.val_galoisConjugate_extension_eq 𝔗 ev₂ ev₂' σ h1 h2 (hreg ev₂ h) (hreg ev₂' h') b
    unfold GMem.YY
    refine exists_congr fun p => exists_congr fun x => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact Tower.pt_iff_pt_gl' 𝔗 A'.A (yK ev₂' h') (yK ev₂ h) (φ₂ ev₂' h') (φ₂ ev₂ h) σ (hφ₂ ev₂' h').1 (hφ₂ ev₂ h).1
      ((hφ₂ ev₂' h').2.trans (hφ₂ ev₂ h).2.symm) hy
      (algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))) x.left (Over.w x) a

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.IntLabel

section
variable {G X : Type} [AddCommGroup G] [AddCommGroup X] {N : ℕ} {Y : G → (Fin 8 → X) → Prop}

theorem yy_zero (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) : Y 0 0 := by
  obtain ⟨mu, hmu⟩ := h1 0
  have h2 := h4 0 0 mu mu hmu hmu
  rw [add_zero] at h2
  have hc := (h3 0 mu (mu + mu) hmu).1 h2
  refine (h3 0 mu 0 hmu).2 fun v => ?_
  obtain ⟨w, hw⟩ := hc v
  have e : mu v = N • w := add_left_cancel (a := mu v) (by simpa using hw)
  exact ⟨-w, by simp [e]⟩

theorem yy_neg (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a : G} {mu : Fin 8 → X} (ha : Y a mu) :
    Y (-a) (-mu) := by
  obtain ⟨mu', h'⟩ := h1 (-a)
  have h0 := h4 a (-a) mu mu' ha h'
  rw [add_neg_cancel] at h0
  have hc := (h3 0 0 (mu + mu') (yy_zero h1 h3 h4)).1 h0
  refine (h3 (-a) mu' (-mu) h').2 fun v => ?_
  obtain ⟨w, hw⟩ := hc v
  simp only [Pi.add_apply, Pi.zero_apply, zero_add] at hw
  refine ⟨-w, ?_⟩
  simp only [Pi.neg_apply, smul_neg]
  rw [← hw]
  abel

theorem yy_sub (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a b : G} {mu nu : Fin 8 → X} (ha : Y a mu)
    (hb : Y b nu) : Y (a - b) (mu - nu) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h4 _ _ _ _ ha (yy_neg h1 h3 h4 hb)

theorem yy_nsmul (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (k : ℕ) {a : G} {mu : Fin 8 → X} (ha : Y a mu) :
    Y (k • a) (k • mu) := by
  induction k with
  | zero => simpa using yy_zero h1 h3 h4
  | succ k ih => rw [succ_nsmul, succ_nsmul]; exact h4 _ _ _ _ ih ha

theorem mem_closure_iff (p J : ℕ) (hJ : 2 ≤ J) (hN : N = p ^ J) (hG : ∀ a : G, N • a = 0)
    (htor : ∀ b : G, p • b = 0 → ∃ c, b = p ^ (J - 1) • c) (htf : ∀ x : X, p ^ (J - 1) • x = 0 → x = 0)
    (h1 : ∀ a, ∃ mu, Y a mu) (h2 : ∀ mu, ∃ a, Y a mu)
    (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (S : Set G) (hS : ∀ a ∈ S, Y a 0)
    (hT : ∀ a, Y a 0 → ∃ b, p • b = 0 ∧ a + b ∈ S) (a : G) : a ∈ AddSubgroup.closure S ↔ Y a 0 := by
  constructor
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem x hx => exact hS x hx
    | zero => exact yy_zero h1 h3 h4
    | add x y _ _ hx hy => simpa using h4 x y 0 0 hx hy
    | neg x _ hx => simpa using yy_neg h1 h3 h4 hx
  · intro ha
    obtain ⟨b, hb, hab⟩ := hT a ha
    have hYb : Y b 0 := by simpa using yy_sub h1 h3 h4 (hS _ hab) ha
    obtain ⟨c, rfl⟩ := htor b hb
    obtain ⟨muc, hc⟩ := h1 c
    have hcong := (h3 _ _ _ (yy_nsmul h1 h3 h4 (p ^ (J - 1)) hc)).1 hYb
    have hw : ∀ v, ∃ w : X, muc v = p • w := by
      intro v
      obtain ⟨w, hw⟩ := hcong v
      simp only [Pi.zero_apply, Pi.smul_apply] at hw
      refine ⟨-w, ?_⟩
      have e : p ^ (J - 1) • (muc v + p • w) = 0 := by
        rw [smul_add, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN]
        exact hw.symm
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      exact htf _ e
    choose w hw using hw
    have hmu : muc = p • w := funext fun v => by simp [hw v]
    obtain ⟨c', hc'⟩ := h2 w
    have hk : Y (c - p • c') 0 := by
      have := yy_sub h1 h3 h4 hc (yy_nsmul h1 h3 h4 p hc')
      rwa [← hmu, sub_self] at this
    obtain ⟨bk, hbk, hkS⟩ := hT _ hk
    have hbk0 : p ^ (J - 1) • bk = 0 := by
      obtain ⟨e, he⟩ : ∃ e, J - 1 = e + 1 := ⟨J - 2, by omega⟩
      rw [he, pow_succ, mul_smul, hbk, smul_zero]
    have key : p ^ (J - 1) • c = p ^ (J - 1) • ((c - p • c') + bk) := by
      rw [smul_add, hbk0, add_zero, smul_sub, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN, hG, sub_zero]
    have hbcl : p ^ (J - 1) • c ∈ AddSubgroup.closure S := by
      rw [key]; exact nsmul_mem (AddSubgroup.subset_closure hkS) _
    have e : a = (a + p ^ (J - 1) • c) - p ^ (J - 1) • c := by abel
    rw [e]
    exact sub_mem (AddSubgroup.subset_closure hab) hbcl

theorem zmod_tors {p J M : ℕ} (hp : 0 < p) (hJ : 1 ≤ J) (hM : M = p ^ J) (x : ZMod M) (hx : p • x = 0) :
    ∃ y : ZMod M, x = p ^ (J - 1) • y := by
  subst hM
  haveI : NeZero (p ^ J) := ⟨pow_ne_zero _ hp.ne'⟩
  have h1 : p ^ J ∣ p * x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (p ^ J)) (p ^ J)]
    push_cast
    rw [ZMod.natCast_zmod_val]
    rwa [nsmul_eq_mul] at hx
  have h2 : p ^ (J - 1) ∣ x.val := by
    have e : p ^ J = p * p ^ (J - 1) := by rw [← pow_succ']; congr 1; omega
    have h1' : p * p ^ (J - 1) ∣ p * x.val := by rw [← e]; exact h1
    exact Nat.dvd_of_mul_dvd_mul_left hp h1'
  obtain ⟨q, hq⟩ := h2
  refine ⟨(q : ZMod (p ^ J)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [hq, nsmul_eq_mul]
  push_cast
  ring

end
end GlobalTheory.Poinc.Sep.IntLabel

namespace GlobalTheory.Poinc.Sep


open GlobalTheory.Poinc.Sep.IntLabel in
theorem mem_HH_iff_yy_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ ↔ 𝔪.YY a 0 := by
  intro g n F W Z i X₁ z₁ act x₀ hx₀ V _ _ _ ev X _ m t δ 𝔪 a
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨j, hj, hr⟩ := X₁.ρ.r_eq
  have hp : 0 < X₁.ρ.n := X₁.ρ.n_prime.pos
  have hk := X₁.ρ.two_le
  have hN : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j + X₁.ρ.k * 2) := by rw [hr, X₁.ρ.N_eq, pow_add, pow_mul]
  have hJ : 2 ≤ j + X₁.ρ.k * 2 := by omega
  have hG : ∀ b : X₁.S.Gam, (X₁.S.r * X₁.S.N) • b = 0 := fun b => by
    funext v
    simp [nsmul_eq_mul]
  have htor : ∀ b : X₁.S.Gam, X₁.ρ.n • b = 0 → ∃ c : X₁.S.Gam, b = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • c := by
    intro b hb
    have hv : ∀ v, ∃ y : ZMod (X₁.S.r * X₁.S.N), b v = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • y := fun v =>
      zmod_tors hp (by omega) hN (b v) (by simpa using congrFun hb v)
    choose c hc using hv
    exact ⟨c, funext fun v => by simpa using hc v⟩
  have htf : ∀ x : X, X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • x = 0 → x = 0 := by
    intro x hx
    have hq : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) ≠ 0 := pow_ne_zero _ hp.ne'
    have hs : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • (Pi.single 0 x : Fin 8 → X) = 0 := by
      funext v
      by_cases hv : v = 0
      · subst hv; simp [hx]
      · simp [Pi.single_apply, hv]
    have he : ((X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) : ℕ) : ℤ) • 𝔪.e₈ (Pi.single 0 x) = 0 := by
      rw [natCast_zsmul, ← map_nsmul, hs, map_zero]
    have h0 : 𝔪.e₈ (Pi.single 0 x) = 0 := (smul_eq_zero.1 he).resolve_left (by exact_mod_cast hq)
    have h0' : (Pi.single 0 x : Fin 8 → X) = 0 := 𝔪.e₈.injective (h0.trans (map_zero _).symm)
    simpa using congrFun h0' 0
  rw [ThetaSys.HH]
  exact mem_closure_iff (X₁.ρ.n) (j + X₁.ρ.k * 2) hJ hN hG htor htf h1 h2 h3 h4 _
    (fun b hb => GlobalTheory.T.thetaLabel_class_zero_of_divides_all_thetaConstants g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 b hb)
    (fun b hb => GlobalTheory.T.exists_torsionTranslate_label_thetaConstant_divides_all g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hx₀ b hb) a

end GlobalTheory.Poinc.Sep
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unit_modulus_rational_phase_mem_coefficient_field : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (t : D.ntw.Tw) (j : Fin D.R.m)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RatHyp T Rl F κ v₀ O t j hV →
  ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
  ∀ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) →
  (∀ k, Rl.phs k = 1) → T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ →
  ∀ ph : ℂ, ‖ph‖ = 1 → IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph → ∃ c : D.what₂.LL, sg0 D A3.A c = ph := by
  first | exact @GlobalTheory.PhaseOneOnto.phase_mem_coefField | exact GlobalTheory.PhaseOneOnto.phase_mem_coefField | (intros; apply GlobalTheory.PhaseOneOnto.phase_mem_coefField <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.raynaud_lineBundle_relAmple_of_generic_semiAbelian : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ L : LB G.left, L.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → IsAmpleLB L := by
  first | exact @GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic | exact GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic | (intros; apply GlobalTheory.AmpleGenericSemiAb.isAmpleLB_of_generic <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.TowerVA

theorem exists_compatible_of_lift (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (N : ∀ e, LB (Y e).left) (hN : ∀ e, (N e).IsLB) (p k c : ℕ) (hk : 1 ≤ k) (hc : (c : ℤ) = (p : ℤ) * (k : ℤ))
    (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N 0) p))
    (hs : VeryAmpleBy (Y 0).hom (GlobalTheory.AbLaw.pw (N 0) p) s)
    (hlift : ∀ (L : ∀ e, LB (Y e).left) (u : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))),
      (∀ e, (L e).IsLB ∧ (u e).IsGen) → LBIso (L 0) (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k) →
        ∀ σ₀ : LB.Sec (L 0), ∃ σ : ∀ e, LB.Sec (L e), σ 0 = σ₀ ∧ ∀ e, Rel (β e) (u e) (σ (e + 1)) (σ e))
    (v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e))) (hv : ∀ e, (v e).IsGen) :
    ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)),
      (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  have hEq : GlobalTheory.AbLaw.pw (N 0) c = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k := by
    rw [hc]
    exact congrArg (fun g => (⟨(N 0).ι, (N 0).U, g⟩ : LB (Y 0).left))
      (funext fun i => funext fun j => zpow_mul ((N 0).g i j) _ _)
  have h0 : ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N 0) c)),
      VeryAmpleBy (Y 0).hom (GlobalTheory.AbLaw.pw (N 0) c) s' := by
    rw [hEq]
    exact GlobalTheory.AbLaw.veryAmpleBy_pw _ _ _ _ n s (isLB_pw (hN 0) _) hs k hk
  obtain ⟨n', s0, hs0⟩ := h0
  have hL : ∀ e, (GlobalTheory.AbLaw.pw (N e) c).IsLB ∧ (v e).IsGen := fun e => ⟨isLB_pw (hN e) _, hv e⟩
  have hiso : LBIso (GlobalTheory.AbLaw.pw (N 0) c) (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw (N 0) p) k) :=
    hEq ▸ lbIso_refl (isLB_pw (hN 0) _)
  choose σ hσ0 hσ using fun j => hlift (fun e => GlobalTheory.AbLaw.pw (N e) c) v hL hiso (s0 j)
  refine ⟨n', fun e j => σ j e, fun e j => hσ j e, ?_⟩
  rintro (_ | e)
  · show VeryAmpleBy _ _ (fun j => σ j 0)
    simp only [hσ0]
    exact hs0
  · obtain ⟨j₀, hj, w, hw, hr⟩ := tower I Y β hβ (fun e => GlobalTheory.AbLaw.pw (N e) c) v hL (fun e j => σ j e)
      (fun e j => hσ j e) e
    simp only [hσ0] at hr
    exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
      (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _) _ _ _ _ j₀ hj _ _ w n' _ _ (hL _).1 (hL _).1
      ((isGen_iff _).2 hw) hr hs0

theorem exists_veryAmple_compatible : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → RelAmple (Y 0) (N 0) → ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ, c = a ∨ c = a + 1 → ∀ v : ∀ e, LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)), (∀ e, (v e).IsGen) → ∃ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw (N e) c)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) ∧ ∀ e, VeryAmpleBy (Y e).hom (GlobalTheory.AbLaw.pw (N e) c) (s e) := by
  intro R _ _ I Y β hβ N hN hamp
  obtain ⟨d, hd1, hd⟩ := GlobalTheory.T.exists_consecutive_veryAmple_powers_relAmple (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0) hamp
  obtain ⟨n₁, s₁, hs₁⟩ := hd d (Or.inl rfl)
  obtain ⟨n₂, s₂, hs₂⟩ := hd (d + 1) (Or.inr rfl)
  obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.exists_uniform_lift_sections_thickeningTower R I Y β hβ _ n₁ s₁ (isLB_pw (hN 0) _) hs₁
  obtain ⟨k₂, hk₂⟩ := GlobalTheory.T.exists_uniform_lift_sections_thickeningTower R I Y β hβ _ n₂ s₂ (isLB_pw (hN 0) _) hs₂
  refine ⟨d * (1 + (d + 1) * max k₁ k₂), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  have ht1 : ∀ m t : ℕ, 1 ≤ m → t ≤ 1 + m * t := fun m t hm => by nlinarith
  rintro c (rfl | rfl) v hv
  · exact exists_compatible_of_lift R I Y β hβ N hN d (1 + (d + 1) * max k₁ k₂) _ (by omega) (by push_cast; ring)
      n₁ s₁ hs₁ (hk₁ _ (le_trans (le_max_left _ _) (ht1 _ _ (by omega)))) v hv
  · exact exists_compatible_of_lift R I Y β hβ N hN (d + 1) (1 + d * max k₁ k₂) _ (by omega) (by push_cast; ring)
      n₂ s₂ hs₂ (hk₂ _ (le_trans (le_max_right _ _) (ht1 _ _ hd1))) v hv

end GlobalTheory.FormalAlg.TowerVA
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.verticalSymbol_zero_of_bracket_preserving : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Λᵀ = Λ → (∀ r, δ₀ ((algebraMap Ω (FractionRing Ω)) (φ r)) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ b c : FractionRing Ω, GlobalTheory.HeatSym.VS φ t.PP.L x' g k b → GlobalTheory.HeatSym.VS φ t.PP.L x' g k c → GlobalTheory.HeatSym.VS φ t.PP.L x' g (3 * k) ((k : FractionRing Ω) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b))) → Λ = 0 := by
  first | exact @GlobalTheory.HeatSym.vertical_symbol_zero | exact GlobalTheory.HeatSym.vertical_symbol_zero | (intros; apply GlobalTheory.HeatSym.vertical_symbol_zero <;> assumption)
end
