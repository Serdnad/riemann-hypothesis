module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle018
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.TestBundle

open GlobalTheory.CechPic

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (P : Over (Spec (CommRingCat.of V))) [Smooth P.hom] [GeometricallyConnected P.hom]
    (e : Spec (CommRingCat.of V) ⟶ P.left) (he : e ≫ P.hom = 𝟙 _) {L M : LB P.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : CechPic.pull (pullback.fst P.hom (jK V)) (cls L hL) =
      CechPic.pull (pullback.fst P.hom (jK V)) (cls M hM)) : LBIso L M := by
  have hN := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
  have h₂ : Flat (jK V) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors V))
  refine GenericExtend.exists_isGen_of_densePart _ _ (jK V) ((isNormalScheme_iff_pred _).1 inferInstance) h₁ h₂
    DVR.isDominant_jK inferInstance P e (LB.div M L) he ‹_› (geometricallyIntegral_of_smooth P.hom) hN
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hN _)) ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  rw [cls_pull hN, cls_div hM hL, map_sub, h, sub_self]

theorem lbIso_pull_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK _ F ψ ⟨_, h₁, _, h₂⟩
  have := u.semi.smooth
  have := u.semi.geomConnected
  have hL := Q.L.isLB
  have hP := ρ.P.isLB
  have hA := u.A.isLB
  have hG := u.U.LG.isLB
  refine lbIso_of_generic u.G (eSec u.G) (Over.w η[u.G]) (pull_isLB hL F) hG ?_
  have a : CechPic.pull Q.φ (cls _ hL) = CechPic.pull (pullback.fst ρ.P.A.hom Q.u₀) (cls _ hP) :=
    (cls_eq_iff (pull_isLB hL _) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
  have b : cls _ hA = CechPic.pull u.φ (cls _ hP) := (cls_eq_iff hA (pull_isLB hP _)).2 u.lb
  have c : CechPic.pull u.U.gen.hom.left (cls _ hA) = CechPic.pull (pullback.fst u.G.hom (jK u.V)) (cls _ hG) :=
    (cls_eq_iff (pull_isLB hA _) (pull_isLB hG _)).2 u.U.ext
  refine Eq.trans ?_ c
  rw [cls_pull hL, ← pull_comp, ← h₂, pull_comp, a, ← pull_comp, h₁, b]
  exact pull_comp _ _ _

end GlobalTheory.ZH.TestBundle
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_psi_ratio {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (ψ : TauTwist.PsiFam D)
    (hψ : ∀ χ, (ψ χ).IsGen) (χ : D.X) : ∃ u : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
      val (D.psi χ) (𝟙 _) z J = TauTwist.unitAt (A := FractionRing R) (Z := (TK R).left) (𝟙 _) z u * val (ψ χ) (𝟙 _) z J :=
  TauTwist.exists_ratio (F := FractionRing R) D.P.isLB (fun _ _ _ => rfl) (D.psi_gen χ) (hψ χ)

theorem unitAt_genMap {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (z : (TK K).left) (v : (FractionRing K₁)ˣ) :
    TauTwist.unitAt (A := FractionRing K₁) (genMap β.injective) z v =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom v) :=
  (congrArg (fun r => TauTwist.unitAt (A := FractionRing K₁) r z v) (Category.id_comp _).symm).trans
    (TauTwist.unitAt_spMap (𝟙 _) (fracMap β.injective) z v)

theorem exists_isPullDeg_rescale {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (D₁ : DegPre K₁) (D : DegPre K)
    (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ))
    (q : D₁.X → (FractionRing K₁)ˣ)
    (hq : ∀ χ (z : (TK K).left) J, Good D.P.L z J → val (D.psi χ) (𝟙 _) z J =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ))) *
        val (ψ χ) (𝟙 _) z J) :
    ∃ hD : IsPullDeg β (TauTwist.rescale D₁ q) D, proj hD = proj h := by
  have key : ∀ (x : D.X) (z : (TK K).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val ((TauTwist.rescale D₁ q).psi (h.xe x)) (genMap β.injective) z J =
        (om h.w z J J' (D.xK x))⁻¹ * val (D.psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    have e := psi_val (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h (genMap β.injective) (𝟙 _) (fracMap_sq β.injective) hJ hJ' x
    rw [Category.id_comp] at e
    refine (TauTwist.val_psi_rescale q (h.xe x) _ hJ).trans ((congrArg₂ (· * ·) (unitAt_genMap β z _) e).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) rfl (hq x z J' hJ')).symm
  obtain ⟨hD, hp, -, -⟩ := exists_isPullDeg_of_val β (TauTwist.rescale D₁ q) D (Φ := proj (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h)
    (pull_grp (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.w
    ((isGen_iff h.w).1 h.w_gen) (pmaps_rig (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.xe h.c_pr key
  exact ⟨hD, hp⟩

theorem exists_ratio_descends (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) :
    ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁)
      (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) →
      ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D),
        PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  choose u hu using exists_psi_ratio D ψ hψ
  refine ⟨fun χ => FractionRing.algEquiv K K (u χ).val, fun K₁ _ β D₁ h ha => ?_⟩
  choose a₁ ha₁ using ha
  have key : ∀ χ, fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ χ)) = (u χ).val := fun χ => by
    rw [fracMap_algebraMap, ha₁]
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  have hne : ∀ χ, algebraMap K₁ (FractionRing K₁) (a₁ χ) ≠ 0 := fun χ e => (u χ).ne_zero (by
    rw [← key, e, map_zero])
  obtain ⟨q, hq⟩ : ∃ q : D₁.X → (FractionRing K₁)ˣ,
      ∀ χ, Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ)) = u χ :=
    ⟨fun y => Units.mk0 _ (hne (h.xe.symm y)), fun χ => Units.ext (by
      show fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ (h.xe.symm (h.xe χ)))) = _
      rw [AddEquiv.symm_apply_apply, key])⟩
  obtain ⟨hD, hp⟩ := exists_isPullDeg_rescale β D₁ D ψ hψ h q fun χ z J hJ => by
    rw [hq]; exact hu χ z J hJ
  exact ⟨_, _, hD, hp⟩

end GlobalTheory.FieldPull
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_uniformised_model' : GlobalTheory.Published.SemistableReductionSt → ThmUSt → PolBaseChangeSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), ∃ u : ρ.UTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  first | exact @GlobalTheory.exists_uniformised_model | exact GlobalTheory.exists_uniformised_model | (intros; apply GlobalTheory.exists_uniformised_model <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.ThetaExt

open TopologicalSpace

noncomputable def invMul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (c : Γ(X, ⊤)ˣ) : LB.Iso B A :=
  ⟨fun p => res (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) c *
    (res (fun _ hy => ⟨hy.2, hy.1⟩ : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹⟩

theorem gm_invMul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (c : Γ(X, ⊤)ˣ) (y : X) (a : A.ι) (b : B.ι)
    (ha : y ∈ A.U a) (hb : y ∈ B.U b) : gm (𝟙 X) y (A.U a ⊓ B.U b) ((invMul w c).s (a, b)) =
      gm (𝟙 X) y ⊤ c * (gm (𝟙 X) y (B.U b ⊓ A.U a) (w.s (b, a)))⁻¹ :=
  have hp : (𝟙 X : X ⟶ X) y ∈ A.U a ⊓ B.U b := ⟨ha, hb⟩
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))

theorem isGen_invMul {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (c : Γ(X, ⊤)ˣ) :
    (invMul w c).IsGen := by
  rintro ⟨a, b⟩ ⟨a', b'⟩
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a') := ⟨⟨hy.1.2, hy.1.1⟩, hy.2.2, hy.2.1⟩
  have e := congrArg (gm (𝟙 X) y (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))) (hw (b, a) (b', a'))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (b, a) (b', a') hm) (gm_res _ y _ hm _))))
  have alg : ∀ {a b t s u : (X.presheaf.stalk y)ˣ}, u = b * a⁻¹ * s → t * u⁻¹ = a * b⁻¹ * (t * s⁻¹) := by
    rintro a b t s _ rfl
    rw [mul_inv, mul_inv, inv_inv, mul_comm a, mul_left_comm]
  exact ((gm_res _ y _ hy _).trans (gm_invMul w c y a b hy.1.1 hy.1.2)).trans ((alg e').trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y (a, b) (a', b') hy)
      ((gm_res _ y _ hy _).trans (gm_invMul w c y a' b' hy.2.1 hy.2.2)))).symm)

variable {C : Core} (T : C.Theta) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

theorem isClosed_closedPoint : IsClosed ({τ.y₀ (IsLocalRing.closedPoint τ.V)} : Set C.Z) := by
  have := τ.j_loc
  have h : spMap τ.j (cPt p) = IsLocalRing.closedPoint τ.V := IsLocalRing.comap_closedPoint τ.j
  have e : y (cPt p) = τ.y₀ (IsLocalRing.closedPoint τ.V) := by
    rw [← h]
    exact (congrArg (fun g => g (cPt p)) τ.fac).symm
  rw [← e]
  exact GlobalTheory.ZH.isClosed_singleton_cPt y

theorem exists_mem_basicOpen [IsIntegral τ.H.left] [Nonempty (pullback τ.H.hom (Out.jK τ.V) :)]
    [IsOpenImmersion (pullback.fst τ.H.hom (Out.jK τ.V))] (h : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) :
    ∃ (x : (pullback τ.H.hom (Out.jK τ.V) :)) (k : T.L.L.ι), τ.φ x ∈ C.A.left.basicOpen (T.θ.f k) := by
  obtain ⟨x₀, hx₀, e₀⟩ := T.s_ne _ (isClosed_closedPoint τ)
  obtain ⟨x₁, e₁, -⟩ := Scheme.exists_preimage_of_isPullback h x₀ _ e₀
  obtain ⟨_, hx₂, x₂, rfl⟩ := nonempty_preirreducible_inter (τ.f ⁻¹ᵁ Out.nonzeroLocus T.s).isOpen
    (pullback.fst τ.H.hom (Out.jK τ.V)).isOpenEmbedding.isOpen_range ⟨x₁, show τ.f x₁ ∈ _ by rw [e₁]; exact hx₀⟩
    (Set.range_nonempty _)
  have e₂ : C.a (τ.φ x₂) = τ.f (pullback.fst τ.H.hom (Out.jK τ.V) x₂) := congrArg (fun g => g x₂) τ.φ_f
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show C.a (τ.φ x₂) ∈ Out.nonzeroLocus T.s by rw [e₂]; exact hx₂)
  have hi' := C.G.toScheme.basicOpen_le _ hi
  obtain ⟨k, hk⟩ := exists_chart T.L.isLB ((mulN C.A T.m).left (τ.φ x₂))
  have u := (SecPullIso.isUnit_gs_iff C.a _ hi' _).2 hi
  rw [T.w_sec _ i k hi' hk] at u
  have u' := (SecPullIso.isUnit_gs_iff _ _ hk _).1 (isUnit_of_mul_isUnit_right u)
  obtain ⟨x₃, e₃, -⟩ := Scheme.exists_preimage_of_isPullback τ.φ_cart.1 ((mulN C.A T.m).left (τ.φ x₂))
    (((Over.pullback (Out.jK τ.V)).obj τ.H).hom x₂)
    ((congrArg (fun g => g (τ.φ x₂)) (Over.w (mulN C.A T.m))).trans (congrArg (fun g => g x₂) τ.φ_cart.1.w))
  exact ⟨x₃, k, by rw [← e₃] at u'; exact u'⟩

end GlobalTheory.ZJ.ThetaExt

namespace GlobalTheory.ZJ

open ThetaExt TopologicalSpace

theorem Core.Theta.nonempty_ext : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  intro hE C T p _ y τ hC
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ τ.H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible τ.V
  have hK := IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)
  have hs := IsPullback.of_hasPullback τ.H.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue τ.V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  have : IsCommMonObj ((Over.pullback (Out.jK τ.V)).obj τ.H) := Functor.isCommMonObj_obj
  obtain ⟨ρ, hρ⟩ := gen_chartPull (chartPullLinComb T.L.L τ.φ (K := PUnit)
    (fun _ => eSec ((Over.pullback (Out.jK τ.V)).obj τ.H)) (fun _ => eSec C.A) (fun _ => 1) τ.yK
    fun _ => (cubeMapOf τ.φ_cart).e_comm) T.L.rig T.L.rigGen
  obtain ⟨L, w₀, hw₀⟩ := hE τ.V (FractionRing τ.V) τ.H (eSec ((Over.pullback (Out.jK τ.V)).obj τ.H))
    (cubeMapOf (isGrpPullback_pullback τ.H (Out.jK τ.V))).e_comm (T.L.L.pull τ.φ) (pull_isLB T.L.isLB _) ρ hρ
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull τ.φ T.L.L (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) w₀ T.L.isLB
    (pull_isLB L.isLB _) hw₀ T.θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ L.isLB r (by
    obtain ⟨x, k, hk⟩ := exists_mem_basicOpen T τ (hC p y τ)
    obtain ⟨a, ha⟩ := exists_chart (pull_isLB L.isLB (pullback.fst τ.H.hom (Out.jK τ.V))) x
    have hk' := C.A.left.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff τ.φ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap τ.V (FractionRing τ.V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective τ.V _)).2 hϖ.ne_zero)
  have hc := (h0.isUnit.map (Scheme.ΓSpecIso (.of (FractionRing τ.V))).inv.hom).map
    (pullback.snd τ.H.hom (Out.jK τ.V)).appTop.hom
  refine ⟨⟨L, invMul w₀ hc.unit, isGen_invMul hw₀ _, σ, fun x i k hi hk => ?_, x₀, Opens.mem_iSup.2 ⟨b, hb⟩, hx₀⟩⟩
  have hi' : x ∈ (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))).U fun _ => i := mem_pull.2 hi
  have hk' : x ∈ (T.L.L.pull τ.φ).U fun _ => k := mem_pull.2 hk
  have e₁ := congrArg (gs (𝟙 _) x _) (hσ fun _ => i)
  have e₂ := (gs_appLE _ _ _ _ (𝟙 _) x hi' _).symm.trans (e₁.trans ((gs_mul (𝟙 _) x _ hi' _ _).trans
    (congrArg (· * _) ((gs_res (𝟙 _) x le_top hi' _).trans (gs_unit (𝟙 _) x ⊤ trivial hc.unit)))))
  rw [Category.id_comp] at e₂
  refine e₂.trans (Eq.symm ?_)
  refine (congrArg₂ (· * ·) ((gs_unit (𝟙 _) x _ (show _ ∈ _ ⊓ _ from ⟨hi', hk'⟩) _).trans
    (congrArg Units.val (gm_invMul w₀ hc.unit x _ _ hi' hk'))) (hr x k _ hk hi')).trans ?_
  rw [Units.val_mul, _root_.mul_assoc]
  exact congrArg (_ * ·) (Units.inv_mul_cancel_left _ _)

end GlobalTheory.ZJ
end
