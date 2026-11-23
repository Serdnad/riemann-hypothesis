module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_baseChange_semiAbelian_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R' → FinExt ρ → ∃ (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), IsSemiAbelian G₁ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) := by
  intro R _ _ _ _ G _ _ hG P A gen hmon hext R' _ _ _ ρ _ hfin
  have hinj : Function.Injective ρ := hfin.2.1

  have gpG₁ : IsGrpPullback ((Over.pullback (spMap ρ)).obj G) G (spMap ρ) (pullback.fst G.hom (spMap ρ)) :=
    isGrpPullback_pullback G (spMap ρ)
  obtain ⟨β₂, hsq, hlam⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ) G ((Over.pullback (spMap ρ)).obj G) _ gpG₁

  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap (hw := pullback.condition) P
    (GlobalTheory.UU.toBase_mul_pullback G (spMap ρ)) _ (pull_isLB P.L.isLB _) _ (GlobalTheory.UU.pullIso_isGen P.L.isLB _)
  let P₁ : GlobalTheory.UU.CP ((Over.pullback (spMap ρ)).obj G) :=
    ⟨⟨P.L.L.pull (pullback.fst G.hom (spMap ρ)), rig, pull_isLB P.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩

  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hinj)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (GlobalTheory.ArcPull.fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  haveI := hmon
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have gpGen : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ :=
    (GlobalTheory.ArcPull.fracMap_sq hinj).symm.trans (Category.id_comp _)
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G
      (spMap (GlobalTheory.ArcPull.fracMap hinj) ≫ jK R)
      (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp gpG₁).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpGen)
  refine ⟨(Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance, pullback.fst G.hom (spMap ρ), β₂, P₁, A', eA,
    IsSemiAbelian.pullback _ G hG, gpG₁, hsq, mE, ?_, ?_⟩
  · refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB (pull_isLB P.L.isLB _) _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    have hgi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb P.L.L (pullback.fst G.hom (spMap ρ))
        (fun _ => pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R'))
        (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) hext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  · have hL := P.L.isLB
    have h := hlam P.L.L (P.L.L.pull (pullback.fst G.hom (spMap ρ))) _ (abelian₂ G P.L.L) (𝟙 _) hL (pull_isLB hL _)
      (LB.isLB_linComb hL _ _) (lbIso_refl (pull_isLB hL _)) (LBIso.symm (lbIso_pull_id (LB.isLB_linComb hL _ _)))
    rwa [Category.comp_id] at h

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenericPull

open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull GlobalTheory.FieldPull

theorem nonempty_isPullDeg_cancel {R K₁ K : Type} [CommRing R] [IsDomain R] [Field K₁] [Field K] {α : R →+* K₁}
    (hα : Function.Injective α) (β : K₁ →+* K) {D₀ : DegPre R} {D₁ : DegPre K₁} {D : DegPre K}
    (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D) : Nonempty (IsPullDeg β D₁ D) := by
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen)
    ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (pmaps_rig h₁) (pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨hD, -, -, -⟩ := exists_isPullDeg_of_val β D₁ D gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK K ≫ spMap β = genMap β.injective ≫ jK K₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq β.injective)
    have sα : jK K₁ ≫ spMap α = genMap hα ≫ jK R :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap β.injective ≫ jK K₁ ≫ spMap α = (genMap β.injective ≫ genMap hα) ≫ jK R :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK K).left ≫ jK K ≫ spMap (β.comp α) = (genMap β.injective ≫ genMap hα) ≫ jK R :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap β.injective ≫ D₁.xK (xe x) := by
      show (jK K ≫ (D.c x).left) ≫ Φ = genMap β.injective ≫ jK K₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

theorem exists_generic_fibre {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) :
    ∃ E : DegPre (FractionRing R), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D E) := by
  obtain ⟨U, hU, hψ⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨E, p, -⟩ := DegPull.exists_isPullDeg polBaseChange_holds R (FractionRing R) (algebraMap R (FractionRing R))
    D U hψ (TauPull.jK_mem (R := R) (genericPoint (Spec (CommRingCat.of (FractionRing R)))) U ⟨_, hU⟩)
  exact ⟨E, ⟨p⟩⟩

end GlobalTheory.GenericPull

namespace GlobalTheory.Mum

open GlobalTheory.GenericPull

theorem exists_generic_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, IsPullDeg φ D₁.toPre D' → IsPullDeg φ D₂.toPre D' → ∃ (E₁ E₂ : DegPre (FractionRing R)) (L : Type) (_ : Field L) (β : FractionRing R →+* L) (E' : DegPre L), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₁.toPre E₁) ∧ Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₂.toPre E₂) ∧ Nonempty (IsPullDeg β E₁ E') ∧ Nonempty (IsPullDeg β E₂ E') := by
  intro R _ _ _ _ D₁ D₂ W _ _ φ hφ D' p₁ p₂
  obtain ⟨E₁, ⟨q₁⟩⟩ := exists_generic_fibre D₁.toPre D₁.tau_bimult
  obtain ⟨E₂, ⟨q₂⟩⟩ := exists_generic_fibre D₂.toPre D₂.tau_bimult
  obtain ⟨E', ⟨q⟩⟩ := exists_generic_fibre D' (TauPull.tauBimult_pull globalFns_holds p₁ D₁.tau_bimult)
  have e : (algebraMap W (FractionRing W)).comp φ = (ArcPull.fracMap hφ).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun x => (ArcPull.fracMap_algebraMap hφ x).symm
  have hR := IsFractionRing.injective R (FractionRing R)
  have hW := IsFractionRing.injective W (FractionRing W)
  obtain ⟨r₁⟩ := e ▸ PullDegComp.nonempty_isPullDeg_comp hφ hW p₁ q
  obtain ⟨r₂⟩ := e ▸ PullDegComp.nonempty_isPullDeg_comp hφ hW p₂ q
  exact ⟨E₁, E₂, FractionRing W, inferInstance, ArcPull.fracMap hφ, E', ⟨q₁⟩, ⟨q₂⟩,
    nonempty_isPullDeg_cancel hR _ q₁ r₁, nonempty_isPullDeg_cancel hR _ q₂ r₂⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.CommonCover

theorem exists_cover_field (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (K' : Type) [Field K']
    (io : FractionRing R →+* K') (hfin : io.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'),
      FinExt ρ ∧ IsLocalHom ρ ∧ τ.comp (io.comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  obtain ⟨⟨hN, -, hIC, hC⟩, hc0⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hfin
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : Algebra.IsSeparable (FractionRing R) K' := inferInstance
  let C := integralClosure R K'
  haveI : Module.Finite R C := IsIntegralClosure.finite R (FractionRing R) K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension (FractionRing R) K'
  have hφ : Function.Injective (algebraMap R C) := fun a b h => by
    have h' : io (algebraMap R (FractionRing R) a) = io (algebraMap R (FractionRing R) b) := congrArg Subtype.val h
    exact IsFractionRing.injective R (FractionRing R) (io.injective h')
  obtain ⟨R', _, _, _, ρ, σ, hCN, hρ, hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) ⟨hN, hIC, hC, hc0⟩ hφ (RingHom.finite_algebraMap.2 inferInstance)
  have hσi : Function.Injective σ := by
    refine (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := R) ?_)
    change (RingHom.ker σ).comap (algebraMap R C) = ⊥
    rw [RingHom.comap_ker, hσ]
    exact (RingHom.injective_iff_ker_eq_bot ρ).1 hρ
  have hg : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσi
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, IsFractionRing.lift (A := C) hg,
    ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hρ, hfin'⟩, hloc, ?_⟩
  ext r
  have e : io (algebraMap R (FractionRing R) r) = algebraMap C K' (algebraMap R C r) := rfl
  simp only [RingHom.comp_apply]
  rw [e, IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply σ, hσ]

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegPre R) (E₁ E₂ : DegPre (FractionRing R)), IsPullDeg (algebraMap R (FractionRing R)) D₁ E₁ → IsPullDeg (algebraMap R (FractionRing R)) D₂ E₂ → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (E₃ : DegPre K'), io.Finite → IsPullDeg io E₁ E₃ → IsPullDeg io E₂ E₃ → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (E : DegPre (FractionRing R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) := by
  intro R _ _ _ hR D₁ D₂ E₁ E₂ p₁ p₂ K' _ io E₃ hfin q₁ q₂
  obtain ⟨R', _, _, _, ρ, τ, hE, hloc, hτ⟩ := exists_cover_field R hR K' io hfin
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨E, t, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hL.polBaseChange K' (FractionRing R') τ E₃ ⊤
    (GlobalTheory.FieldPull.nonempty_psiOn_field E₃) trivial
  have ha : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hio : Function.Injective (io.comp (algebraMap R (FractionRing R))) := io.injective.comp ha
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, E, hE, hloc, ?_, ?_⟩
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₁ q₁
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₂ q₂
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t

end GlobalTheory.CommonCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_finExt_realising : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (E : IntermediateField (FractionRing R₁) (Kb R₁)), FiniteDimensional (FractionRing R₁) E → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ ∧ FinExt (i₁₂.comp ρ) ∧ IsLocalHom i₁₂ ∧ ∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r) := by
  intro R _ _ _ hR R₁ _ _ _ ρ hρ E hE
  obtain ⟨hadm, hinj, hfin⟩ := hρ
  haveI : CharZero R := hR.2
  haveI : CharZero R₁ := charZero_of_injective_ringHom hinj
  have hR₁ : Base R₁ := ⟨hadm, inferInstance⟩
  let E' := IntermediateField.normalClosure (FractionRing R₁) E (Kb R₁)
  haveI : IsGalois (FractionRing R₁) E' := inferInstance
  haveI : FiniteDimensional (FractionRing R₁) E' := inferInstance
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E') hR₁
  letI : Algebra R₁ E' := (baseMap R₁ E').toAlgebra
  haveI : IsScalarTower R₁ (FractionRing R₁) E' := IsScalarTower.of_algebraMap_eq' rfl
  set R₂ := integralClosure R₁ E'
  haveI : IsFractionRing R₂ E' := integralClosure.isFractionRing_of_finite_extension (FractionRing R₁) E'
  let incl : E →ₐ[FractionRing R₁] E' := IntermediateField.inclusion (IntermediateField.le_normalClosure E)
  let eqv : E' ≃ₐ[R₂] FractionRing R₂ := (FractionRing.algEquiv R₂ E').symm
  have hloc' : IsLocalHom (algebraMap R₁ R₂) := by
    haveI : Module.Finite R₁ R₂ := RingHom.finite_algebraMap.1 hfe.2.2
    have : (Ideal.comap (algebraMap R₁ R₂) (maximalIdeal R₂)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal R₂)
    exact ((local_hom_tfae (algebraMap R₁ R₂)).out 1 5).mpr (IsLocalRing.eq_maximalIdeal this)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R₁ R₂, eqv.toRingHom.comp incl.toRingHom, hfe,
    ⟨hfe.1, hfe.2.1.comp hinj, hfe.2.2.comp hfin⟩, hloc', fun r => ?_⟩
  have h1 : incl (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ E' (algebraMap R₁ R₂ r) :=
    incl.commutes _
  change eqv (incl _) = _
  rw [h1]
  exact eqv.commutes _

end GlobalTheory.GalClosure
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsionLabels_trait_compatible_levels_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → ∀ (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) (k * d)), q.y = d • p.y → q.g = p.g → lab (k * d) q = lab k p := by
  first | exact @GlobalTheory.Mum.lab_level_mul | exact GlobalTheory.Mum.lab_level_mul | (intros; apply GlobalTheory.Mum.lab_level_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.eq_of_fieldPoints_closedFibre_same_projective_image : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ E.H.toScheme), (∀ t, M.π (G'.hom (E.H.ι (p t))) = closedPoint R) → p ≫ E.H.ι ≫ G'.hom = p' ≫ E.H.ι ≫ G'.hom → p ≫ E.f = p' ≫ E.f → p = p' := by
  first | exact @GlobalTheory.Mum.Emb.eq_of_closedFibre | exact GlobalTheory.Mum.Emb.eq_of_closedFibre | (intros; apply GlobalTheory.Mum.Emb.eq_of_closedFibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_extension_fraction_field_uniform : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (A : PolAV (Sp (FractionRing R₁))) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), Function.Injective i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → ∃ x₀ : Sp (FractionRing R₂) ⟶ A₂.A.left, x.left = spMap (algebraMap (FractionRing R₂) (Kb R₂)) ≫ x₀ := by
  first | exact @GlobalTheory.Mum.RatTors.torsion_rational | exact GlobalTheory.Mum.RatTors.torsion_rational | (intros; apply GlobalTheory.Mum.RatTors.torsion_rational <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.endomorphism_characterAction_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (a : 𝓞 E), EndChar P.U (t.act.act a) (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) := by
  first | exact @GlobalTheory.UPoinc.endChar_act | exact GlobalTheory.UPoinc.endChar_act | (intros; apply GlobalTheory.UPoinc.endChar_act <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.algClosurePoint_factors_through_finite_local_subalgebra : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Z : Scheme.{0}) (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z), k ≫ π = (TF (R := R) (Kb R)).hom → ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧ ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k := by
  first | exact @GlobalTheory.Mum.finpt_factor | exact GlobalTheory.Mum.finpt_factor | (intros; apply GlobalTheory.Mum.finpt_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibreEmbedding_lift_separated_finiteType_quasiCompact : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', IsSeparated (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧ LocallyOfFiniteType (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧ QuasiCompact (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) := by
  first | exact @GlobalTheory.Mum.emb_lift_sep_loft_qc | exact GlobalTheory.Mum.emb_lift_sep_loft_qc | (intros; apply GlobalTheory.Mum.emb_lift_sep_loft_qc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lift_to_projective_base_injective_over_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ z w : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over w = pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over z → w = z := by
  first | exact @GlobalTheory.Mum.Emb.chart_injective | exact GlobalTheory.Mum.Emb.chart_injective | (intros; apply GlobalTheory.Mum.Emb.chart_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkPt_rational_of_pull : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ → IsLocalHom i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p := by
  intro R₁ _ _ _ hR D₁ n hn
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hG := hL.globalFns
  have hB₁ := D₁.tau_bimult
  have := hR.2
  have : CharZero (Kb R₁) := (RingHom.charZero_iff (algebraMap (FractionRing R₁) (Kb R₁)).injective).1 inferInstance
  obtain ⟨M, hM, H⟩ := GlobalTheory.QkNumberField.exists_finite_qk (D := D₁.toPre) (L := Kb R₁) hL hB₁ (N := n)
    (Nat.cast_ne_zero.2 (by omega))
  refine ⟨M, hM, ?_⟩
  intro R₂ _ _ _ i₁₂ e hfin _ he D₂ ⟨hD⟩ p
  have hB₂ := D₂.tau_bimult
  have hi : Function.Injective i₁₂ := hfin.2.1
  letI : Algebra (FractionRing R₁) (FractionRing R₂) := (fracMap hi).toAlgebra
  have he' : e.comp (algebraMap (FractionRing R₁) M) = algebraMap (FractionRing R₁) (FractionRing R₂) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => (he r).trans (fracMap_algebraMap hi r).symm)
  letI : Algebra (FractionRing R₁) (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp (fracMap hi)).toAlgebra
  have cK : Compat i₁₂ (Kb R₂) := fun r => congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (fracMap_algebraMap hi r)
  have cF : Compat i₁₂ (FractionRing R₂) := fracMap_algebraMap hi
  letI : Algebra M (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp e).toAlgebra
  haveI : Module.IsTorsionFree M (Kb R₂) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree M (Kb R₁) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Algebra.IsAlgebraic M (Kb R₁) := Algebra.IsAlgebraic.tower_top (K := FractionRing R₁) M
  let σ' : Kb R₁ →ₐ[M] Kb R₂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ' : ∀ m : M, σ' (m : Kb R₁) = algebraMap (FractionRing R₂) (Kb R₂) (e m) := fun m => σ'.commutes m
  let σ : Kb R₁ →ₐ[FractionRing R₁] Kb R₂ := ⟨σ'.toRingHom, fun x => by
    show σ' (algebraMap (FractionRing R₁) (Kb R₁) x) = _
    exact (hσ' (algebraMap (FractionRing R₁) M x)).trans (congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.congr_fun he' x))⟩
  have key : σ.toRingHom.comp M.val.toRingHom = (algebraMap (FractionRing R₂) (Kb R₂)).comp e :=
    RingHom.ext fun m => hσ' m
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG cK hB₁ hB₂ p
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.LabTrans.exists_of_ext hB₁ σ hn q
  obtain ⟨z, rfl⟩ := H n dvd_rfl q₀
  let z' : QkPt D₁.toPre (FractionRing R₂) n := qkExt hB₁ e he' z
  let p₀ := pullQk hD hG cF hB₁ hB₂ z'
  let p₁ := qkExt hB₂ (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.comp_id _) p₀
  have hp₁ : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ := (qkExt_iff hB₂ _ _ _ _).2 rfl
  have hf₂ : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₁) (FractionRing R₂)) =
      algebraMap (FractionRing R₁) (Kb R₂) := rfl
  let w := qkExt hB₁ (algebraMap (FractionRing R₂) (Kb R₂)) hf₂ z'
  have hw : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) z' w := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz' : QkExt e z z' := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz : QkExt M.val.toRingHom z (qkExt hB₁ M.val.toRingHom (GlobalTheory.QkNumberField.val_comp M) z) :=
    (qkExt_iff hB₁ _ _ _ _).2 rfl
  have t₁ := GlobalTheory.LabTrans.qkExt_trans hz hq₀
  have t₂ := GlobalTheory.LabTrans.qkExt_trans hz' hw
  rw [← key] at t₂
  have hqw : q = w := GlobalTheory.QkClosure.qkExt_unique (σ.toRingHom.comp M.val.toRingHom) (σ.comp_algebraMap ▸ rfl) t₁ t₂
  refine ⟨p₀, p₁, hp₁, ?_⟩
  have e₁ : p₁ = pullQk hD hG cK hB₁ hB₂ q := by
    rw [eq_pullQk_iff]
    refine ⟨?_, ?_⟩
    · rw [hqw]; rfl
    · rw [hqw]
      exact isPullGtF_ext hD cK _ (RingHom.comp_id _) (isPullGtF_pullGt hD hG cF z'.g) hw hp₁
  rw [e₁]
  exact qk_equiv_refl hB₂ _

end GlobalTheory.Mum
end
