module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Uniformization.RankOneModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIffValEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3047
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

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

namespace GlobalTheory.GSep.TorTrans

theorem exists_trait_pull {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (φ : R →+* W)
      (ga : FractionRing R →+* FractionRing W) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
      (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal W) D' A' G')
      (a : A'.A.left ⟶ A.A.left) (xe : D'.toPre.X ≃+ D.toPre.X)
      (em : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing W)),
      IsAdicComplete (maximalIdeal W) W ∧ IsLocalHom φ ∧ (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
      IsSemiAbelian G' ∧ IsGrpPullback A'.A A.A (spMap ga) a ∧ LBIso A'.L (A.L.pull a) ∧
      em.comp (algebraMap (FractionRing R) _) = (algebraMap (FractionRing W) _).comp ga ∧
      ∀ k, 1 ≤ k → ∀ (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) k)
        (x : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing R)) k p x →
        ∃ (p' : QkPt D'.toPre (AlgebraicClosure (FractionRing W)) k)
          (x' : TFK (R := W) (AlgebraicClosure (FractionRing W)) ⟶ A'.A), p'.y = xe.symm p.y ∧
          QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing W)) k p' x' ∧ x'.left ≫ a = spMap em ≫ x.left := by
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  haveI := hR.1
  obtain ⟨W, _, _, _, φ, hW, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have hloc : IsLocalHom φ := ⟨fun r hr => by
    by_contra h
    have : r ∈ (maximalIdeal W).comap φ := hc.symm ▸ (mem_maximalIdeal r).2 h
    exact (mem_maximalIdeal _).1 this hr⟩
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨D', hD, A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR hW' φ hφ (Ideal.map_le_iff_le_comap.2 hc.ge) hG U
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp hφ
  let ga : FractionRing R →+* FractionRing W := IsFractionRing.lift hinj
  have hga : ∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    rw [← Spec.map_comp, ← Spec.map_comp]; congr 1; ext1; exact RingHom.ext fun r => (hga r).symm
  have g₁ := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have g₂ := ((GlobalTheory.ThetaBaseChange.grp_generic U'.toUnifPre).comp (isGrpPullback_pullback G (spMap φ))).congr hsq rfl
  let a : A'.A.left ⟶ A.A.left := g₁.1.lift _ (A'.A.hom ≫ spMap ga) (g₂.1.w.trans (Category.assoc _ _ _).symm)
  have ha : a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = _ := g₁.1.lift_fst _ _ _
  have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (specOf φ) := Category.id_comp _
  have gp : IsGrpPullback A'.A A.A (spMap ga) a := g₁.cancel (g₂.congr rfl ha.symm) (g₁.1.lift_snd _ _ _)
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing W)) :=
    ((algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))).comp ga).toAlgebra
  obtain ⟨em⟩ : Nonempty (AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] AlgebraicClosure (FractionRing W)) :=
    ⟨IsAlgClosed.lift⟩
  have hF : GlobalTheory.ArcPull.Compat φ (AlgebraicClosure (FractionRing W)) := fun r =>
    congrArg (algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))) (hga r)
  refine ⟨W, _, _, hW.1, hW.2.2, φ, ga, D', A', _, _, _, U', a, hD.xe, em.toRingHom, hW.2.1, hloc, hga,
    IsSemiAbelian.pullback _ G hG, gp, ?_, em.comp_algebraMap, fun k hk p x hpx => ?_⟩
  · have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hgi' : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have H₀ : LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
    have H₁ : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst _ (jK W))) :=
      LBIso.chartPull (h := U'.gen.inv.left) (chartPullSec A'.L _ _ hgi')
        (chartPullSame U'.LG.L _ (fun _ => pullback.fst _ (jK W)) _ _ fun _ => rfl) U'.ext
    have H₂ : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst _ (jK W)))
        (U.LG.L.pull (a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => _) _ _ fun _ => ha.trans (congrArg (_ ≫ ·) hb.symm))
        ⟨hP.lg.choose, hP.lg.choose_spec.1⟩
    have H₃ : LBIso (A.L.pull a) (U.LG.L.pull (a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSame U.LG.L _ (fun _ => _) _ _ fun _ => rfl) H₀
    exact (H₁.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) H₂).trans A'.isLB (pull_isLB U.LG.isLB _)
      (pull_isLB A.isLB _) H₃.symm
  · obtain ⟨⟨p₁, h₁⟩, hx, hgal⟩ := GlobalTheory.UT.ClModel.galois_all R _ hR D A G hG U _ _ em k hk p
    obtain ⟨x₁, hx₁⟩ := hx x
    have hw : x₁.left ≫ A.A.hom = jFK (R := W) (AlgebraicClosure (FractionRing W)) ≫ spMap ga :=
      (Over.w x₁).trans (Spec.map_comp (CommRingCat.ofHom ga) (CommRingCat.ofHom (algebraMap _ _)))
    let x' : TFK (R := W) (AlgebraicClosure (FractionRing W)) ⟶ A'.A :=
      Over.homMk (gp.1.lift x₁.left _ hw) (gp.1.lift_snd _ _ _)
    have h₄ : x'.left ≫ a = x₁.left := gp.1.lift_fst _ _ _
    obtain ⟨h₂, h₃⟩ := (GlobalTheory.ArcPull.eq_pullQk_iff hD hL.globalFns hF D.tau_bimult D'.tau_bimult p₁ _).1 rfl
    refine ⟨_, x', h₂.trans (congrArg _ h₁.1), ?_, h₄.trans hx₁⟩
    refine h5.qkBaseChange R W _ _ hR hW' φ D A G U _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hP
      _ hF k hk p₁ x₁ _ x' h₂ h₃ ?_ ((hgal p₁ x x₁ h₁ hx₁).1 hpx)
    rw [← h₄, Category.assoc, ha, hb, Category.assoc]

theorem div_and_translate {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type}
    [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X]
    {t : X → V} {δ : I → X → X} (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {x₀ : X₁.S.Gam}
    (hx₀ : X₁.M.Div X₁.S.th x₀ z₁) (a₀ : X₁.S.Gam) (ha₀ : 𝔪.YY a₀ 0) (a : X₁.S.Gam) (mu : X) (ha : 𝔪.YY a mu) :
    (a ∈ X₁.S.supI X₁.M z₁ → ∃ w, mu = (X₁.S.r * X₁.S.N) • w) ∧
      ((∃ w, mu = (X₁.S.r * X₁.S.N) • w) → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ a + b ∈ X₁.S.supI X₁.M z₁) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI := 𝔪.loc
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨T, _, _, _, _, φ, ga, D', A', G', _, _, U', α, xe, em, hc, hloc, hga, hG', gp, lb, hem, hmove⟩ :=
    exists_trait_pull hA 𝔪.semi 𝔪.U
  let ξ : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁
  have hx : ξ (closedPoint V) = z₁ := by
    show X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁
    rw [show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]
    exact Scheme.fromSpecStalk_closedPoint
  have hU : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : T) := by
    have := (X₁.S.unit.map (Spec.preimage (ξ ≫ X₁.M.s)).hom).map φ
    rwa [map_natCast, map_natCast] at this
  haveI : CharZero (FractionRing T) := charZero_of_injective_algebraMap (IsFractionRing.injective T (FractionRing T))
  have cart : IsGrpPullback A'.A X₁.ρ.P.A (spMap (ga.comp 𝔪.yK)) (α ≫ 𝔪.φ) :=
    (gp.comp 𝔪.cart).congr (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom ga)).symm rfl
  have lb' : LBIso A'.L (X₁.ρ.P.L.pull (α ≫ 𝔪.φ)) :=
    LBIso.trans A'.isLB (pull_isLB 𝔪.A.isLB _) (pull_isLB X₁.ρ.P.isLB _) lb (lbIso_pull_comp ⟨𝔪.wl, 𝔪.wl_gen⟩ α)
  obtain ⟨s, v, hs, hsv, -, hcl⟩ := GlobalTheory.Poinc.ScaleAtModel.scale_at_model _ _ X₁.S X₁.ρ T hc hU (ga.comp 𝔪.yK) A' _
    cart lb' G' hG' D' U' (GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 _ _ _ X₁.ρ _ _)
  have tr : ∀ a mu, 𝔪.YY a mu → (IsUnit (v a) → ∃ w, mu = (X₁.S.r * X₁.S.N) • w) ∧
      ((∃ w, mu = (X₁.S.r * X₁.S.N) • w) → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ IsUnit (v (a + b))) := by
    rintro a mu ⟨p, x, hp, hq, hxa⟩
    obtain ⟨p', x', hp', hq', hx'⟩ := hmove _ hk p x hq
    obtain ⟨h₁, h₂⟩ := hcl a p' x' hq' (by
      rw [← Category.assoc, hx', Category.assoc, hxa, ← Category.assoc, ← RingHom.comp_assoc, ← hem, RingHom.comp_assoc]
      exact congrArg (· ≫ _) (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom em)).symm)
    rw [hp] at hp'
    refine ⟨fun h => ?_, fun ⟨w, hw⟩ => h₂ ⟨xe.symm (𝔪.e₈ w), by rw [hp', hw, map_nsmul, map_nsmul]⟩⟩
    obtain ⟨z, hz⟩ := h₁ h
    refine ⟨𝔪.e₈.symm (xe z), ?_⟩
    rw [← map_nsmul, ← map_nsmul, ← hz, hp', AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  have hsp : ∀ w, (jK V ≫ ξ) w ⤳ (jK V ≫ ξ) (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim w (closedPoint (FractionRing V))]
  have hsx : ξ (closedPoint V) ⤳ z₁ := hx ▸ specializes_rfl
  let wv : X₁.S.Gam → V := fun b => RatModel.valLoc ξ z₁ hsx ⟨X₁.S.th b / X₁.S.th x₀, hx₀.2 b⟩
  have hw : ∀ b, φ (wv b) * v x₀ = v b := fun b => by
    have e1 : X₁.M.val (jK V ≫ ξ) (X₁.S.th b / X₁.S.th x₀) = algebraMap V (FractionRing V) (wv b) :=
      RatModel.val_spMap_comp (algebraMap V (FractionRing V)) ξ hsx ⟨X₁.S.th b / X₁.S.th x₀, hx₀.2 b⟩
    have e2 := RatModel.val_mul hsp (RatModel.O_le_of_specializes (hx ▸ (IsLocalRing.specializes_closedPoint
      (jK V (closedPoint (FractionRing V)))).map ξ.continuous) (hx₀.2 b)) (𝔪.reg _ (X₁.S.th_mem x₀))
    rw [div_mul_cancel₀ _ hx₀.1, e1] at e2
    have e3 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ =
        algebraMap V (FractionRing V) (wv b) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
      rw [𝔪.yK_eq, 𝔪.yK_eq]; exact e2
    have e4 := congrArg ga e3
    rw [map_mul, hga] at e4
    have e5 := hsv b
    have e6 := hsv x₀
    rw [RingHom.comp_apply] at e5 e6
    rw [e5, e6, ← _root_.mul_assoc, mul_comm _ s, _root_.mul_assoc, ← map_mul] at e4
    exact IsFractionRing.injective T (FractionRing T) (mul_left_cancel₀ hs e4).symm
  obtain ⟨b₀, -, hb₀⟩ := (tr a₀ 0 ha₀).2 ⟨0, (nsmul_zero _).symm⟩
  have hv0 : IsUnit (v x₀) := isUnit_of_mul_isUnit_right (show IsUnit (φ (wv (a₀ + b₀)) * v x₀) by rw [hw]; exact hb₀)
  have hset : ∀ b, b ∈ X₁.S.supI X₁.M z₁ ↔ IsUnit (v b) := fun b => by
    show X₁.M.Div X₁.S.th b z₁ ↔ IsUnit (v b)
    rw [hx₀.div_iff_isUnit b, ← RatModel.isUnit_valLoc_iff ξ hx, ← hw b, IsUnit.mul_iff, and_iff_left hv0,
      isUnit_map_iff φ]
  simp only [hset]
  exact tr a mu ha

theorem exists_translate_mem_supI : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ a, 𝔪.YY a 0 → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ a + b ∈ X₁.S.supI X₁.M z₁ := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ hx₀ a ha
  exact (div_and_translate 𝔪 hx₀ a ha a 0 ha).2 ⟨0, (nsmul_zero _).symm⟩

end GlobalTheory.GSep.TorTrans
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

noncomputable section

namespace GlobalTheory.GSep.TermsLabel

theorem yy_zero_of_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ c, 𝔪.YY (lab c) 0 := by
  intro I X₁ z₁ act x₀ V _ _ _ ev X _ t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, -⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨⟨o, ho₁, ho₂⟩, hwc, hov⟩ := hg c
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (AlgebraicClosure (FractionRing V))
  have hkg : (X₁.S.r * X₁.S.N) • g' c = 0 :=
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq _).1 ho₂)
  set gb := GlobalTheory.TorusExt.gtExt 𝔪.D.toPre (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))
    (RingHom.comp_id _) (g' c) with hgb
  have hkgb : (X₁.S.r * X₁.S.N) • gb = 0 := by
    rw [hgb, ← map_nsmul, hkg, map_zero]

  have hi : GtPtF.IsIota 0 (0 : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V))) := by
    have hz := (GlobalTheory.TorusExt.isZero_iff_eq (0 : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V)))).2 rfl
    obtain ⟨hb, hv⟩ := (GlobalTheory.TorusExt.isZero_iff_val _).1 hz
    refine (GlobalTheory.TorusExt.isIota_iff_val 0 _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have C : IsCub (DVR.th 𝔪.D.toPre (T := TF (R := V) (AlgebraicClosure (FractionRing V))) y J) := isCub_cubV 𝔪.D.toPre.cub hJ
    have tt := tau_mul (𝟙 (TF (R := V) (AlgebraicClosure (FractionRing V)))) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) :=
    ⟨0, gb, 0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hkgb.symm, hi⟩
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x (lab c)
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ (g' c) (w c) (x (lab c)) (fr (lab c)) hwc (hfr _).1 hov xb rfl

  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have hq := (f₁ p (f' p)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V))
    w₀ hw₀ _ hk p (f' p) rfl hq

  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀ hw₀ p.g wb w' xb
    (f' p) frb fr' hwb hw' hfrb hfr' hlb hl'
  refine ⟨p, xb, (map_zero 𝔪.e₈).symm, e ▸ hq, ?_⟩
  have e₁ : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
    (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  rw [← e₁, Category.assoc, ← hx (lab c)]
  rfl

end GlobalTheory.GSep.TermsLabel
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
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep

theorem over_rescale : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ g w w' x e e' l hl he hw H k hk wk' hwk' hgen s s' v hs hv
  have hlk : l ^ k ≠ 0 := pow_ne_zero k hl
  obtain ⟨wk, hwkg, hwk⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale wk' hgen hlk
  have h₁ : ValAt s x e (l ^ k * v) := fun z J hJ => by
    rw [hv z J hJ]
    have r₁ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    have r₂ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e' (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e' (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    rw [r₁, r₂, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    simp only [id, GlobalTheory.Poinc.TorsRatio.cst_eq_cstK, map_mul, map_pow]
    ring
  have h₂ := H k hk wk (fun z J hJ => Units.ext (by
    rw [hwk z J hJ, hwk' z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, map_pow])) hwkg s s' _ hs h₁
  have h₃ := GlobalTheory.Poinc.Sep.sumF_const_mul (l ^ k)⁻¹ h₂
  simpa only [GlobalTheory.UT.TorsionValue.coef_scale hgen hwk, inv_mul_cancel_left₀ hlk] using h₃

end GlobalTheory.GSep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TorsUniq

theorem same_point : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b ∧ ∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ x fr g g₂ w w₂ hw₀ hfr hg hw ho hg₂ hw₂ ho₂
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨e, -⟩ := GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hn g g₂ w w₂ x fr hg hg₂ hw hw₂ hfr ho ho₂
  subst e
  exact ⟨rfl, fun _ _ _ _ => rfl⟩

end GlobalTheory.GSep.TorsUniq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.Labels

theorem comp_pow_overScheme_grpObj {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]


open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in
theorem yy_hom : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ CongMod (X₁.S.r * X₁.S.N) mu' mu)) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, -, he, -⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y →
      y ^ (X₁.S.r * X₁.S.N) = 1 := fun p y h => by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (h w hw).1
  have uniq : ∀ a (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 →
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left → y = x a := by
    intro a y hy hya
    obtain ⟨b, rfl⟩ := xonto y hy
    obtain ⟨c, -, hc⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V))
      (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK))
      ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) :
        Over.mk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ⟶
          baseOver (Sp X₁.S.R)) ≫ X₁.ρ.pt a)
      (by rw [← comp_pow_overScheme_grpObj, (X₁.ρ.fr_tors a).1, MonObj.comp_one])
    have h1 := hc a rfl
    have h2 := hc b (by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
      rw [← hx b, hya])
    rw [h1.trans h2.symm]
  have ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) :=
    fun a => by
      obtain ⟨p, hp⟩ := f₂ (x a) (he a).1
      exact ⟨p, (f₁ _ _).2 hp.symm⟩
  have yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N),
      p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) := by
    intro a mu
    constructor
    · rintro ⟨p, y, hpy, hq, hov⟩
      obtain rfl := uniq a y (tor p y hq) hov
      exact ⟨p, hpy, hq⟩
    · rintro ⟨p, hpy, hq⟩
      exact ⟨p, x a, hpy, hq, hx a⟩
  refine ⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩
  · obtain ⟨p, hp⟩ := ex a
    exact ⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩
  · obtain ⟨p, hp⟩ := exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)
    obtain ⟨a, ha⟩ := xonto (f p) (tor p _ ((f₁ _ _).2 rfl))
    exact ⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    rw [yyI]
    constructor
    · rintro ⟨p', hpy', hq'⟩
      have hpp : QkPt.Equiv _ _ p p' := (f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))
      obtain ⟨z, hz, -⟩ := (GlobalTheory.TorusExt.equiv_iff hB p p').1 hpp
      have e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])
      exact ⟨𝔪.e₈.symm z, e'⟩
    · intro hc
      obtain ⟨w, hw⟩ := hc
      refine ⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩
      show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'
      rw [hpy, ← map_nsmul, ← map_add (f := _)]
      rw [hw]
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    obtain ⟨p', hpy', hq'⟩ := (yyI a' mu').1 h'
    refine (yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩
    · show p.y + p'.y = 𝔪.e₈ (mu + mu')
      rw [map_add (f := _), hpy, hpy']
    · rw [f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]

end GlobalTheory.GSep.Labels
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
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match | exact GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match | (intros; apply GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.level_unit_thetaConstant_ne_zero_divides_all : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧ ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  first | exact @GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd | exact GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd | (intros; apply GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd <;> assumption)
end
