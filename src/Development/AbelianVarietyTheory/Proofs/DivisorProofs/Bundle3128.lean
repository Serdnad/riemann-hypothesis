module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LamPullComp

section Iso

variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {B' : Over S₁} [GrpObj B']
  {G' : Over S₂} [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {β₂ : (G2 B').left ⟶ (G2 G).left}
  {sq : (G2 G').left ⟶ (G2 B').left} {L : LB G.left} {L' : LB G'.left}

theorem pt_eq (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (I : ULift.{0} (Finset (Fin 2))) (x : (G2 G').left) :
    lamφ G I (β₂ (sq x)) = φ (lamφ G' I x) :=
  congrArg (fun g => g x) (h I)

theorem iso_le (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ)
    (p : (((abelian₂ G L).pull β₂).pull sq).ι × (abelian₂ G' L').ι) (I : ULift.{0} (Finset (Fin 2))) :
    (((abelian₂ G L).pull β₂).pull sq).U p.1 ⊓ (abelian₂ G' L').U p.2 ≤
      lamφ G' I ⁻¹ᵁ ((L.pull φ).U (fun _ => p.1 PUnit.unit PUnit.unit I) ⊓ L'.U (p.2 I)) := fun x hx =>
  ⟨mem_pull.2 (by
    have := Set.mem_iInter.1 (mem_pull.1 (mem_pull.1 hx.1)) I
    show φ (lamφ G' I x) ∈ _
    rw [← pt_eq h I x]; exact this), Set.mem_iInter.1 hx.2 I⟩

def iso2 (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) :
    LB.Iso (abelian₂ G' L') (((abelian₂ G L).pull β₂).pull sq) :=
  ⟨fun p => ∏ I, (res (iso_le h p I)
    (pullU (lamφ G' I) _ (v.s (fun _ => p.1 PUnit.unit PUnit.unit I, p.2 I)))) ^ lamε I⟩

theorem mumfordBundle_pullback_composite_germ_iso (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) {Y : Scheme.{0}}
    (r : Y ⟶ (G2 G').left) (y : Y) (j : PUnit → ULift.{0} (Finset (Fin 2)) → L.ι)
    (k : ULift.{0} (Finset (Fin 2)) → L'.ι)
    (hj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I)) (hk : ∀ I, lamφ G' I (r y) ∈ L'.U (k I)) :
    gw (iso2 h v) r y j k = ∏ I, gw v (r ≫ lamφ G' I) y (j PUnit.unit I) (k I) ^ lamε I := by
  have hm : r y ∈ (((abelian₂ G L).pull β₂).pull sq).U (fun _ => j) ⊓ (abelian₂ G' L').U k :=
    ⟨mem_pull.2 (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (sq (r y))) ∈ L.U (j PUnit.unit I)
      rw [pt_eq h]; exact hj I)), Set.mem_iInter.2 hk⟩
  unfold gw
  dsimp only [iso2]
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => (map_zpow _ _ _).trans (congrArg (· ^ lamε I) ?_))
  exact (gm_res r y _ hm _).trans (gm_pull r (lamφ G' I) y ((L.pull φ).U (fun _ => j PUnit.unit I) ⊓ L'.U (k I))
    ⟨mem_pull.2 (hj I), hk I⟩ _)

theorem mumfordBundle_pullback_composite_isGen (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) (hv : PGen v) :
    PGen (iso2 h v) := by
  intro Y r y j j' k k' hj hj' hk hk'
  have bj := mem_pull.1 hj
  have bj' := mem_pull.1 hj'
  have aj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj I
  have aj' : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j' PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj' I
  have ak : ∀ I, lamφ G' I (r y) ∈ L'.U (k I) := fun I => Set.mem_iInter.1 hk I
  have ak' : ∀ I, lamφ G' I (r y) ∈ L'.U (k' I) := fun I => Set.mem_iInter.1 hk' I
  rw [mumfordBundle_pullback_composite_germ_iso h v r y j k aj ak, mumfordBundle_pullback_composite_germ_iso h v r y j' k' aj' ak']
  have e₀ := gm_pull_g (abelian₂ G L) β₂ (r ≫ sq) y j j' hj hj'
  have e₁ := gm_linComb L (lamφ G) lamε ((r ≫ sq) ≫ β₂) y (j PUnit.unit) (j' PUnit.unit) bj bj'
  have e₂ := gm_linComb L' (lamφ G') lamε r y k k' hk hk'
  erw [e₀, e₁, e₂]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [hv Y (r ≫ lamφ G' I) y (j PUnit.unit I) (j' PUnit.unit I) (k I) (k' I) (aj I) (aj' I) (ak I) (ak' I),
    Category.assoc, Category.assoc, Category.assoc, h, mul_zpow, mul_zpow, inv_zpow]

end Iso

theorem lamIso_comp_pull : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S₁ S₂ S₀ G _ _ B' _ G' _ _ T _ _ f₁ f₂ β' Φ φ β₂ β₂' L L' M gp' gΦ hsq hΦ hL hL' hM v w₁ hv hw₁
  have gp : IsGrpPullback G' G (f₂ ≫ f₁) φ := (IsGrpPullback.comp gΦ gp').congr rfl hΦ
  have e1 : GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ = GlobalTheory.HalfBC.sqOf gp := by
    apply pullback.hom_ext
    · show _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, hsq.1, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      show ((fst G' G').left ≫ Φ) ≫ β' = (fst G' G').left ≫ φ
      rw [Category.assoc, hΦ]
    · show _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, hsq.2, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      show ((snd G' G').left ≫ Φ) ≫ β' = (snd G' G').left ≫ φ
      rw [Category.assoc, hΦ]
  have h : ∀ I, GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ := fun I => by
    rw [← Category.assoc, e1, GlobalTheory.HalfBC.sqOf_lamφ]
  have hΛT : (abelian₂ T M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛG : ((abelian₂ G L).pull β₂).IsLB := LB.isLB_pull (DVR.linComb_isLB _ hL _ _) _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w, Tw⟩ := exists_comp hΛG w₁ (iso2 h v) ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv)) hΛT hΛ'
  refine ⟨w, (isGen_iff _).2 (Tw.pgen_comp hΛG ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := Tw Z p z (fun I => J (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (fun _ I => J₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (GlobalTheory.HalfBC.sqOf gΦ (p z))) ∈ L.U (J₁ ((p ≫ lamφ G' I) ≫ φ))
      rw [pt_eq h]; exact hJ₁ ((p ≫ lamφ G' I) ≫ φ)))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z (fun I => J ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂' ≫ lamφ T I))
      (fun _ I => J₁ ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂ ≫ lamφ G I))
    simp only [Category.assoc, h]
  · exact mumfordBundle_pullback_composite_germ_iso h v p z _ _ (fun I => hJ₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => hJ' (p ≫ lamφ G' I))

end GlobalTheory.LamPullComp

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodPull

open GlobalTheory.TChart

theorem gm_unitOn_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) (z : Sp R') :
    gm (𝟙 (Sp R')) z ⊤ (unitOn (Units.map f.toMonoidHom u)) =
      Units.map ((spMap f).stalkMap z).hom.toMonoidHom (gm (𝟙 (Sp R)) (spMap f z) ⊤ (unitOn u)) := by
  rw [← GlobalTheory.ConstFam.gm_comp_stalkMap (spMap f) (𝟙 _) z ⊤ trivial, Category.comp_id]
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have e := congrArg (fun g => g.hom (u : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [e]
  simp [Scheme.Hom.appTop]
  rfl

theorem periods_pull : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  intro n V _ _ D r e₀ o W _ _ _ T V₁ _ _ f₁ κ₁ e B' _ β₂ β₂' x w₁ q hf₁ hP V₂ _ _ f₂ fK I _ s ε hfK hq D' hD Φ gΦ hc w hw a b
  refine ⟨Units.map fK.toMonoidHom (q (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)),
    hq _ _, ?_⟩
  intro z J J' hJ hJ'
  set E := hD.xe.trans (e₀.symm.trans e.symm) with hE
  obtain ⟨κK, hκK, -⟩ := GlobalTheory.HalfBC.exists_kappa f₁ f₂ fK hfK hf₁
  let g₀ : (TK V₂).left ⟶ (TK V₁).left := spMap fK
  have sg : g₀ ≫ jK V₁ = jK V₂ ≫ spMap f₂ := GlobalTheory.HalfBC.gam_comm f₂ fK hfK
  choose J₁ hJ₀ using fun χ : (TK V₂).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have hJ₁ : Good D.P.L z J₁ := hJ₀
  have cE : ∀ a, (e.trans e₀) (E a) = hD.xe a := fun a => by simp [E]
  have t₁ := hP κK hκK (E a) (E b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
    (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
  rw [cE, cE] at t₁
  have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
  have n₁ : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
      (val (D.tau (hD.xe a) (hD.xe b)) κK (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
    Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κK g₀ z J₁ hJ₁).2.2.1 _)
  have h0 : g₀ ≫ (TK V₁).hom ≫ spMap κ₁ = (TK V₂).hom ≫ spMap (f₂.comp κ₁) := by
    show g₀ ≫ jK V₁ ≫ spMap κ₁ = jK V₂ ≫ spMap (f₂.comp κ₁)
    rw [← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
  have n₀ : val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b))
        ((TK V₁).hom ≫ spMap κ₁) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) := by
    rw [← h0]; exact Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ g₀ z J hJ).2.2.1 _)
  have nC : gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK V₁).left) (g₀ z) ⊤ (unitOn (q (E a) (E b)))) :=
    gm_unitOn_map fK _ z
  have ni : isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ =
      Units.map (g₀.stalkMap z).hom.toMonoidHom (isoVal w₁ (lift (toUnit (TK V₁) ≫ x (E a))
        (toUnit (TK V₁) ≫ x (E b))).left (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))) := by
    unfold isoVal
    simp only [Category.assoc]
    refine GlobalTheory.ConstFam.gm_comp_stalkMap g₀ _ z _ ?_ _
    exact ⟨mem_pull.2 (Set.mem_iInter.2 fun I => hJ _), mem_pull.2 (Set.mem_iInter.2 fun I => hJ₁ _)⟩
  have hr : 𝟙 _ ≫ jK V₂ ≫ spMap (f₂.comp f₁) = (g₀ ≫ κK) ≫ jK V := by
    rw [Category.id_comp, Category.assoc, hκK, ← Category.assoc, sg, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂]
  have tv := GlobalTheory.ArcPull.tau_val hD (g₀ ≫ κK) (𝟙 _) hr hJ₁ hJ' a b
  have A : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ κK) z J₁ =
      gm (𝟙 (TK V₂).left) z ⊤ (unitOn (Units.map fK.toMonoidHom (q (E a) (E b)))) *
        (isoVal w₁ (g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left) z J J₁ *
          val (T.τ₀ ((n : ℤ) • E a) ((n : ℤ) • E b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
    rw [n₁, t₂, nC, ni, n₀]
  have hx : ∀ χ, (toUnit (TK V₂) ≫ D'.c χ).left ≫ Φ = g₀ ≫ (toUnit (TK V₁) ≫ x (E χ)).left := fun χ => by
    show (jK V₂ ≫ (D'.c χ).left) ≫ Φ = spMap fK ≫ jK V₁ ≫ (x (E χ)).left
    rw [Category.assoc, hc, ← Category.assoc, ← sg, Category.assoc]
  have hPq : (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left ≫ GlobalTheory.HalfBC.sqOf gΦ =
      g₀ ≫ (lift (toUnit (TK V₁) ≫ x (E a)) (toUnit (TK V₁) ≫ x (E b))).left := by
    have sq1 : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    have sq2 : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.P.A D'.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.P.A D'.P.A)) (pushPt gΦ.1.w (snd D'.P.A D'.P.A)))
    apply pullback.hom_ext
    · show _ ≫ (fst B' B').left = _ ≫ (fst B' B').left
      rw [Category.assoc, sq1, ← Category.assoc, ← Over.comp_left, lift_fst,
        Category.assoc, ← Over.comp_left, lift_fst]
      exact hx a
    · show _ ≫ (snd B' B').left = _ ≫ (snd B' B').left
      rw [Category.assoc, sq2, ← Category.assoc, ← Over.comp_left, lift_snd,
        Category.assoc, ← Over.comp_left, lift_snd]
      exact hx b
  let h : ((TK V₂).left ⟶ D'.P.A.left) → ((TK V₂).left.presheaf.stalk z)ˣ :=
    fun q => gw hD.w q z (J₁ (q ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' q)
  have K := (hw _ (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
    (congrArg₂ (· * ·) (congrArg (fun q => isoVal w₁ q z J J₁) hPq)
      (prod_lam (DVR.cP D' (TK V₂) a) (DVR.cP D' (TK V₂) b) h))
  rw [← DVR.cPoint_add] at K
  have c₀ : ∀ χ, GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ D'.xK χ) = h (DVR.cP D' (TK V₂) χ).left := fun χ => by
    rw [Category.id_comp]; rfl
  have c₁ : GlobalTheory.ArcPull.om hD.w z J₁ J' (𝟙 _ ≫ (1 : TK V₂ ⟶ D'.P.A).left) = h (1 : TK V₂ ⟶ D'.P.A).left := by
    rw [Category.id_comp]; rfl
  rw [c₀, c₀, c₀, c₁] at tv
  rw [K]
  have F := tv.symm.trans A
  generalize val (D'.tau a b) (𝟙 _) z J' = X at F ⊢
  generalize h (DVR.cP D' (TK V₂) (a + b)).left = Y₀ at F ⊢
  generalize h (DVR.cP D' (TK V₂) a).left = Y₁ at F ⊢
  generalize h (DVR.cP D' (TK V₂) b).left = Y₂ at F ⊢
  generalize h (1 : TK V₂ ⟶ D'.P.A).left = Y₃ at F ⊢
  have F' := congrArg Additive.ofMul F
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at F' ⊢
  linear_combination (norm := abel) F'

end GlobalTheory.PeriodPull
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.MulExpand

open ReciprocityTheory.ChartRestriction.G.DVR (mulGen_isGen pullGen_isGen powGen_isGen val_pow cP comp_cP)
open GlobalTheory.UT

section
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}

abbrev prj (hD : IsPullDeg φ D D') : D'.P.A.left ⟶ D.P.A.left := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)

def om (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι) (q : Z ⟶ D'.P.A.left) : (Z.presheaf.stalk z)ˣ :=
  gw hD.w q z (J (q ≫ prj hD)) (J' q)

theorem pullB_val {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x}
    (H : PullB hD x b b') {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    sval b (r ≫ prj hD) z J = (∏ κ, om hD z J J' (r ≫ D'.famφB x κ) ^ DegPre.famε k κ).val * sval b' r z J' := by
  rw [sval_of b (r ≫ prj hD) z J (fun κ => J ((r ≫ D'.famφB x κ) ≫ prj hD)) (fun κ => by
    rw [Category.assoc r (prj hD), Category.assoc r _ (prj hD), ExpGTrans.famφB_pull hD x κ])]
  exact H Z r z _ _ (fun κ => hJ ((r ≫ D'.famφB x κ) ≫ prj hD)) (fun κ => hJ' (r ≫ D'.famφB x κ))

theorem prod_fam_unit (D : DegPre R) (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : (Sp R ⟶ D.P.A.left) → U) :
    ∏ κ, h (eSec D.P.A ≫ D.famφB α κ) ^ DegPre.famε k κ = h (eSec D.P.A) ^ (k : ℤ) := by
  have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by rw [Hom.one_def]; simp
  have a₀ : eSec D.P.A ≫ D.famφB α 0 = eSec D.P.A := Category.comp_id _
  have a₁ : eSec D.P.A ≫ D.famφB α 1 = eSec D.P.A ≫ D.famφB α 2 := congrArg (fun z => z.left)
    ((MonObj.comp_mul η[D.P.A] (𝟙 _) (cP D _ α)).trans
      ((congrArg (· * _) ((Category.comp_id _).trans e₁.symm)).trans (_root_.one_mul _)))
  have a₃ : eSec D.P.A ≫ D.famφB α 3 = eSec D.P.A := PullExp.eSec_comp_one
  rw [Fin.prod_univ_four, a₀, a₁, a₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, DegPre.famε, Matrix.cons_val]
  module

theorem mul_val_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') (m k k' : ℕ) (hk : k ≤ k') (x x' : D'.X) (hx : x' = m • x)
    (a : D'.P.A ⟶ D'.P.A) (ha : a = 𝟙 D'.P.A ^ m) (b : D.SecB k (hD.xe x)) (g : ∀ χ, D.SecB k' χ)
    (hM : MulSecB D m (hD.xe x) b (g (m • hD.xe x))) (b' : D'.SecB k x) (hb : PullB hD x b b')
    (c' : D'.SecB k' x') (hc : PullB hD x' (g (hD.xe x')) c')
    (eB : LB.Gen (LB.LinComb D'.P.L (Sum.elim (D'.famφB x') (fun i => a.left ≫ D'.famφB x i))
        (Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)))) (heB : eB.IsGen)
    (hn : ∀ y J, Good D'.P.L y J → val eB (eSec D'.P.A) y J = rigV D' (𝟙 _) y J ^ ((k' : ℤ) - k))
    (y : D'.P.A.left) (J') (hJ' : Good D'.P.L y J') :
    sval c' (𝟙 _) y J' = sval b' (𝟙 _ ≫ a.left) y J' * (val eB (𝟙 _) y J').val := by
  subst hx ha
  obtain ⟨u, hu, hun, hrel⟩ := hM
  have gp := pull_grp hD
  have hm : (mulA D'.P.A m).left ≫ prj hD = prj hD ≫ (mulA D.P.A m).left := GlobalTheory.ZH.TorsFrame.mulA_comm gp m
  have hφ : ∀ i, mulφB D' m x i ≫ prj hD = prj hD ≫ mulφB D m (hD.xe x) i := by
    rintro (i | i)
    · have := ExpGTrans.famφB_pull hD (m • x) i
      rw [map_nsmul] at this
      exact this
    · show ((mulA D'.P.A m).left ≫ D'.famφB x i) ≫ prj hD = prj hD ≫ (mulA D.P.A m).left ≫ D.famφB (hD.xe x) i
      rw [Category.assoc, ExpGTrans.famφB_pull hD x i, ← Category.assoc, hm, Category.assoc]
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (φ' := mulφB D' m x)
    (ε := mulεB k k') eB heB
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ i, om hD z J J' (r ≫ mulφB D' m x i) ^ mulεB k k' i) * val eB r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [om, Category.assoc]
  have hr : PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
    (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (prj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
  have he : eSec D'.P.A ≫ prj hD = spMap φ ≫ eSec D.P.A := hD.he
  have hem : eSec D'.P.A ≫ (mulA D'.P.A m).left = eSec D'.P.A := by
    have e₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = η[D'.P.A] := by rw [Hom.one_def]; simp
    refine (GlobalTheory.ZH.TorsFrame.comp_mulA η[D'.P.A] m).trans ?_
    rw [← e₁, one_pow, e₁]; rfl
  have key := gen_unique' D.P.isLB (φ := fun i => prj hD ≫ mulφB D m (hD.xe x) i) (ε := mulεB k k')
    (fun V _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ mulεB k k' i) (hφ i))
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 (pullGen_isGen _ _ _ _ hu (prj hD)) ht (fun y I hI => by
      choose I' hI' using fun χ : Sp R' ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have hI' : Good D'.P.L y I' := hI'
      have p : (∏ i, om hD y I I' (eSec D'.P.A ≫ mulφB D' m x i) ^ mulεB k k' i) =
          om hD y I I' (eSec D'.P.A) ^ ((k' : ℤ) - k) := by
        rw [Fintype.prod_sum_type]
        simp only [mulφB, mulεB, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, hem, zpow_neg, Finset.prod_inv_distrib]
        rw [prod_fam_unit D' _ _ (om hD y I I'), prod_fam_unit D' _ _ (om hD y I I'), zpow_sub]
      have q : rigV D (spMap φ) y I = om hD y I I' (eSec D'.P.A) * rigV D' (𝟙 _) y I' := by
        have := hr _ (𝟙 _) y (fun _ => I (eSec D'.P.A ≫ prj hD)) (fun _ => I' (eSec D'.P.A))
          (fun _ => hI (eSec D'.P.A ≫ prj hD)) (fun _ => hI' (eSec D'.P.A))
        rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at this
        rw [rigV, rigV, val_of (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig _ y I (fun _ => I (eSec D'.P.A ≫ prj hD)) (fun _ => by rw [he]),
          val_of (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig _ y I' (fun _ => I' (eSec D'.P.A)) (fun _ => by rw [Category.id_comp])]
        exact this
      have s := val_corr hI hun (spMap φ)
      rw [val_pull hI, val_pow] at s
      rw [val_pull hI, hv' _ _ y I I' hI hI', p, hn y I' hI', ← mul_zpow, ← q, he, s,
        show ((k' : ℤ) - k) = ((k' - k : ℕ) : ℤ) by omega, zpow_natCast]
      rfl)
  choose J hJ using fun χ : D'.P.A.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ
  have k₁ := (val_pull hJ u (prj hD) (𝟙 _)).symm.trans ((key _ (𝟙 _) y J hJ).trans (hv' _ _ y J J' hJ hJ'))
  have k₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 hrel _ (𝟙 _ ≫ prj hD) y J hJ
  have k₃ := pullB_val hc (𝟙 _) y hJ hJ'
  have k₄ := pullB_val hb (𝟙 _ ≫ (mulA D'.P.A m).left) y hJ hJ'
  have k₅ : sval (g (hD.xe (m • x))) (𝟙 _ ≫ prj hD) y J = sval (g (m • hD.xe x)) (𝟙 _ ≫ prj hD) y J :=
    congrArg (fun χ => sval (g χ) (𝟙 _ ≫ prj hD) y J) (map_nsmul hD.xe m x)
  rw [Category.assoc (𝟙 _) (prj hD), ← hm, ← Category.assoc (𝟙 _) _ (prj hD), k₄, k₁, ← k₅, k₃, Fintype.prod_sum_type] at k₂
  simp only [mulφB, mulεB, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, zpow_neg, Finset.prod_inv_distrib] at k₂
  refine (Units.mul_right_inj _).1 (k₂.trans ?_)
  generalize (∏ κ, om hD y J J' (𝟙 _ ≫ D'.famφB (m • x) κ) ^ DegPre.famε k' κ) = P
  generalize (∏ κ, om hD y J J' ((𝟙 _ ≫ (mulA D'.P.A m).left) ≫ D'.famφB x κ) ^ DegPre.famε k κ) = Q
  rw [Units.val_mul, Units.val_mul]
  linear_combination (P.val * sval b' (𝟙 _ ≫ (mulA D'.P.A m).left) y J' * (val eB (𝟙 _) y J').val) * Q.mul_inv

end

theorem expand : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ), Odd m →
    ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G →
    ∀ (σ' : H0 T.U.LG.L 1) (f' : ∀ x, T.D'.toPre.SecB 1 x), (∀ x, PullB T.hD x (F₁.f (T.hD.xe x)) (f' x)) →
    (∀ e, T.U.ExpandsAt e 1 σ' f') →
    ∀ (f'' : ∀ x, T.D'.toPre.SecB (m ^ 2) x), (∀ x, PullB T.hD x (G.f (T.hD.xe x)) (f'' x)) →
    ∃ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (σ'' : H0 T.U.LG.L (m ^ 2)), uG.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
        sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) ∧
      ∀ e, T.U.ExpandsAt e (m ^ 2) σ'' f'' := by
  intro R _ _ _ _ D C W _ _ _ T m hm F₁ G hFG σ' f' hf' hσ' f'' hf''
  obtain ⟨hd, hV, hz⟩ := T.cdvr
  have hL := GlobalTheory.firstFiveLaws
  have hI : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have hGF := hL.1.globalFns
  have hG : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨E, hEG, -, hEB, hEh, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL W (maximalIdeal W) hI T.D' T.A T.G hG T.U).1 m
  have := E.homG
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hsm : Function.Injective fun χ : T.D'.toPre.X => m • χ := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
    exact smul_right_injective T.D'.toPre.X (Int.natCast_ne_zero.2 hm0) h'
  have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
  obtain ⟨β₀, hβ₀⟩ := ThetaSum.exists_gen_pow T.U.LG T.U.cubG T.U.symG T.U.symG_gen m E.aG hEG
  obtain ⟨β, hβ, hβ'⟩ := PullExp.exists_normalised T.U.LG.isLB E.aG _ _ β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL W (maximalIdeal W) hI T.D' T.A T.G hG T.U E (m ^ 2) 1 β hβ hβ'
  obtain ⟨σ₃, f₃, p₁, p₂, p₃, p₄⟩ := GlobalTheory.T.pullback_section_endomorphism_expansion W (maximalIdeal W) T.D' T.A T.G T.U.toUnifPre E hinj (m ^ 2) 1 β hβ κ₀
    hκ₀.1 hrel σ' f' hσ'
  have hf : f₃ = f'' := funext fun b => ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext (sec_ext_val T.D'.toPre.P.isLB fun y J hJ => by
    by_cases hb : b ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      obtain ⟨eB, heB, hvB⟩ := NsmulPull.gen_shape T.D'.toPre E.aB (m ^ 2) 1 hm2 (E.h χ) χ κ₀ hκ₀.1 (E.u χ) (E.u_norm χ).1
      have h := mul_val_pull hGF T.hD m 1 (m ^ 2) hm2 χ (E.h χ) (hEh χ) E.aB hEB _ G.f (hFG.1 _) _ (hf' χ) _ (hf'' _) eB heB
        (fun y J hJ => by
          have a := val_corr hJ hκ₀.2 (𝟙 _)
          have a' := val_corr hJ (E.u_norm χ).2 (𝟙 _)
          rw [val_pull hJ, Category.id_comp, val_one] at a a'
          rw [hvB _ _ y J hJ, a, a', _root_.one_mul, _root_.mul_one]
          exact congrArg (fun q => rigV T.D'.toPre q y J ^ _) (Over.w η[T.D'.toPre.P.A])) y J hJ
      rw [h, hvB _ _ y J hJ]
      exact p₃ χ _ _ y J hJ
    · choose J₀ hJ₀ using fun χ : T.D'.toPre.P.A.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
      have h := pullB_val (hf'' b) (𝟙 _) y hJ₀ hJ
      rw [GlobalTheory.PullComp.sval_eq_zero _ (hFG.2 _ fun χ e => hb ⟨T.hD.xe.symm χ, by
        rw [hEh, ← map_nsmul, ← e, AddEquiv.symm_apply_apply]⟩)] at h
      rw [GlobalTheory.PullComp.sval_eq_zero _ (p₄ b hb), (Units.mul_right_eq_zero _).1 h.symm])
  subst hf
  let ρ := LB.pullGen T.U.LG.L (K := PUnit) (fun _ => eSec T.G) (fun _ => 1) T.U.LG.rig T.G.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ T.U.LG.rigGen _
  obtain ⟨uG, huG, hv⟩ := exists_gen T.U.LG.isLB (K' := Fin 2) (φ' := ![𝟙 T.G.left, (mulA T.G m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]) (fun U _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_three, Fintype.prod_unique]
      show h (𝟙 _) ^ ((m ^ 2 : ℕ) : ℤ) * h E.aG.left ^ (-((1 : ℕ) : ℤ)) * h (1 : T.G ⟶ T.G).left ^ (((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)) *
        h (T.G.hom ≫ eSec T.G) ^ (((m ^ 2 - 1 : ℕ) : ℤ) * 1) = h (𝟙 _) ^ ((m ^ 2 : ℕ) : ℤ) * h (mulA T.G m).left ^ (-((1 : ℕ) : ℤ))
      rw [hEG, GlobalTheory.ZH.TorsFrame.one_left, _root_.mul_assoc, ← zpow_add, Nat.cast_sub hm2]
      simp)
    (LB.mulGen _ _ _ _ _ β (GeneratorPullback.powGen _ _ _ ρ (m ^ 2 - 1))) (mulGen_isGen _ _ _ _ _ _ _ hβ (powGen_isGen _ _ _ _ hρ _))
  refine ⟨uG, σ₃, huG, fun Z r z J hJ => ?_, p₁⟩
  rw [p₂ Z r z J hJ, hv _ _ z J hJ, val_mul hJ, val_pow, val_pull hJ, Category.comp_id, mul_comm,
    show r ≫ E.aG.left = r ≫ (mulA T.G m).left by rw [hEG],
    show (((m ^ 2 : ℕ) : ℤ) - (1 : ℕ)) = ((m ^ 2 - 1 : ℕ) : ℤ) by omega, zpow_natCast]

end GlobalTheory.Mum.MulExpand
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisations_translation_period_maps_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ) := by
  first | exact @GlobalTheory.MumCmp.TranslC.c_correspond | exact GlobalTheory.MumCmp.TranslC.c_correspond | (intros; apply GlobalTheory.MumCmp.TranslC.c_correspond <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mumfordBundleIso_comp_group_pullback_iso : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  first | exact @GlobalTheory.LamPullComp.lamIso_comp_pull | exact GlobalTheory.LamPullComp.lamIso_comp_pull | (intros; apply GlobalTheory.LamPullComp.lamIso_comp_pull <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.period_relation_pullback_monomial_constants : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.X) {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (f₁ : V →+* V₁) (κ₁ : W →+* V₁) (e : (Fin T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β₂ : (G2 B').left ⟶ (G2 D.P.A).left) (β₂' : (G2 B').left ⟶ (G2 T.B).left) (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (w₁ : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ), Function.Injective f₁ → PeriodRel D T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D') (Φ : D'.P.A.left ⟶ B'.left) (gΦ : IsGrpPullback D'.P.A B' (spMap f₂) Φ), (∀ a, (D'.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left) → ∀ (w : LB.Iso (abelian₂ D'.P.A D'.P.L) ((abelian₂ T.B T.M.L).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂'))), (∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D'.P.A).left) (z : Z) (J : (Z ⟶ T.B.left) → T.M.L.ι) (J₁ : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good T.M.L z J → Good D.P.L z J₁ → Good D'.P.L z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw hD.w (p ≫ lamφ D'.P.A I) z (J₁ ((p ≫ lamφ D'.P.A I) ≫ GlobalTheory.PsiEvenPull.proj hD)) (J' (p ≫ lamφ D'.P.A I)) ^ lamε I) → ∀ a b : D'.X, ∃ k : (FractionRing V₂)ˣ, (k : FractionRing V₂) = ∏ i, algebraMap V₂ (FractionRing V₂) (s i) ^ ((n : ℤ) * ε i (hD.xe.trans (e₀.symm.trans e.symm) a) (hD.xe.trans (e₀.symm.trans e.symm) b)) ∧ ∀ z J J', Good T.M.L z J → Good D'.P.L z J' → val (D'.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V₂).left) z ⊤ (unitOn k) * (lamVal w (lift (toUnit (TK V₂) ≫ D'.c a) (toUnit (TK V₂) ≫ D'.c b)).left z J J' * val (T.τ₀ ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) a) ((n : ℤ) • hD.xe.trans (e₀.symm.trans e.symm) b)) ((TK V₂).hom ≫ spMap (f₂.comp κ₁)) z J) := by
  first | exact @GlobalTheory.PeriodPull.periods_pull | exact GlobalTheory.PeriodPull.periods_pull | (intros; apply GlobalTheory.PeriodPull.periods_pull <;> assumption)

end
end
