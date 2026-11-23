module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartBoundaryEquations
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3294
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotent_image_nDividedPoint_galoisConj_equiv : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p p' : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  first | exact @GlobalTheory.Mum.GalFixQ.eImage_equiv_conj | exact GlobalTheory.Mum.GalFixQ.eImage_equiv_conj | (intros; apply GlobalTheory.Mum.GalFixQ.eImage_equiv_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TautGt


open GlobalTheory.TChart.GensFrom in
theorem exists_gen_at {W V : Type} [CommRing W] [CommRing V] {BT : Over (Sp W)} [GrpObj BT] [IsCommMonObj BT]
    {BQ : Over (Sp V)} [GrpObj BQ] [IsCommMonObj BQ] {MT : LB BT.left} {MQ : LB BQ.left} (hMT : MT.IsLB) (hMQ : MQ.IsLB)
    (iw : W →+* V) {β : BQ.left ⟶ BT.left} {β₂ : (G2 BQ).left ⟶ (G2 BT).left} (hsq : IsSquare β β₂)
    (w : LB.Iso (abelian₂ BQ MQ) ((abelian₂ BT MT).pull β₂)) (hw : w.IsGen) {T' : Over (Sp V)} (x y : T' ⟶ BQ)
    (x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ BT) (hx : x.left ≫ β = T'.hom ≫ spMap iw ≫ x₀.left)
    (hy : y.left ≫ β = T'.hom ≫ spMap iw ≫ y₀.left)
    (τ₁ : LB.Gen (LB.LinComb MT (lamPts x₀ y₀) negε)) (h₁ : τ₁.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb MQ (lamPts x y) negε), τ.IsGen ∧ ∀ (z : T'.left) J J',
      Good MT z J → Good MQ z J' →
        val τ (𝟙 _) z J' = lamVal w (lift x y).left z J J' * val τ₁ (T'.hom ≫ spMap iw) z J := by
  have hψ : (lift x y).left ≫ β₂ = (T'.hom ≫ spMap iw) ≫ (lift x₀ y₀).left := by
    apply pullback.hom_ext
    · show ((lift x y).left ≫ β₂) ≫ (fst BT BT).left = ((T'.hom ≫ spMap iw) ≫ (lift x₀ y₀).left) ≫ (fst BT BT).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
        lift_fst, Category.assoc]
    · show ((lift x y).left ≫ β₂) ≫ (snd BT BT).left = ((T'.hom ≫ spMap iw) ≫ (lift x₀ y₀).left) ≫ (snd BT BT).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
        lift_snd, Category.assoc]
  obtain ⟨t₂, ht₂, hv₂⟩ := exists_gen hMT
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift x₀ y₀).left ≫ (psum BT (x2 BT) I.down).left)
    (ε' := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (by
      intro U _ H
      rw [lam_form x₀ y₀ U H, ← Finset.prod_inv_distrib]
      simp only [zpow_neg]) (LB.invGen MT _ _ τ₁) (DVR.invGen_isGen _ _ _ _ h₁)
  let t₃ : LB.Gen ((abelian₂ BT MT).pull (lift x₀ y₀).left) := GlobalTheory.UU.unflatGen t₂
  have ht₃ : t₃.IsGen := GlobalTheory.UU.unflatGen_isGen ht₂
  obtain ⟨a, ha, hva⟩ := GlobalTheory.ArcPull.exists_down_om hw (LB.isLB_linComb hMT _ _) (LB.isLB_linComb hMQ _ _)
    (φ' := fun _ : PUnit => (lift x y).left) (φ := fun _ => (lift x₀ y₀).left) (ε := fun _ => 1) (T'.hom ≫ spMap iw)
    (fun _ => hψ) t₃ ht₃
  obtain ⟨τ, hτ, hvτ⟩ := exists_gen hMQ
    (φ := fun I : ULift.{0} (Finset (Fin 2)) => (lift x y).left ≫ (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => -((-1 : ℤ) ^ (2 - I.down.card))) (φ' := lamPts x y) (ε' := negε) (by
      intro U _ H
      simp only [zpow_neg, Finset.prod_inv_distrib]
      rw [lam_form x y U H, inv_inv]) (LB.invGen MQ _ _ (GlobalTheory.UU.flatGen a))
    (DVR.invGen_isGen _ _ _ _ (GlobalTheory.UU.flatGen_isGen ha))
  refine ⟨τ, hτ, fun z J J' hJ hJ' => ?_⟩
  have e1 := hvτ _ (𝟙 T'.left) z J' hJ'
  have e5 := val_flatGen (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x y).left) a (𝟙 T'.left) z hJ'
  rw [val_inv, e5] at e1
  have e6 : val t₃ (𝟙 T'.left ≫ T'.hom ≫ spMap iw) z
      (fun ψ (k : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum BT (x2 BT) k.down).left)) =
      val t₂ (𝟙 T'.left ≫ T'.hom ≫ spMap iw) z J := val_unflatGen (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x₀ y₀).left) t₂ (𝟙 T'.left ≫ T'.hom ≫ spMap iw) z hJ
  have e2 := hva _ (𝟙 T'.left) z _ _
    (good_linComb (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ)
    (good_linComb (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ')
  rw [e6, hv₂ _ _ z J hJ, val_inv, Fintype.prod_unique, zpow_one, om_lam] at e2
  simp only [Category.id_comp] at e1 e2
  rw [e1, ← inv_inv (val τ₁ (T'.hom ≫ spMap iw) z J), e2, _root_.mul_inv, _root_.mul_inv_cancel_left]
  rfl

end GlobalTheory.TautGt

noncomputable section
namespace GlobalTheory.TautGt

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen t c) r z J = gm r z ⊤ c * val t r z J :=
  gm_scaleGen t c r z _ (hJ.mem φ r)

theorem mult_alg {G : Type} [CommGroup G] (u₁ u₂ L L₁ L₂ t t₁ t₂ cD cT : G) (h1 : L * cD = L₁ * L₂ * cT)
    (h2 : t * cT = t₁ * t₂) : u₁ * u₂ * (L * t) * cD = u₁ * (L₁ * t₁) * (u₂ * (L₂ * t₂)) := by
  rw [eq_mul_inv_of_mul_eq h1, eq_mul_inv_of_mul_eq h2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def kU {V : Type} [CommRing V] [IsDomain V] {r : ℕ} {I : Type} [Fintype I] (s : I → V) (hs : ∀ i, s i ≠ 0)
    (ε : I → LinearMap.BilinForm ℤ (Fin r → ℤ)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (x a : Fin r → ℤ) : Fˣ :=
  Units.mk0 (∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s i)) ^ ε i x a)
    (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ((map_ne_zero _).2
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i))))

theorem kU_add {V : Type} [CommRing V] [IsDomain V] {r : ℕ} {I : Type} [Fintype I] (s : I → V) (hs : ∀ i, s i ≠ 0)
    (ε : I → LinearMap.BilinForm ℤ (Fin r → ℤ)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (x x' a : Fin r → ℤ) : kU s hs ε F (x + x') a = kU s hs ε F x a * kU s hs ε F x' a := by
  apply Units.ext
  simp only [kU, Units.val_mk0, Units.val_mul, map_add (f := _), LinearMap.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => zpow_add₀ ((map_ne_zero _).2
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i))) _ _

theorem kU_zero {V : Type} [CommRing V] [IsDomain V] {r : ℕ} {I : Type} [Fintype I] (s : I → V) (hs : ∀ i, s i ≠ 0)
    (ε : I → LinearMap.BilinForm ℤ (Fin r → ℤ)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (a : Fin r → ℤ) : kU s hs ε F 0 a = 1 := by
  apply Units.ext
  simp [kU]

end GlobalTheory.TautGt


open GlobalTheory.TautGt in
theorem GlobalTheory.TInj.exists_tautPt : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → (∀ i, s i ≠ 0) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ), ∃ g : GtPtF D F, TautPt T ω s ε n D e β ββ w F a g := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF hs F _ _ a
  have hF' := hF
  obtain ⟨hpb, hsq, hw, hc, -⟩ := hF
  have hι : (toUnit (TF (R := V) F)).left = (TF (R := V) F).hom := rfl
  let bL : (TF (R := V) F).left ⟶ D.P.A.left :=
    hpb.1.lift ((TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left) (TF (R := V) F).hom (by
      rw [Category.assoc, Category.assoc, Over.w (T.c₀ a)]; rfl)
  let b : TF (R := V) F ⟶ D.P.A := Over.homMk bL (hpb.1.lift_snd _ _ _)
  have hb : b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left := hpb.1.lift_fst _ _ _
  have hx : ∀ χ : D.X, (DegPre.cF D F χ).left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ ((n : ℤ) • e χ)).left :=
    fun χ => by
      show ((toUnit (TF (R := V) F)).left ≫ (D.c χ).left) ≫ β = _
      rw [Category.assoc, hc χ, hι]
  have key := fun χ : D.X => exists_gen_at T.M.isLB D.P.isLB ω hsq w hw (DegPre.cF D F χ) b
    (T.c₀ ((n : ℤ) • e χ)) (T.c₀ a) (hx χ) hb (T.τ₀ _ _) (T.τ₀_gen _ _)
  choose τ hτg hτv using key
  have hval : ∀ χ z J J', Good T.M.L z J → Good D.P.L z J' →
      val (scaleGen (τ χ) (unitOn (kU s hs ε F (e χ) a))) (𝟙 _) z J' =
        gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn (kU s hs ε F (e χ) a)) *
          (lamVal w (lift (DegPre.cF D F χ) b).left z J J' *
            val (T.τ₀ ((n : ℤ) • e χ) a) ((TF (R := V) F).hom ≫ spMap ω) z J) := fun χ z J J' hJ hJ' => by
    rw [val_scaleGen _ _ _ _ hJ', hτv χ z J J' hJ hJ']
  have hτ0 : ∀ y J, Good T.M.L y J → val (T.τ₀ 0 a) ((TF (R := V) F).hom ≫ spMap ω) y J = 1 := fun y J hJ => by
    have C : LB.Gen.Corr T.M.L _ _ _ _ (T.τ₀ 0 a) (LB.oneGen T.M.L) := corr_of_val T.M.isLB fun y J hJ =>
      (show val (T.τ₀ 0 a) (𝟙 _) y J = 1 by
        have h := T.τ₀_add 0 0 a y J hJ
        have f : cubV T.cub y J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1 := by
          rw [TautBase.c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
        rw [f, _root_.mul_one, add_zero] at h
        exact mul_eq_left.1 h.symm).trans (val_one _).symm
    exact (val_corr hJ C _).trans (val_one _)
  have hc0 : D.c 0 = 1 := mul_eq_left.1 ((D.c_add 0 0).symm.trans (by rw [add_zero]))
  have hcF0 : DegPre.cF D F 0 = 1 := by
    show toUnit _ ≫ D.c 0 = 1
    rw [hc0, MonObj.comp_one]
  have hcF : ∀ χ χ', DegPre.cF D F (χ + χ') = DegPre.cF D F χ * DegPre.cF D F χ' := fun χ χ' => by
    show toUnit _ ≫ D.c (χ + χ') = _
    rw [D.c_add]
    exact MonObj.comp_mul _ _ _
  have unitOn_mul : ∀ k k' : Fˣ, unitOn (k * k') = unitOn k * unitOn k' := fun k k' => map_mul _ _ _
  refine ⟨{ b := b
            s := fun χ => scaleGen (τ χ) (unitOn (kU s hs ε F (e χ) a))
            isGen := fun χ => scaleGen_isGen D.P.isLB _ (hτg χ) _
            s_zero := ?_
            mult := ?_ }, hb, fun χ => ⟨kU s hs ε F (e χ) a, rfl, fun z J J' hJ hJ' => hval χ z J J' hJ hJ'⟩⟩
  · refine corr_of_val D.P.isLB fun y J' hJ' => ?_
    choose J hJ using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ y)
    refine (hval 0 y J J' hJ hJ').trans (Eq.trans ?_ (val_one _).symm)
    rw [map_zero e, kU_zero, smul_zero, hτ0 y J hJ, hcF0,
      (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D ω s e β ββ w hB hF' (TF (R := V) F) b y J J' hJ hJ').1,
      show unitOn (1 : Fˣ) = 1 from map_one _, map_one, _root_.mul_one, _root_.mul_one]
  · intro χ χ'
    refine corr_of_val D.P.isLB fun y J' hJ' => ?_
    choose J hJ using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ y)
    have hcub : val (DegPre.cubAt D F (DegPre.cF D F χ) (DegPre.cF D F χ') b) (𝟙 _) y J' =
        cubV D.cub y J' (DegPre.cF D F χ) (DegPre.cF D F χ') b := by
      unfold DegPre.cubAt
      refine (val_pull hJ' _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    let r := (TF (R := V) F).hom ≫ spMap ω
    let ρ := toUnit (Over.mk r)
    have W1 := (GlobalTheory.T.mumfordBundleIso_additive_cubicalStructure T ε n V D ω s e β ββ w hB hF' (TF (R := V) F) (DegPre.cF D F χ) (DegPre.cF D F χ') b
      (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ ((n : ℤ) • e χ')) (ρ ≫ T.c₀ a) ((hx χ).trans (Category.assoc _ _ _).symm)
      ((hx χ').trans (Category.assoc _ _ _).symm) (hb.trans (Category.assoc _ _ _).symm) y J J' hJ hJ').1
    have T1 : val (T.τ₀ ((n : ℤ) • e χ + (n : ℤ) • e χ') a) r y J *
        @id ((TF (R := V) F).left.presheaf.stalk y)ˣ
          (cubV T.cub y J (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ ((n : ℤ) • e χ')) (ρ ≫ T.c₀ a)) =
        val (T.τ₀ ((n : ℤ) • e χ) a) r y J * val (T.τ₀ ((n : ℤ) • e χ') a) r y J := by
      have C : LB.Gen.Corr T.M.L _ _ _ _
          (LB.mulGen T.M.L _ _ _ _ (T.τ₀ ((n : ℤ) • e χ + (n : ℤ) • e χ') a)
            (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t
              (lift (T.c₀ ((n : ℤ) • e χ)) (lift (T.c₀ ((n : ℤ) • e χ')) (T.c₀ a))).left))
          (LB.mulGen T.M.L _ _ _ _ (T.τ₀ ((n : ℤ) • e χ) a) (T.τ₀ ((n : ℤ) • e χ') a)) :=
        corr_of_val T.M.isLB fun y J hJ => by
          refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
          refine (congrArg (_ * ·) ((val_pull hJ _ _ _).trans ?_)).trans (T.τ₀_add _ _ a y J hJ)
          rw [Category.id_comp]
          rfl
      have h1 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ C r).trans (val_mul hJ _ _ _))
      refine Eq.trans ?_ h1
      exact congrArg (_ * ·) (val_cub T.cub ρ hJ _ _ _).symm
    refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
    refine (congrArg₂ (· * ·) (hval (χ + χ') y J J' hJ hJ') hcub).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (hval χ y J J' hJ hJ') (hval χ' y J J' hJ hJ')).symm)
    rw [hcF, map_add e, kU_add, smul_add, unitOn_mul, map_mul]
    exact mult_alg _ _ _ _ _ _ _ _ _ _ W1 T1
end
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_qkPoint_extension_of_divided_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ p : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', p.y = 0 → ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) p₀ p := by
  first | exact @GlobalTheory.DivTorsRat.exists_qkExt_of_divFrom | exact GlobalTheory.DivTorsRat.exists_qkExt_of_divFrom | (intros; apply GlobalTheory.DivTorsRat.exists_qkExt_of_divFrom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tautologicalChart_boundary_equations : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧ ∃ a : Fin C.m → ℕ, (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i} := by
  first | exact @GlobalTheory.UCanonBd.boundary_eq | exact GlobalTheory.UCanonBd.boundary_eq | (intros; apply GlobalTheory.UCanonBd.boundary_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.subsingleton_characterGroup_of_goodReduction_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X := by
  first | exact @GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset | exact GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset | (intros; apply GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTranslW

theorem lift_commutes_translation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∃ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl ∧ ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (W : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, W)), dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ W) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app W).hom f) = pbT T₀ (dl W f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ W)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  letI := H.starRing
  intro Y n' v' dd hinv D q hq h hB hdef hΘ ρ hρ A₀ _ m₀ hm₀
  let φ : ChartRing k m d →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ
  have hφΘ : ∀ a b, φ (h.Θ a b) = 0 := fun a b => by
    have h0 : MvPowerSeries.constantCoeff (h.Θ a b) = 0 := by
      by_contra hne
      exact hΘ a b (MvPowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne))
    simp [φ, hρ, h0]
  obtain ⟨dl, hdl, hdesc⟩ := GlobalTheory.Heat.AbConst.exists_locDerK_desc Y h (fun a => (hinv a).1) hB φ hφΘ A₀.hom m₀ hm₀.1.w
  have hD : (fun r => φ (D r)) = fun r => (ρ r).snd := funext fun r => by simp [φ, hρ]
  rw [hD] at hdl
  refine ⟨dl, hdl, fun y T₀ hT₀ hT₀' W f => ?_⟩
  obtain ⟨N, hN, Ix, U, M, r, hU, hUa, hgen, hrat⟩ := GlobalTheory.Heat.Gens.gens P.D.toPre
  refine GlobalTheory.Heat.DerComm.comm_of_gen A₀.hom P.D.toPre.P.A.hom m₀ _ dl hdl _ T₀ hT₀ hT₀' (Over.w _) Ix U M r hU hUa hgen (fun i j => ?_) W f
  obtain ⟨σ, σ', hσ⟩ := hrat i j
  exact GlobalTheory.T.closedFibreLift_comm_translation_section_ratios E H k m d t P gam hmon hli hab Y n' v' dd hinv D q hq h hB hdef hΘ ρ hρ A₀ _ m₀ hm₀ dl hdl hdesc y T₀ hT₀
    hT₀' N hN σ σ' (U i) (r i j) hσ

end GlobalTheory.HeatTranslW
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_conjugate_heatOperator_periodShift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∀ mu : Dd.toPre.X, ∃ (h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X →+ R) (π π' : R), IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) (σ₁ σ₁' : Dd.toPre.SecB k (α + k • mu)), 1 ≤ k → ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → TActs Y h k (α + k • mu) σ₁ σ₁' → ∃ σ'' : Dd.toPre.SecB k α, TActs Y h' k α σ σ'' ∧ ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  first | exact @GlobalTheory.HeatDefect.exists_conj_shift | exact GlobalTheory.HeatDefect.exists_conj_shift | (intros; apply GlobalTheory.HeatDefect.exists_conj_shift <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatUniq

theorem exists_affine_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (ℓ : Q.X →+ R) (π π' : R), ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π')) * sval σ x.left z J := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hdd D h' h hb' hb hΘ' hu'
  have hΘ : h.Θ = h'.Θ := hΘ'.symm
  have hu : h.u = h'.u := hu'.symm
  obtain ⟨e, π, π', hT, hG⟩ := GlobalTheory.T.torusInvariant_heatOperators_difference_global R Q O oa Y n v dd hdd D h h' hb hb' hΘ hu
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.exists_addHom_invariantField_kills_weightZero R Q O oa Y n v dd hdd e hT
  refine ⟨ℓ, π, π', ?_⟩
  intro k α σ σ'' σ' h1' h1 T x z J hJ
  refine GlobalTheory.T.heat_operator_fourier_term_values_eq_of_local_identity R Q O oa Y n v dd hdd D h h' hb hb'
    (fun k α => 2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') ?_ k α σ σ' σ'' h1 h1' T x z J hJ
  intro i i' k α V hV f hf
  obtain ⟨h2d, h3, h4⟩ := hG i i' _ hV
  simp only [dlg] at h2d h3 h4
  have hle : Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) := fun pt hpt =>
    ⟨h.le i (hV hpt).1, h'.le i' (hV hpt).2⟩
  have hg : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) *
      pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ V) = 1 := by
    unfold pbT
    rw [dite_eq_left hle, dite_eq_left hle, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have mono : ∀ (δ : Fld Y.H.left) {W₁ W₂ : Y.H.left.Opens}, W₁ ≤ W₂ → IsField W₂ δ → IsField W₁ δ :=
    fun δ W₁ W₂ hle H => ⟨fun W hW => H.1 W (hW.trans hle), fun W hW => H.2.1 W (hW.trans hle),
      fun W W' hh hW => H.2.2 W W' hh (hW.trans hle)⟩
  rw [GlobalTheory.T.heatOperator_conj_unitPow_corrections R Y.H n dd h.Θ h.symm h.u (h.d i) (h.W i) (h.W i) _ (h.p i) (h.p' i) k _ _ hg (hV.trans inf_le_left)
    (h.lift i).1 (fun a => mono _ le_top (hdd a).1) f]
  congr 1
  have hc : constFn Y.H.hom (Y.q.left ⁻¹ᵁ V) (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') =
      2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ (ℓ α) +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * constFn Y.H.hom _ π +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ π' := by
    simp only [constFn, map_add (f := _), map_mul, map_pow, map_natCast, map_ofNat]
  simp only [hc]
  have hl := hℓ α V f hf
  unfold op
  rw [← hΘ, ← hu]
  linear_combination (2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V))) * h2d f + (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * f * h3 +
    (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * f * h4 + 2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * hl

end GlobalTheory.HeatUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_linked_thetaSystem_regular_monomialFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : V →+* V₁) (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (r : Fin Cm.m → V₁), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ GlobalTheory.GSep.ULink C X₁ act u π ∧ IsCov C π z₁ ζ ∧ IsCN V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ev₁ ∧ GlobalTheory.GSep.RegAt X₁ z₁ ev₁ ∧ spMap ev₁ ≫ ζ = spMap ρ₁ ≫ ξ ∧ ∀ k, r k ^ 2 = ρ₁ (Cm.s k) := by
  first | exact @GlobalTheory.GSep.exists_uLink_regAt_chart | exact GlobalTheory.GSep.exists_uLink_regAt_chart | (intros; apply GlobalTheory.GSep.exists_uLink_regAt_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_thetaMember_injective_evaluation : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Function.Injective ev ∧ Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  first | exact @GlobalTheory.GSep.exists_gMem_injective | exact GlobalTheory.GSep.exists_gMem_injective | (intros; apply GlobalTheory.GSep.exists_gMem_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaMember_dividing_label_class_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  first | exact @GlobalTheory.GSep.DivInt.label_zero_of_mem_supI | exact GlobalTheory.GSep.DivInt.label_zero_of_mem_supI | (intros; apply GlobalTheory.GSep.DivInt.label_zero_of_mem_supI <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.torsor_trivial_strict_henselisation_origin : GlobalTheory.LocAcyc.KeyOrigin := by
  first | (exact @GlobalTheory.KeyOriginCut.keyOrigin) | (exact GlobalTheory.KeyOriginCut.keyOrigin) | (intros; apply GlobalTheory.KeyOriginCut.keyOrigin  <;> assumption)
end
