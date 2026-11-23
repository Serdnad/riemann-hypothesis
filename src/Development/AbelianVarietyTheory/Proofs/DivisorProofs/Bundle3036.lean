module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.EventuallyEvalNegOfCoeffNeg
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.GensFrom

theorem lam_form {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B) (U : Type)
    [CommGroup U] (H : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), H ((lift x y).left ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (∏ k, H (lamPts x y k) ^ negε k)⁻¹ := by
  have p : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B (x2 B) I).left = (psum B ![x, y] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I).trans (by
      congr 1; funext i; fin_cases i <;> simp [x2, preHom]))
  simp only [p]
  rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    Fin.prod_univ_four]
  have q0 : psum B ![x, y] ∅ = 1 := rfl
  have q1 : psum B ![x, y] {0} = x := _root_.mul_one x
  have q2 : psum B ![x, y] {1} = y := _root_.mul_one y
  have q3 : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  simp [q0, q1, q2, q3, lamPts, negε]
  generalize H (x * y).left = A, H x.left = A₁, H y.left = A₂, H (1 : T ⟶ B).left = A₀
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem good_linComb {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good (LB.LinComb L φ ε) z (fun ψ k => J (ψ ≫ φ k)) := fun ψ => hJ.mem φ ψ

theorem val_flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.flatGen u) r z J = val u r z (fun ψ k => J (ψ ≫ φ k)) := by
  exact (gm_res r z _ (hJ.mem (fun k => F ≫ φ k) r) _).trans
    (val_of u r z _ (fun _ k => J (r ≫ F ≫ φ k)) (fun _ => funext fun k => by simp only [Category.assoc])).symm

theorem val_unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.unflatGen v) r z (fun ψ k => J (ψ ≫ φ k)) = val v r z J := by
  exact (gm_res r z _ ((good_linComb (φ := φ) (ε := ε) hJ).mem (fun _ : PUnit => F) r) _).trans
    (val_of v r z J (fun k => J ((r ≫ F) ≫ φ k)) (fun k => by simp only [Category.assoc])).symm

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem om_lam {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    GlobalTheory.ArcPull.om w z (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum B (x2 B) I.down).left))
      (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J' (ψ ≫ (psum B' (x2 B') I.down).left)) p = lamVal w p z J J' := by
  have H : ∀ i i' : (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).ι, i = i' →
      gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i) (w.s i) =
        gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i') (w.s i') := by
    rintro _ _ rfl; rfl
  unfold GlobalTheory.ArcPull.om Geo.Tor.gw lamVal
  refine H (fun _ (I : ULift.{0} (Finset (Fin 2))) => J ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ (I : ULift.{0} (Finset (Fin 2))) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left)) (Prod.ext ?_ rfl)
  funext _ I
  exact congrArg J (Category.assoc _ _ _)

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem exists_gen_of_base {W V : Type} [CommRing W] [CommRing V] {BT : Over (Sp W)} [GrpObj BT] [IsCommMonObj BT]
    {BQ : Over (Sp V)} [GrpObj BQ] [IsCommMonObj BQ] {MT : LB BT.left} {MQ : LB BQ.left} (hMT : MT.IsLB) (hMQ : MQ.IsLB)
    (iw : W →+* V) {β : BQ.left ⟶ BT.left} {β₂ : (G2 BQ).left ⟶ (G2 BT).left} (hsq : IsSquare β β₂)
    (w : LB.Iso (abelian₂ BQ MQ) ((abelian₂ BT MT).pull β₂)) (hw : w.IsGen) (x y : 𝟙_ (Over (Sp V)) ⟶ BQ)
    (x₀ y₀ : 𝟙_ (Over (Sp W)) ⟶ BT) (hx : x.left ≫ β = spMap iw ≫ x₀.left) (hy : y.left ≫ β = spMap iw ≫ y₀.left)
    (τ₁ : LB.Gen (LB.LinComb MT (lamPts x₀ y₀) negε)) (h₁ : τ₁.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb MQ (lamPts x y) negε), τ.IsGen ∧ ∀ (T' : Over (Sp V)) (z : T'.left) J J',
      Good MT z J → Good MQ z J' →
        val τ (toUnit T').left z J' = lamVal w (lift (toUnit T' ≫ x) (toUnit T' ≫ y)).left z J J' *
          val τ₁ (T'.hom ≫ spMap iw) z J := by
  have hψ : (lift x y).left ≫ β₂ = spMap iw ≫ (lift x₀ y₀).left := by
    apply pullback.hom_ext
    · show ((lift x y).left ≫ β₂) ≫ (fst BT BT).left = (spMap iw ≫ (lift x₀ y₀).left) ≫ (fst BT BT).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
        lift_fst]
    · show ((lift x y).left ≫ β₂) ≫ (snd BT BT).left = (spMap iw ≫ (lift x₀ y₀).left) ≫ (snd BT BT).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
        lift_snd]
  obtain ⟨t₂, ht₂, hv₂⟩ := exists_gen hMT
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift x₀ y₀).left ≫ (psum BT (x2 BT) I.down).left)
    (ε' := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (by
      intro U _ H
      rw [lam_form x₀ y₀ U H, ← Finset.prod_inv_distrib]
      simp only [zpow_neg]) (LB.invGen MT _ _ τ₁) (DVR.invGen_isGen _ _ _ _ h₁)
  let t₃ : LB.Gen ((abelian₂ BT MT).pull (lift x₀ y₀).left) := GlobalTheory.UU.unflatGen t₂
  have ht₃ : t₃.IsGen := GlobalTheory.UU.unflatGen_isGen ht₂
  obtain ⟨a, ha, hva⟩ := GlobalTheory.ArcPull.exists_down_om hw (LB.isLB_linComb hMT _ _) (LB.isLB_linComb hMQ _ _)
    (φ' := fun _ : PUnit => (lift x y).left) (φ := fun _ => (lift x₀ y₀).left) (ε := fun _ => 1) (spMap iw)
    (fun _ => hψ) t₃ ht₃
  obtain ⟨τ, hτ, hvτ⟩ := exists_gen hMQ
    (φ := fun I : ULift.{0} (Finset (Fin 2)) => (lift x y).left ≫ (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => -((-1 : ℤ) ^ (2 - I.down.card))) (φ' := lamPts x y) (ε' := negε) (by
      intro U _ H
      simp only [zpow_neg, Finset.prod_inv_distrib]
      rw [lam_form x y U H, inv_inv]) (LB.invGen MQ _ _ (GlobalTheory.UU.flatGen a))
    (DVR.invGen_isGen _ _ _ _ (GlobalTheory.UU.flatGen_isGen ha))
  refine ⟨τ, hτ, fun T' z J J' hJ hJ' => ?_⟩
  have e1 := hvτ _ (toUnit T').left z J' hJ'
  have e5 := val_flatGen (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x y).left) a (toUnit T').left z hJ'
  rw [val_inv, e5] at e1
  have e6 : val t₃ ((toUnit T').left ≫ spMap iw) z
      (fun ψ (k : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum BT (x2 BT) k.down).left)) =
      val t₂ ((toUnit T').left ≫ spMap iw) z J := val_unflatGen (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) (F := (lift x₀ y₀).left) t₂ ((toUnit T').left ≫ spMap iw) z hJ
  have e2 := hva _ (toUnit T').left z _ _
    (good_linComb (L := MT) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BT (x2 BT) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ)
    (good_linComb (L := MQ) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum BQ (x2 BQ) I.down).left)
      (ε := fun I => (-1 : ℤ) ^ (2 - I.down.card)) hJ')
  rw [e6, hv₂ _ _ z J hJ, val_inv, Fintype.prod_unique, zpow_one, om_lam] at e2
  have e3 : (lift (toUnit T' ≫ x) (toUnit T' ≫ y)).left = (toUnit T').left ≫ (lift x y).left := by
    rw [← comp_lift]; rfl
  have e4 : (toUnit T').left = T'.hom := by simpa using Over.w (toUnit T')
  rw [e1, e3, ← e4, ← inv_inv (val τ₁ ((toUnit T').left ≫ spMap iw) z J), e2, _root_.mul_inv, _root_.mul_inv_cancel_left]
  rfl

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart


open GensFrom in
theorem exists_gens_of_dataFrom {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V)
    (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)) {M : ℕ}
    (eI : I ≃ Fin M) (hD : DataFrom T iw s ε n Q e) :
    ∃ τ : GlobalTheory.Poinc.Sep.Gens Q, GlobalTheory.Poinc.Sep.TauIn Q τ (fun k => s (eI.symm k))
      (fun k => (n : ℤ) • pull e.toIntLinearEquiv.toLinearMap (ε (eI.symm k))) ∧ GlobalTheory.Poinc.Sep.FromBase Q τ iw := by
  obtain ⟨β, β₂, w, hpb, hsq, hw, hc, hτ⟩ := hD
  have key := fun a b => exists_gen_of_base T.M.isLB Q.M.isLB iw hsq w hw (Q.c a) (Q.c b)
    (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b)) (hc a) (hc b) (T.τ₀ _ _) (T.τ₀_gen _ _)
  choose τ hτg hτv using key
  refine ⟨τ, fun a b => ⟨hτg a b, ?_⟩, T.B, inferInstance, inferInstance, T.M.L, fun a => T.c₀ ((n : ℤ) • e a),
    fun a b => T.τ₀ _ _, β, β₂, w, T.isAb, T.M.isLB, hpb, hsq, hw, hc, fun a b => T.τ₀_gen _ _,
    fun T' a b z J J' hJ hJ' => hτv a b T' z J J' hJ hJ'⟩
  obtain ⟨k, hk, hv⟩ := hτ a b
  refine ⟨k, ?_, fun z J' hJ' => ?_⟩
  · rw [hk]
    refine Fintype.prod_equiv eI _ _ fun i => ?_
    simp [pull]
  · choose J hJ using fun χ : (TK V).left ⟶ T.B.left => exists_chart T.M.isLB (χ z)
    rw [hv z J J' hJ hJ', hτv a b (TK V) z J J' hJ hJ']

end GlobalTheory.TChart
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.EffPos

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier

theorem exists_coheight_eq_one_notMem {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {M : LB X}
    (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {x : X} (hx : x ∉ nonzeroLocus s) :
    ∃ w : X, Order.coheight w = 1 ∧ w ∉ nonzeroLocus s := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ M.U i := by
    have : x ∈ (⨆ i, M.U i : X.Opens) := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set g := X.presheaf.germ _ x hi (s.f i) with hgdef
  have hg0 : g ≠ 0 := GlobalTheory.MixHt.CycLoc.germ_ne_zero hs hi
  have hgu : ¬ IsUnit g := fun h =>
    hx ((Cartier.mem_nonzeroLocus_iff s i hi).2 ((Scheme.mem_basicOpen _ _ _ _).2 h))
  have hle : Ideal.span {g} ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2 hgu)
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le hle
  have hPp : P.IsPrime := hP.1.1
  have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  have hgP : g ∈ P := hP.1.2 (Ideal.subset_span rfl)
  have hP0 : (⊥ : Ideal (X.presheaf.stalk x)) < P := bot_lt_iff_ne_bot.2 fun h =>
    hg0 (by rw [h] at hgP; simpa using hgP)
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
  rw [Ideal.height_bot, zero_add] at e0
  refine ⟨X.fromSpecStalk x ⟨P, hPp⟩, ?_, ?_⟩
  · rw [GlobalTheory.MixHt.CycLoc.coheight_fromSpecStalk]
    exact le_antisymm h1 e0
  · rw [GlobalTheory.MixHt.CycLoc.mem_nonzeroLocus_iff_notMem s hi, not_not]
    exact hgP

end GlobalTheory.AV.EffPos

namespace GlobalTheory.AV.EffPos

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier

theorem interNumRed_pos {K : Type} [Field K] (A : AbVar K) (n : ℕ) (hdim : A.dim = n + 1)
    (L : LB A.X.left) (hL : L.IsLB) (hLa : IsAmpleLB L) {w : A.X.left} (hw : Order.coheight w = 1) :
    letI := A.algΓ
    0 < interNumRed K (⟨closure {w}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) := by
  letI := A.algΓ
  obtain ⟨hint, hnoeth, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hstr, hproj⟩ := AbVarProj.strHom_eq_and_isProjOver K A
  have hp : IsProjOver (strHom K (X := A.X.left)) := hstr ▸ hproj
  have hX : topologicalKrullDim A.X.left = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_dim, hdim]
  have : LocallyOfFiniteType (strHom K (X := A.X.left)) := by
    obtain ⟨N, j, _, h⟩ := hp
    exact h ▸ inferInstance
  set C : Closeds A.X.left := ⟨closure {w}, isClosed_closure⟩ with hC
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓAlong K (redι C)
  rw [interNumRed_def, interNumSub_def,
    interNumOn_eq_interNum_pull (k := K) (f := redι C) (fun _ => rfl) (fun _ => hL)]
  have hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = (n : WithBot ℕ∞) := by
    rw [topologicalKrullDim_red]
    exact VdmRec.CutSec.dim_closure_of_coheight_field (strHom K A.X.left) hX hw
  exact CompanionTheory.NefKleiman.interNum_top_pos_of_isAmpleLB K _ (PullVanish.isProjOver_red hp C) n hd _
    (hLa.pull_of_isClosedImmersion (redι C))

theorem inter_cons_pos : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left), IsAmpleCls c → ∀ (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), Out.nonzeroLocus s ≠ ⊥ → Out.nonzeroLocus s ≠ ⊤ → 0 < inter A (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  intro K _ A n hdim c hc M hM s hbot htop
  obtain ⟨L, hL, hrel, rfl⟩ := hc
  have hLa : IsAmpleLB L := (AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 ⟨L, hL, hrel, rfl⟩
  letI := A.algΓ
  obtain ⟨hint, hnoeth, hcpt⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hstr, hproj⟩ := AbVarProj.strHom_eq_and_isProjOver K A
  have hp : IsProjOver (strHom K (X := A.X.left)) := hstr ▸ hproj
  have hX : topologicalKrullDim A.X.left = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_dim, hdim]
  have hcons : ∀ j, ((Fin.cons M (fun _ : Fin n => L) : Fin (n + 1) → LB A.X.left) j).IsLB :=
    fun j => Fin.cases hM (fun _ => hL) j
  have hfam : (Fin.cons (cls M hM) (fun _ : Fin n => cls L hL) : Fin (n + 1) → Pic A.X.left) =
      fun j => cls ((Fin.cons M (fun _ : Fin n => L) : Fin (n + 1) → LB A.X.left) j) (hcons j) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
  rw [hfam, T.abelianVariety_intersection_eq_lineBundleIntersection K A (Fin (n + 1)) _ hcons]
  have hs : genericPoint A.X.left ∈ nonzeroLocus s := by
    obtain ⟨y, hy⟩ : (nonzeroLocus s : Set A.X.left).Nonempty := by
      by_contra h
      exact hbot (TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 h))
    exact ((genericPoint_spec A.X.left).mem_open_set_iff (nonzeroLocus s).isOpen).2 ⟨y, trivial, hy⟩
  rw [SecCycle.interNum_cons_eq_finsum_mult K A.X.left hp n hX.le M hM (fun _ => L) (fun _ => hL) s hs]
  obtain ⟨x, hx⟩ : ∃ x, x ∉ nonzeroLocus s := by
    by_contra h
    push_neg at h
    exact htop (eq_top_iff.2 fun x _ => h x)
  obtain ⟨w, hw1, hws⟩ := exists_coheight_eq_one_notMem hM s hs hx
  have hfs := (divOfSec hM s hs).finite_support_mult
  have hterm : ∀ v, 0 ≤ (divOfSec hM s hs).mult v *
      interNumRed K (⟨closure {v}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) := by
    intro v
    by_cases hv : (divOfSec hM s hs).mult v = 0
    · rw [hv, zero_mul]
    · exact mul_nonneg (mult_divOfSec_nonneg v)
        (interNumRed_pos A n hdim L hL hLa (CartierDiv.coheight_eq_one_of_mult_ne_zero hv)).le
  have hmw : (divOfSec hM s hs).mult w ≠ 0 := SecCycle.mult_divOfSec_ne_zero hM s hs hw1 hws
  have hw0 : 0 < (divOfSec hM s hs).mult w *
      interNumRed K (⟨closure {w}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) :=
    mul_pos (lt_of_le_of_ne (mult_divOfSec_nonneg w) (Ne.symm hmw)) (interNumRed_pos A n hdim L hL hLa hw1)
  rw [finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_]
  · exact Finset.sum_pos' (fun v _ => hterm v) ⟨w, by simpa using hmw, hw0⟩
  · intro v hv
    simpa using Function.support_mul_subset_left _ _ hv

end GlobalTheory.AV.EffPos
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K]

def kerLPart (l : ℕ) {A B : AbVar K} (f : A ⟶ B) : Subgroup A.Pt where
  carrier := {x | x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1}
  one_mem' := ⟨(ptMap f).map_one, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, n, hn⟩ ⟨hy, m, hm⟩
    refine ⟨?_, n + m, ?_⟩
    · have := (ptMap f).map_mul x y
      simp only [ptMap_apply] at this
      rw [this, hx, hy, _root_.one_mul]
    · rw [mul_pow, pow_add, pow_mul, hn, one_pow, mul_comm (l ^ n), pow_mul, hm, one_pow, _root_.one_mul]
  inv_mem' := by
    rintro x ⟨hx, n, hn⟩
    refine ⟨?_, n, ?_⟩
    · have := (ptMap f).map_inv x
      simp only [ptMap_apply] at this
      rw [this, hx, inv_one]
    · rw [inv_pow, hn, inv_one]

theorem kerLPart_le (l : ℕ) {A B : AbVar K} (f : A ⟶ B) : kerLPart l f ≤ (ptMap f).ker :=
  fun _ hx => hx.1

theorem card_kerLPart_eq (K : Type) [Field K] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0)
    (A B : AbVar K) (f : A ⟶ B) (hf : IsIsogeny f) :
    Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} = l ^ padicValNat l (deg f) := by
  set G := kerLPart l f with hG
  change Nat.card G = _
  have hker : Finite (ptMap f).ker := (GlobalTheory.T.isFinite_iff_finite_ker' K A B f).1 hf.1
  haveI hGfin : Finite G := Finite.of_injective (Subgroup.inclusion (kerLPart_le l f))
    (Subgroup.inclusion_injective _)
  have hpG : IsPGroup l G := fun g => by
    obtain ⟨n, hn⟩ := g.2.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hpG)
  have hcardK : ((Nat.card G : ℕ) : K) ≠ 0 := by
    rw [hk, Nat.cast_pow]; exact pow_ne_zero _ hl
  have hgal : ∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G := by
    rintro σ x ⟨hx, n, hn⟩
    refine ⟨?_, n, ?_⟩
    · have h1 : galPts A.X σ x ≫ f.hom = galPts B.X σ (x ≫ f.hom) := Category.assoc _ _ _
      rw [h1, hx, map_one]
    · rw [← map_pow, hn, map_one]
  obtain ⟨B', q, hq, hdq, hkq, huniv⟩ := GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup K A G hGfin hcardK hgal
  obtain ⟨h, hqh⟩ := huniv B f (kerLPart_le l f)
  have hdAB := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf).1
  have hdAB' := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B' q hq).1
  have hcomp := GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A B' B q h hdAB' (hdAB'.symm.trans hdAB)
  rw [hqh] at hcomp
  have hh : IsIsogeny h := (hcomp.1.mp hf).2
  have hsurj := (GlobalTheory.T.abVar_surjective_iff_ptMap_surjective K A B' q).1 hq.2
  have hnot : ¬ l ∣ deg h := by
    refine GlobalTheory.T.not_dvd_deg_of_no_torsion_in_kernel' K l hl B' B h hh ?_
    intro y hyl hyh
    obtain ⟨x, rfl⟩ := hsurj y
    have hxf : x ≫ f.hom = 1 := by
      rw [← hqh, comp_hom, ← Category.assoc]; exact hyh
    have hxl : x ^ l ∈ G := by
      rw [← hkq, MonoidHom.mem_ker, map_pow, hyl]
    obtain ⟨n, hn⟩ := hxl.2
    have hx : x ∈ G := ⟨hxf, n + 1, by rw [pow_succ', pow_mul]; exact hn⟩
    rw [← hkq] at hx
    exact hx
  have hdh : deg h ≠ 0 := fun h0 => hnot (h0 ▸ dvd_zero l)
  rw [hcomp.2, hdq, hk, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) hdh,
    Nat.padicValNat_def, Nat.multiplicity_prime_pow, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnot, add_zero]

end GlobalTheory.AV.AbVar
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pt_comp_id_pow {K : Type} [Field K] (A : AbVar K) (x : A.Pt) (n : ℕ) :
    x ≫ (𝟙 A.X) ^ n = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ k ih => rw [pow_succ, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem pt_divisible : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), n ≠ 0 → ∀ x : A.Pt, ∃ y : A.Pt, y ^ n = x := by
  intro K _ A n hn x
  have hz : ((n : ℤ)) ≠ 0 := by exact_mod_cast hn
  have hiso := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hz).1
  have hs : Function.Surjective (ptMap ((n : ℤ) • 𝟙 A)) := (GlobalTheory.T.abVar_surjective_iff_ptMap_surjective K A A _).1 hiso.2
  obtain ⟨y, hy⟩ := hs x
  refine ⟨y, ?_⟩
  rw [← hy, ptMap_apply, natCast_zsmul, nsmul_hom, id_hom, pt_comp_id_pow]

end GlobalTheory.AV.AbVar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rechart_at_unitaryClassicalTrait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (U : X.M.Z.Opens) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U → (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) ∈ U → spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ → X.M.ringOn U ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₁ : ratHull (X.M.ringOn U) →+* PadicAlgCl p, (∀ a : X.M.ringOn U, y₁ (toRat _ a) = X.M.val (gPt p ≫ ct.y) a) ∧ spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y ∧ ∀ a : X.o₁, ‖y₁ (toRat _ (algebraMap X.o₁ (X.M.ringOn U) a))‖ ≤ 1 := by
  first | exact @GlobalTheory.UPoinc.rechart_at_uClassical_trait | exact GlobalTheory.UPoinc.rechart_at_uClassical_trait | (intros; apply GlobalTheory.UPoinc.rechart_at_uClassical_trait <;> assumption)
end
