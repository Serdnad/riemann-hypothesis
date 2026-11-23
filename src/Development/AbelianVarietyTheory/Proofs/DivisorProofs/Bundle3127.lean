module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle021
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']


variable (B') in
abbrev sw2 : Fin 2 → ((G2 B').left ⟶ (G2 B').left) :=
  ![(lift (fst B' B') (snd B' B')).left, (lift (snd B' B') (fst B' B')).left]

theorem lift_comp_squareFactorIdentity_eq_lift {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 0 = (lift a b).left := by
  show (lift a b).left ≫ (lift (fst B' B') (snd B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem lift_comp_squareFactorSwap_eq_lift_swap {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 1 = (lift b a).left := by
  show (lift a b).left ≫ (lift (snd B' B') (fst B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem formEq_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) :
    FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => sw2 B' k ≫ β₂) (flatε lamε ![1, -1]) := by
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  intro U _ h
  rw [GlobalTheory.LamBiext.prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
  show 1 = (∏ i, h (((lift (fst B' B') (snd B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ) *
    (∏ i, h (((lift (snd B' B') (fst B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (-1 : ℤ)
  rw [β₂_lift, β₂_lift, GlobalTheory.LamBiext.prod_lam, GlobalTheory.LamBiext.prod_lam, _root_.mul_comm (toBase hw₀ (snd B' B'))]
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_gen_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) {M : LB B.left} (hM : M.IsLB) :
    ∃ t : LB.Gen (LB.LinComb (abelian₂ B M) (fun k => sw2 B' k ≫ β₂) ![1, -1]), t.IsGen ∧
      ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι), Good M z J →
        val (L := abelian₂ B M) t r z (ind B J) = 1 := by
  obtain ⟨g, hg, hv⟩ := exists_gen hM (formEq_sw hβ hsq) (LB.oneGen M) (oneGen_isGen _)
  refine ⟨GlobalTheory.LamBiext.nest M (lamφ B) lamε (fun k => sw2 B' k ≫ β₂) ![1, -1] g, nest_isGen hg,
    fun r z J hJ => ?_⟩
  refine (val_nest hg r (good_ind hJ) hJ).trans ?_
  simp only [adj_ind hM hJ, one_zpow, Finset.prod_const_one, _root_.one_mul]
  exact (hv _ r z J hJ).trans (val_one r)

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.Mum.Two

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']

theorem isoVal_swap (hB' : IsAbelianScheme B') {M : LB B.left} {M₁ : LB B₁.left} (hM : M.IsLB) (hM₁ : M₁.IsLB)
    {f : S' ⟶ S} {f₁ : S' ⟶ S₁} {β : B'.left ⟶ B.left} {β₁ : B'.left ⟶ B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (hβ : IsGrpPullback B' B f β) (hβ₁ : IsGrpPullback B' B₁ f₁ β₁) (hsq : IsSquare β β₂) (hsq₁ : IsSquare β₁ β₂')
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) (hw : w.IsGen) {T : Over S'} (x y : T ⟶ B')
    (z : T.left) (J : (T.left ⟶ B₁.left) → M₁.ι) (J' : (T.left ⟶ B.left) → M.ι) (hJ : Good M₁ z J)
    (hJ' : Good M z J') :
    isoVal w (lift x y).left z J J' = isoVal w (lift y x).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have hL' : ((abelian₂ B M).pull β₂).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hM _ _) _ _
  obtain ⟨t, ht, hvt⟩ := exists_gen_sw hβ₁ hsq₁ hM₁
  obtain ⟨g, hg, hvg⟩ := exists_gen_sw hβ hsq hM
  let c := chartPullLinComb (abelian₂ B M) β₂ (sw2 B') (fun k => sw2 B' k ≫ β₂) ![1, -1] (𝟙 _)
    (fun k => (Category.id_comp _).symm)
  have ha : (cGen c g).IsGen := cGen_isGen c hg
  have good_P : ∀ {Z : Scheme.{0}} {z₀ : Z} {J₀ : (Z ⟶ B.left) → M.ι}, Good M z₀ J₀ →
      Good ((abelian₂ B M).pull β₂) z₀ (fun q _ => ind B J₀ (q ≫ β₂)) :=
    fun hJ₀ q => mem_pull.2 (good_ind hJ₀ (q ≫ β₂))
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B.left) → M.ι), Good M z₀ J₀ →
      val (cGen c g) r z₀ (fun q _ => ind B J₀ (q ≫ β₂)) = 1 := by
    intro Z r z₀ J₀ hJ₀
    rw [← hvg r z₀ J₀ hJ₀, val_of g r z₀ (ind B J₀) (fun k => ind B J₀ ((r ≫ sw2 B' k) ≫ β₂))
      (fun k => by rw [Category.assoc])]
    exact gm_res r z₀ _ ((good_P hJ₀).mem _ r) _
  have gw_iso : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (φ : (G2 B').left ⟶ (G2 B').left) (z₀ : Z)
      (J₀ : (Z ⟶ B₁.left) → M₁.ι) (J₀' : (Z ⟶ B.left) → M.ι),
      gw w (r ≫ φ) z₀ (ind B₁ J₀ (r ≫ φ ≫ β₂')) (fun _ => ind B J₀' ((r ≫ φ) ≫ β₂)) =
        isoVal w (r ≫ φ) z₀ J₀ J₀' := by
    intro Z r φ z₀ J₀ J₀'
    have e₁ : ind B₁ J₀ (r ≫ φ ≫ β₂') = fun I => J₀ ((r ≫ φ) ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left) :=
      funext fun I => congrArg J₀ (by simp only [Category.assoc])
    have e₂ : ind B J₀' ((r ≫ φ) ≫ β₂) = fun I => J₀' ((r ≫ φ) ≫ β₂ ≫ (psum B (x2 B) I.down).left) :=
      funext fun I => congrArg J₀' (by simp only [Category.assoc])
    rw [e₁, e₂]; rfl
  have Fp : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B₁.left) → M₁.ι)
      (J₀' : (Z ⟶ B.left) → M.ι),
      pw w (sw2 B') ![1, -1] r z₀ (fun k => ind B₁ J₀ (r ≫ sw2 B' k ≫ β₂'))
        (fun k => (fun (q : Z ⟶ (G2 B').left) (_ : PUnit) => ind B J₀' (q ≫ β₂)) (r ≫ sw2 B' k)) =
        isoVal w (r ≫ sw2 B' 0) z₀ J₀ J₀' * (isoVal w (r ≫ sw2 B' 1) z₀ J₀ J₀')⁻¹ := by
    intro Z r z₀ J₀ J₀'
    unfold pw
    rw [Fin.prod_univ_two]
    rw [gw_iso r (sw2 B' 0) z₀ J₀ J₀', gw_iso r (sw2 B' 1) z₀ J₀ J₀']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg]
  have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
  have E := rigid_pw w hw hL hL' (sw2 B') ![1, -1] ha ht _ _ he2
    (surj_comp (surj_snd hG hB' _) (hG _ _ hB').2) (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM₁ y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      refine ⟨ind B₁ J₁, fun q _ => ind B J₁' (q ≫ β₂), good_ind hJ₁, good_P hJ₁', ?_⟩
      rw [hvt _ y₀ J₁ hJ₁, Fp, Fa _ y₀ J₁' hJ₁', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, mul_inv_cancel, _root_.mul_one])
    T.left (lift x y).left z (ind B₁ J) (fun q _ => ind B J' (q ≫ β₂)) (good_ind hJ) (good_P hJ')
  rw [hvt _ z J hJ, Fp, Fa _ z J' hJ', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, _root_.mul_one] at E
  exact mul_inv_eq_one.1 E.symm

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart

theorem periodConst_symm : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a b, q a b = q b a := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁ hfin hloc hκ hpb hpb' hsq hsq'
    x hx w₁ q hgen hper hnorm a b
  have hAb : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback D.toPre.P.isAb hpb
  obtain ⟨κK, hκK⟩ : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ := by
    have hi : Function.Injective ((algebraMap V₁ (FractionRing V₁)).comp f₁) :=
      (IsFractionRing.injective V₁ (FractionRing V₁)).comp hf₁
    obtain ⟨g, eg⟩ : ∃ g : FractionRing V →+* FractionRing V₁,
        g.comp (algebraMap V (FractionRing V)) = (algebraMap V₁ (FractionRing V₁)).comp f₁ :=
      ⟨IsLocalization.lift (M := nonZeroDivisors V) (g := (algebraMap V₁ (FractionRing V₁)).comp f₁) fun y =>
        IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (nonZeroDivisors.coe_ne_zero y)), IsLocalization.lift_comp _⟩
    refine ⟨spMap g, ?_⟩
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eg]
  let z : (TK V₁).left := (⊥ : PrimeSpectrum (FractionRing V₁))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt L.T.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB z
  have h₁ := hper κK hκK a b z J J' hJ hJ'
  have h₂ := hper κK hκK b a z J J' hJ hJ'
  rw [GlobalTheory.Mum.RosatiSymmetry.val_tau_symm D.toPre hJ' κK,
    val_corr hJ (corr_of_val L.T.M.isLB (L.T.τ₀_symm ((n : ℤ) • b) ((n : ℤ) • a))),
    GlobalTheory.TChart.SwapIso.isoVal_swap hAb D.toPre.P.isLB L.T.M.isLB hpb hpb' hsq hsq' w₁ hgen
      (toUnit (TK V₁) ≫ x b) (toUnit (TK V₁) ≫ x a) z J J' hJ hJ'] at h₂
  have hq := mul_right_cancel (h₁.symm.trans h₂)
  have hs : Subsingleton (TK V₁).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing V₁)))
  have eu : unitOn (q a b) = unitOn (q b a) := unit_ext fun y _ => by rw [Subsingleton.elim y z]; exact hq
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V₁))).inv).1 eu

end GlobalTheory.TChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mulFam_exists_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G → (∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0 := by
  intro R _ _ _ _ D m hm F₁ G hG ⟨α, j, hj⟩
  by_contra hcon
  push_neg at hcon
  apply hj
  have hfinite : IsFinite (mulA D.toPre.P.A m).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ D.toPre.P m hm.pos
  have hc := D.toPre.P.isAb.comm
  have hsm := D.toPre.P.isAb.smooth
  have hmhom := GlobalTheory.AbLaw.MulN.isMonHom_mulA D.toPre.P.A m
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ _),
      Flat ((Over.pullback t).map (mulA D.toPre.P.A m)).left ∧
        Surjective ((Over.pullback t).map (mulA D.toPre.P.A m)).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (TLinPf.isAb_pullback t D.toPre.P.A D.toPre.P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hfinite)
  have h₂ : Flat (mulA D.toPre.P.A m).left :=
    GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ _ _ _ inferInstance inferInstance
      inferInstance hfinite fun K _ _ t => (hgeo K t).1
  have h₃ : Surjective (mulA D.toPre.P.A m).left :=
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2
  obtain ⟨u, -, -, e⟩ := hG.1 α
  refine GlobalTheory.PullLin.sec_eq_zero_of_flat D.toPre.P.isLB (F₁.f α) (mulA D.toPre.P.A m).left (fun x J hJ => ?_) j
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (𝟙 _) x J hJ
  rw [ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius.sval_zero _ (hcon _), Category.id_comp] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.MulPull in
theorem mulPull_gen_labCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    (C : LabCover D) (m : ℕ) :
    ∃ u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]),
      u.IsGen := by
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hcube : HasGen C.P.L.L (thφ C.G (x3 C.G)) thε := ⟨C.P.c.t, C.P.c.isGen⟩
  have hrig : HasGen C.P.L.L (K := PUnit) (fun _ => eSec C.G) (fun _ => 1) := ⟨C.P.L.rig, C.P.L.rigGen⟩
  have hone : HasGen C.P.L.L (K := Fin 1) ![(1 : C.G ⟶ C.G).left] ![1] := by
    refine (hrig.pull (toUnit C.G).left).of_formEq hL (fun U _ h => ?_)
    simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, _root_.mul_one]
    rfl
  have hsym0 : HasGen C.P.L.L (K := Fin 2) ![(ι[C.G]).left, 𝟙 C.G.left] ![1, -1] := ⟨C.P.sym, C.P.sym_gen⟩
  have e1 : ((𝟙 C.G)⁻¹ : C.G ⟶ C.G).left = (ι[C.G]).left := by
    show ((𝟙 C.G) ≫ ι[C.G]).left = _
    rw [Category.id_comp]
  have e2 : (𝟙 C.G : C.G ⟶ C.G).left = 𝟙 C.G.left := rfl
  have hsym : HasGen C.P.L.L (K := Fin 2) ![(𝟙 C.G : C.G ⟶ C.G).left, ((𝟙 C.G)⁻¹ : C.G ⟶ C.G).left] ![1, -1] := by
    refine hsym0.inv.of_formEq hL (fun U _ h => ?_)
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, e1, e2]
    simp only [neg_neg, zpow_one, _root_.mul_one]
    exact mul_comm _ _
  have H := hasGen_pow hL hcube (𝟙 C.G) hone hsym m
  have e3 : ((𝟙 C.G) ^ m : C.G ⟶ C.G).left = (mulA C.G m).left := by
    rw [← GlobalTheory.ZH.TorsFrame.comp_mulA]
  refine H.of_formEq hL (fun U _ h => ?_)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, e2, e3]
  push_cast
  rfl


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_mulSecK (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hR : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) (m : ℕ) (_hm : Odd m) (θ₀ : SecK C.P.L.L C.α 1) :
    ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  obtain ⟨u, hu⟩ := mulPull_gen_labCover C m
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hc : (mulA C.A.A m).left ≫ C.α = C.α ≫ (mulA C.G m).left := GlobalTheory.ZH.TorsFrame.mulA_comm C.α_cart m
  let S₀ := pullMulSec θ₀ (mulA C.A.A m).left (LB.pullGen C.P.L.L _ _ u C.α) (DVR.pullGen_isGen C.P.L.L _ _ u hu C.α)
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (mulA C.A.A m).left ≫ C.α)
      (fun k : Fin 2 => C.α ≫ (![𝟙 C.G.left, (mulA C.G m).left] : Fin 2 → _) k))
      (Sum.elim (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) (![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)] : Fin 2 → ℤ))
      (fun _ : Fin 1 => C.α) (fun _ => ((m ^ 2 : ℕ) : ℤ)) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Category.comp_id, hc]
    simp only [Nat.cast_one, zpow_one, zpow_neg, _root_.mul_one]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨S, hS⟩ := exists_sec hL hf S₀
  refine ⟨S, u, hu, fun Z p z J hJ => ?_⟩
  rw [hS Z p z J hJ, sval_pullMulSec θ₀ _ _ _ p z hJ, val_pull hJ, mul_comm]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem intElem_pow_mul_of_away {R S Rt St : Type} [CommRing R] [CommRing S] [CommRing Rt] [CommRing St]
    (f : R →+* S) (t : R) [Algebra R Rt] [Algebra S St] [IsLocalization.Away t Rt]
    [IsLocalization.Away (f t) St] (ft : Rt →+* St)
    (hc : ft.comp (algebraMap R Rt) = (algebraMap S St).comp f) (x : S)
    (hx : ft.IsIntegralElem (algebraMap S St x)) : ∃ n : ℕ, f.IsIntegralElem (f t ^ n * x) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra Rt St := ft.toAlgebra
  letI : Algebra R St := ((algebraMap S St).comp f).toAlgebra
  haveI : IsScalarTower R Rt St := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : IsScalarTower R S St := IsScalarTower.of_algebraMap_eq' rfl
  have hx' : IsIntegral Rt (algebraMap S St x) := hx
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := hx'.exists_multiple_integral_of_isLocalization (Submonoid.powers t)
  have e : (⟨t ^ a, a, rfl⟩ : Submonoid.powers t) • algebraMap S St x =
      algebraMap S St (f t ^ a * x) := by
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S St, ← map_mul]
    simp [RingHom.algebraMap_toAlgebra]
  rw [e] at ha
  have hr : IsIntegral R (f t) := f.isIntegralElem_map
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (R := R) (Sₘ := St) hr ha
  exact ⟨n + a, by rw [pow_add, _root_.mul_assoc]; exact hn⟩

theorem isIntegralElem_of_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) {y : C} (h : (g.comp f).IsIntegralElem y) : g.IsIntegralElem y := by
  obtain ⟨p, hp, h⟩ := h
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact h⟩

theorem res_res_sections {Y : Scheme.{0}} {U V V' : Y.Opens} (h1 : V ≤ U) (h2 : V' ≤ V) (z : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom z) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chartVal_isIntegral_of_intAt : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k)
    (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) →
    (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  intro X Y L α k s j W hW hWa hYa hint
  letI : Algebra Γ(X, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  set F := chartVal L α s j W hW with hF
  have loc : ∀ x ∈ W, ∃ d : Γ(X, W), x ∈ X.basicOpen d ∧
      ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F) := by
    intro x hx
    obtain ⟨j', W', hW', hxW', hW'a, hint'⟩ := hint x hx
    obtain ⟨d, hdle, hxd⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨x, ⟨hx, hxW'⟩⟩ hx
    refine ⟨d, hxd, ?_⟩
    set r : Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom d with hr
    have hED : Y.basicOpen r ≤ α ⁻¹ᵁ X.basicOpen d := (Scheme.preimage_basicOpen α d).ge
    haveI := hWa.isLocalization_basicOpen d
    haveI := hYa.isLocalization_basicOpen r
    have hDW : X.basicOpen d ≤ W := X.basicOpen_le d
    have hDW' : X.basicOpen d ≤ W' := hdle.trans inf_le_right
    have hEW : Y.basicOpen r ≤ α ⁻¹ᵁ W := Y.basicOpen_le r
    have hEW' : Y.basicOpen r ≤ α ⁻¹ᵁ W' := hED.trans (fun y hy => hDW' hy)
    have hDjj : X.basicOpen d ≤ L.U j ⊓ L.U j' := le_inf (hDW.trans hW) (hDW'.trans hW')
    let LC := LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))
    have hEJ : Y.basicOpen r ≤ LC.U (fun _ => j) ⊓ LC.U (fun _ => j') :=
      le_inf (hEW.trans (locInt_le_chart L α j W hW)) (hEW'.trans (locInt_le_chart L α j' W' hW'))
    refine intElem_pow_mul_of_away (α.app W).hom d (Rt := Γ(X, X.basicOpen d))
      (St := Γ(Y, Y.basicOpen r)) (α.appLE _ _ hED).hom ?_ F ?_
    · show (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW).op).hom =
        (Y.presheaf.map (homOfLE hEW).op).hom.comp (α.app W).hom
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
    · have hc0 := congrArg (Y.presheaf.map (homOfLE hEJ).op).hom (s.compat (fun _ => j) (fun _ => j'))
      rw [map_mul] at hc0
      show (α.appLE _ _ hED).hom.IsIntegralElem ((Y.presheaf.map (homOfLE hEW).op).hom F)
      have eF : (Y.presheaf.map (homOfLE hEW).op).hom F = (Y.presheaf.map (homOfLE hEJ).op).hom
          ((Y.presheaf.map (homOfLE (inf_le_left : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ LC.U (fun _ => j))).op).hom
            (s.f (fun _ => j))) :=
        (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
      rw [eF, hc0]
      refine RingHom.IsIntegralElem.mul _ ?_ ?_
      · have h'' : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ α ⁻¹ᵁ (L.U j ⊓ L.U j') :=
          le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
        have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
            Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) ^ k := by
          change ((∏ _i : Fin 1, (ReciprocityTheory.ChartRestriction.G.Semi.res h''
            (ReciprocityTheory.ChartRestriction.G.Semi.pullU α (L.U j ⊓ L.U j') (L.g j j'))) ^ (k : ℤ) :
              Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = _
          rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
          rfl
        have hz : (Y.presheaf.map (homOfLE hEJ).op).hom ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) =
            (α.appLE _ _ hED).hom ((X.presheaf.map (homOfLE hDjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) := by
          refine (res_res_sections _ _ _).trans ?_
          have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (L.g j j' : Γ(X, L.U j ⊓ L.U j')))
            (Scheme.Hom.map_appLE (f := α) hED (homOfLE hDjj).op)
          exact this.symm
        rw [hg, map_pow, hz, ← map_pow]
        exact RingHom.isIntegralElem_map _
      · have h1 := hint'.map (Y.presheaf.map (homOfLE hEW').op).hom
        have e1 : (Y.presheaf.map (homOfLE hEW').op).hom.comp (α.app W').hom =
            (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW').op).hom := by
          rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
        rw [e1] at h1
        have h2 := isIntegralElem_of_comp _ _ h1
        convert h2 using 1
        exact (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
  change F ∈ (integralClosure Γ(X, W) Γ(Y, α ⁻¹ᵁ W)).toSubmodule
  let S0 : Set Γ(X, W) := {d | ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F)}
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ S0 ?_ F ?_
  · rw [← hWa.iSup_basicOpen_eq_self_iff]
    apply le_antisymm
    · exact iSup_le fun d => X.basicOpen_le _
    · intro x hx
      obtain ⟨d, hxd, hd⟩ := loc x hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨d, hd⟩, hxd⟩
  · rintro ⟨d, n, hn⟩
    refine ⟨n, ?_⟩
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow]
    exact hn

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBalNeg

theorem triv_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T (-c) := by
  intro R _ _ D D' r W T c ⟨Ξ, hΞ, h1, h2⟩
  have hF : FormEq (fun v : c.support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => -(c v.1))
      (fun v : (-c).support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => (-c) v.1) := by
    intro U _ h
    rw [Finset.prod_coe_sort c.support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ (-(c v))),
      Finset.prod_coe_sort (-c).support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ ((-c) v)),
      Finsupp.support_neg]
    simp only [Finsupp.neg_apply]
  obtain ⟨Ξ', hΞ', hv⟩ := exists_gen D.P.isLB hF (LB.invGen D.P.L _ _ Ξ) (LB.isGen_invGen D.P.L _ _ Ξ hΞ)
  refine ⟨Ξ', hΞ', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_inv, h1 z J hJ, inv_one]
  · rw [hv _ _ z J hJ, val_inv, h2 z J hJ y y', Finsupp.support_neg, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finsupp.neg_apply, neg_neg, zpow_neg, inv_inv]

end GlobalTheory.TensBalNeg
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isStronglyTrivialFormalSumTensor_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (c : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T (-c) := by
  first | exact @GlobalTheory.TensBalNeg.triv_neg | exact GlobalTheory.TensBalNeg.triv_neg | (intros; apply GlobalTheory.TensBalNeg.triv_neg <;> assumption)

end
end
