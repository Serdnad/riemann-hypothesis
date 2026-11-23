module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  first | exact @GlobalTheory.Mum.UpExt.over_famPull | exact GlobalTheory.Mum.UpExt.over_famPull | (intros; apply GlobalTheory.Mum.UpExt.over_famPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_equivariant_inverse_thetaExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  first | exact @GlobalTheory.Mum.exists_eqv_expandsF | exact GlobalTheory.Mum.exists_eqv_expandsF | (intros; apply GlobalTheory.Mum.exists_eqv_expandsF <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaFamilySectionEquivariance_smul_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  first | exact @GlobalTheory.Mum.ScaleEqv.eqv_scale | exact GlobalTheory.Mum.ScaleEqv.eqv_scale | (intros; apply GlobalTheory.Mum.ScaleEqv.eqv_scale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem _root_.GlobalTheory.T.torsionLabels_surjective_of_larger_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  first | exact @GlobalTheory.Mum.Desc.lab_onto_of_labExt | exact GlobalTheory.Mum.Desc.lab_onto_of_labExt | (intros; apply GlobalTheory.Mum.Desc.lab_onto_of_labExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TInj

theorem from_rescale_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (n : ℕ) (D₀ : DegPre W), D₀.PsiEven → D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → ∀ (ib : D₀.X ≃+ (Fin T.r → ℤ)) (β : D₀.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n D₀ ib β ββ w → ∀ (V : Type) [CommRing V] [IsDomain V] (iw : W →+* V), Function.Injective iw → ∀ (Q : DegPre V) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw D₀ (rescale Q g)) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (e : Q.X ≃+ (Fin T.r → ℤ)), (∀ y : Q.X, e y = ib (hD.xe y)) → (∀ a a' : Q.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e a'))) → ∃ (β' : Q.P.A.left ⟶ T.B.left) (ββ' : (G2 Q.P.A).left ⟶ (G2 T.B).left) (w' : LB.Iso (abelian₂ Q.P.A Q.P.L) ((abelian₂ T.B T.M.L).pull ββ')), From T iw s ε n Q e β' ββ' w' := by
  intro o W _ _ _ _ T n D₀ hev hbi hun ib β ββ w hF V _ _ iw hiw Q g hD I _ s ε e he hg
  have hin : ∀ χ, D₀.PsiIn χ ⊤ := fun χ j U hU hle h => by
    obtain ⟨r, -, hr⟩ := hun χ j U hU (Set.subset_univ _) hle h
    exact ⟨r, by rw [Ideal.map_top]; trivial, hr⟩
  let D₁ : DegData W ⊤ :=
    { toPre := D₀
      psi_even := hev
      tau_bimult := hbi
      psi_pos := fun χ _ => hin χ
      psi_tendsto := fun m => by
        rw [Ideal.top_pow]
        exact Set.finite_empty.subset fun χ hχ => hχ (hin χ) }
  letI : IsEmpty Empty := Empty.instIsEmpty
  obtain ⟨ββ', w', pb, sq, gen, hc, hτ⟩ :=
    from_pull T (fun _ : Empty => 0) n W V ⊤ D₁ (RingHom.id W) (fun _ => 1) ib β ββ w iw (rescale Q g) hD hiw hF
  rw [RingHom.comp_id] at pb hc hτ
  refine ⟨_, ββ', w', pb, sq, gen, fun a => ?_, fun a b => ?_⟩
  · rw [he a]; exact hc a
  · obtain ⟨k, hk, hv⟩ := hτ a b
    have hk1 : k = 1 := Units.ext (by rw [hk]; simp)
    refine ⟨_, hg a b, fun z J J' hJ hJ' => ?_⟩
    have H := hv z J J' hJ hJ'
    have E := rescale_tau_val Q g a b hJ'
    have H' := E.symm.trans H
    rw [hk1] at H'
    rw [he a, he b]
    have aux : ∀ {G : Type} [CommGroup G] (x y u t p : G), x * y⁻¹ * u⁻¹ * t = 1 * p → t = x⁻¹ * y * u * p := by
      intro G _ x y u t p h
      rw [_root_.one_mul] at h
      rw [← h, ← _root_.mul_assoc]
      have h1 : x⁻¹ * y * u * (x * y⁻¹ * u⁻¹) = (x⁻¹ * x) * (y * y⁻¹) * (u * u⁻¹) := by ac_rfl
      rw [h1]
      simp
    simp only [unitOn, map_mul, map_inv, map_one] at H' ⊢
    exact aux _ _ _ _ _ H'

end GlobalTheory.TInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj.PerUnit

theorem dataFrom_ofDeg {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (ω : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ))
    (n : ℕ) (D : DegPre V) (hB : D.TauBimult) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left)
    (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))
    (h : From T ω s ε n D e β β₂ w) : DataFrom T ω s ε n (GlobalTheory.PolDeg.Wit.ofDeg D hB) e := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun a b => ?_⟩
  obtain ⟨k, hk, hv⟩ := h₅ a b
  exact ⟨k, hk, fun z J J' hJ hJ' => ((GlobalTheory.PolDeg.Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ').trans (hv z J J' hJ hJ')⟩

theorem exists_good_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (z : (TK V).left) :
    ∃ J : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι, Good D.P.L z J ∧
      ∀ e : Sp V ⟶ D.P.A.left, e (closedPoint V) ∈ D.P.L.U (J ((TK V).hom ≫ e)) := by
  classical
  haveI : IsDominant (jK V) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : D.P.A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from D.P.A.hom]; infer_instance
  have hinj : ∀ e e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = (TK V).hom ≫ e' → e = e' :=
    fun e e' h => ext_of_isDominant (jK V) h
  have hsp : ∀ (e : Sp V ⟶ D.P.A.left) (p : Sp V) (i : D.P.L.ι), e (closedPoint V) ∈ D.P.L.U i → e p ∈ D.P.L.U i :=
    fun e p i h => (((PrimeSpectrum.le_iff_specializes p (closedPoint V)).1
      (IsLocalRing.le_maximalIdeal p.2.ne_top)).map e.continuous).mem_open (D.P.L.U i).isOpen h
  choose pick hpick using exists_chart D.P.isLB
  refine ⟨fun ψ => if h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ then pick (h.choose (closedPoint V))
    else pick (ψ z), fun ψ => ?_, fun e => ?_⟩
  · by_cases h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ
    · simp only [dif_pos h]
      have e1 : ψ z = ((TK V).hom ≫ h.choose) z :=
        (congrArg (fun q : (TK V).left ⟶ D.P.A.left => q z) h.choose_spec).symm
      rw [e1]
      exact hsp _ _ _ (hpick _)
    · simp only [dif_neg h]
      exact hpick _
  · have h : ∃ e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e' = (TK V).hom ≫ e := ⟨e, rfl⟩
    simp only [dif_pos h]
    rw [hinj _ _ h.choose_spec]
    exact hpick _

theorem val_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {X Y : Scheme.{0}} {L : LB X} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp V ⟶ Y) (z : (TK V).left)
    (J : ((TK V).left ⟶ X) → L.ι) (hJ : ∀ k, (y ≫ φ k) (closedPoint V) ∈ L.U (J ((TK V).hom ≫ y ≫ φ k))) :
    ∃ w : Vˣ, val t ((TK V).hom ≫ y) z J =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) w)) := by
  have hall : ∀ p : Sp V, y p ∈ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) := by
    intro p
    refine Set.mem_iInter.2 fun k => ?_
    have hsp : p ⤳ closedPoint V :=
      (PrimeSpectrum.le_iff_specializes p (closedPoint V)).1 (IsLocalRing.le_maximalIdeal p.2.ne_top)
    have hm := hJ k
    rw [← Category.assoc] at hm
    exact hsp.map (y ≫ φ k).continuous |>.mem_open (L.U _).isOpen hm
  have hU : y ⁻¹ᵁ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) = ⊤ := top_unique fun p _ => hall p
  have key : ∀ (U : (Sp V).Opens) (_ : U = ⊤) (a : Γ(Sp V, U)ˣ), ∃ w : Vˣ,
      gm (TK V).hom z U a = gm (TK V).hom z ⊤ (unitOn w) := by
    rintro U rfl a
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
    show a.val = (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val)
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  obtain ⟨w, hw⟩ := key _ hU (pullU y _ (t.s (fun k => J (((TK V).hom ≫ y) ≫ φ k))))
  refine ⟨w, ?_⟩
  have q : (toUnit (TK V)).left = (TK V).hom := by simp
  rw [← GlobalTheory.PolDeg.Taut.gm_jK_unitOn, q, ← hw]
  exact (gm_pull (TK V).hom y z _ (hall _) _).symm

end GlobalTheory.TInj.PerUnit

namespace GlobalTheory.TInj.PerUnit



theorem monomial_ratio_unit : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → ∀ y y' : D₁.X, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
  intro o W _ _ _ T I _ ε n V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hB₁ hB₂ f₁ f₂ m y y'
  obtain ⟨k₁, hk₁, U₁, -, hU₁⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₁ s₁ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₁ hB₁) e₁
    (dataFrom_ofDeg T ω₁ s₁ ε n D₁ hB₁ e₁ β₁ ββ₁ w₁ f₁) y (φ.symm.toAddMonoidHom (φ y'))
  obtain ⟨k₂, hk₂, U₂, -, hU₂⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₂ s₂ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₂ hB₂) e₂
    (dataFrom_ofDeg T ω₂ s₂ ε n D₂ hB₂ e₂ β₂ ββ₂ w₂ f₂) (φ y) (φ y')
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_iota (F := F) hB₁ y
  obtain ⟨g', ha, hg'⟩ := m.2.2.2.2 y g hg
  obtain ⟨u, hu⟩ := m.2.2.2.1 (φ y')
  let z : (TK V).left := closedPoint (FractionRing V)
  obtain ⟨J₁, gJ₁, cJ₁⟩ := exists_good_closed D₁ z
  obtain ⟨J₂, gJ₂, cJ₂⟩ := exists_good_closed D₂ z
  obtain ⟨J, hJ, hl, hr⟩ := exists_good_join D₁.P.isLB D₂.P.isLB gJ₁ gJ₂
  have key := act_val_frac V D₂ D₁ b φ.symm.toAddMonoidHom F y (φ y) g g' hg hg' ha (φ y') u hu z J hJ
  have t₁ := ((GlobalTheory.PolDeg.Wit.exists_tau D₁ y (φ.symm.toAddMonoidHom (φ y'))).choose_spec.2 _ (𝟙 _) z (rl J)
    ((isPart_inl _ _).good hJ)).symm.trans (hU₁ z (rl J) ((isPart_inl _ _).good hJ))
  have t₂ := ((GlobalTheory.PolDeg.Wit.exists_tau D₂ (φ y) (φ y')).choose_spec.2 _ (𝟙 _) z (rr J)
    ((isPart_inr _ _).good hJ)).symm.trans (hU₂ z (rr J) ((isPart_inr _ _).good hJ))
  obtain ⟨v₁, hv₁⟩ := val_closed U₁ (𝟙 _) z (rl J) (fun k => by erw [hl]; exact cJ₁ _)
  obtain ⟨v₂, hv₂⟩ := val_closed U₂ (𝟙 _) z (rr J) (fun k => by erw [hr]; exact cJ₂ _)
  obtain ⟨v₃, hv₃⟩ := val_closed u (D₁.c y).left z J (fun k => by
    rcases k with k | k
    · have h1 := cJ₁ ((D₁.c y).left ≫ D₁.Oφ (𝟙 _) (φ.symm.toAddMonoidHom (φ y')) k)
      erw [← hl] at h1
      have h2 := ((isPart_inl D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inl, Category.assoc] at h2 ⊢
      exact h2
    · have h1 := cJ₂ ((D₁.c y).left ≫ D₂.Oφ b (φ y') k)
      erw [← hr] at h1
      have h2 := ((isPart_inr D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inr, Category.assoc] at h2 ⊢
      exact h2)
  have q₁ : (toUnit (TK V)).left = (TK V).hom ≫ 𝟙 (Sp V) := by simp
  have q₃ : ptK (D₁.c y) = (TK V).hom ≫ (D₁.c y).left := by simp [ptK]
  rw [← q₁] at hv₁ hv₂
  rw [← q₃] at hv₃
  have um : ∀ a c : (FractionRing V)ˣ, unitOn (a * c) = unitOn a * unitOn c := fun a c => map_mul _ a c
  have E : gm (𝟙 (TK V).left) z ⊤ (unitOn (k₂ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₂)) =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (k₁ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₁ *
        Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₃)) := by
    rw [um, um, um, map_mul, map_mul, map_mul, ← hv₁, ← hv₂, ← hv₃, ← t₂, ← t₁]
    exact key
  have inj := GlobalTheory.DefectHom.gm_unitOn_inj z E
  have hc := congrArg (fun x : (FractionRing V)ˣ => (x : FractionRing V)) inj
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hc
  have hk₁' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
    have h' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ (φ.symm (φ y')))) := by
      exact hk₁
    rw [h', φ.symm_apply_apply]
  have hk₂' : (k₂ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) := by
    exact hk₂
  refine ⟨v₁ * v₃ * v₂⁻¹, ?_⟩
  rw [← hk₂', ← hk₁']
  have hv2 : algebraMap V (FractionRing V) (v₂ : V) * algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(k₂ : FractionRing V)) * hv2 + algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) * hc

end GlobalTheory.TInj.PerUnit

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.comesFromBase_of_refines_polarisedData : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (ρ : R →+* V) (ω : W →+* R) (s : I → R) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (D : DegPre V) (e' : D.X ≃+ Q.X), Function.Injective ρ → DataFrom T ω s ε n Q e → Refines Q ρ D e' → ∃ β ββ w, From T (ρ.comp ω) (fun i => ρ (s i)) ε n D (e'.trans e) β ββ w := by
  first | exact @GlobalTheory.TInj.FromRefine.from_of_refines | exact GlobalTheory.TInj.FromRefine.from_of_refines | (intros; apply GlobalTheory.TInj.FromRefine.from_of_refines <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem spMap_comp_tf {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V) {F₀ F : Type}
    [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (hj : Ext f j) :
    spMap j ≫ (TF (R := R) F₀).hom = (TF (R := V) F).hom ≫ spMap f := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

theorem tr_base {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {f : R →+* V} {D₀ : DegPre R}
    {D : DegPre V} {hD : IsPullDeg f D₀ D} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F]
    [Algebra (FractionRing V) F] {j : F₀ →+* F} (hj : Ext f j) {g₀ : GtPtF D₀ F₀} {g : GtPtF D F}
    (h : Tr f hD j g₀ g) {X : Scheme.{0}} (m : D₀.P.A.left ⟶ X) (k : Sp R ⟶ X)
    (hg₀ : g₀.b.left ≫ m = (TF (R := R) F₀).hom ≫ k) :
    g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f)) ≫ m = (TF (R := V) F).hom ≫ spMap f ≫ k := by
  obtain ⟨g₁, ⟨hb, -⟩, hp⟩ := h
  rw [← Category.assoc, hp.1, hb, Category.assoc, hg₀, ← Category.assoc, spMap_comp_tf f j hj, Category.assoc]

theorem exists_level_pairs : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (D₁ D₂ : DegData V J') (ω : L.W →+* R) (β : D₀.toPre.P.A.left ⟶ L.T.B.left), IsGrpPullback D₀.toPre.P.A L.T.B (spMap ω) β → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ → Ext f₂ j₂ → (∀ p₀ : QkPt D₀.toPre F₀ n, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = 0 ∧ p₁.g.b.left ≫ ((hD₁.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₁)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₁.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ ((hD₂.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₂)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₂.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) := by
  intro o _ ζ n L hn R _ _ V _ _ J J' D₀ D₁ D₂ ω β hβ f₁ f₂ hD₁ hD₂ F₀ _ _ _ F _ _ j₁ j₂ b φ hj₁ hj₂ H l
  have hc := IsGrpPullback.comp hβ L.cart
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.SiegelPull.push_surjective hc (TF (R := R) F₀) (toUnit _ ≫ L.F.univ.lev l)
  have hb₀' : b₀.left ≫ β ≫ L.β = (TF (R := R) F₀).hom ≫ spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫
      (L.F.univ.lev l).left := by
    have e := congrArg (fun z => z.left) hb₀
    simp only [pushHom, pushPt, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at e
    rw [e]
    simp
  have hpow : b₀ ^ n = 1 := by
    apply GlobalTheory.SiegelPull.push_injective hc
    rw [map_pow, hb₀, ← MonObj.comp_pow, L.F.univ.lev_tors, MonObj.comp_one, map_one]
  obtain ⟨p₀, hp₀y, hp₀b⟩ := GlobalTheory.TInj.exists_qk_zero_over R D₀.toPre D₀.tau_bimult F₀ n hn b₀ hpow
  obtain ⟨p₁, p₂, h1y, htr1, h2y, htr2, hq⟩ := H p₀
  have hg₀ : p₀.g.b.left ≫ β ≫ L.β = (TF (R := R) F₀).hom ≫ (spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫
      (L.F.univ.lev l).left) := by rw [hp₀b, hb₀']
  have hsp : ∀ f : R →+* V, spMap (f.comp ω) = spMap f ≫ spMap ω := fun f => by
    simp only [spMap, ← Spec.map_comp]; rfl
  refine ⟨p₁, p₂, by rw [h1y, hp₀y, map_zero], ?_, by rw [h2y, hp₀y, map_zero], ?_, hq⟩
  · have e := tr_base hj₁ htr1 _ _ hg₀
    rw [hsp]
    simpa only [Category.assoc] using e
  · have e := tr_base hj₂ htr2 _ _ hg₀
    rw [hsp]
    simpa only [Category.assoc] using e

end GlobalTheory.TInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.characterValues_galoisFixed_of_idempotent_torsion : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)), ∀ t : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtAct F.o F.e t t → (∃ z : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtF.IsNsmul n t z ∧ z.IsZero) → spMap σ.toAlgHom.toRingHom ≫ t.b.left = t.b.left → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (t.s χ) (LB.pullGen D'.toPre.P.L _ _ (t.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  first | exact @GlobalTheory.Mum.ETors.corr_pullGen_of_torsion | exact GlobalTheory.Mum.ETors.corr_pullGen_of_torsion | (intros; apply GlobalTheory.Mum.ETors.corr_pullGen_of_torsion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotent_image_base_point_rational_fractionField : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → ∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left := by
  first | exact @GlobalTheory.Mum.RatBase.ratBase | exact GlobalTheory.Mum.RatBase.ratBase | (intros; apply GlobalTheory.Mum.RatBase.ratBase <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_nsmul_eq_of_tmap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B),
      tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  intro K _ l _ hl A B f φ hf
  refine exists_nsmul_eq_of_kills_torsion K A B f l hl fun x hx => ?_
  obtain ⟨t, ht⟩ := (tl_lev_surj_ker K l A 1).1 x (by rwa [pow_one])
  have h1 : (tmap l A B f t).lev 1 = x ≫ f.hom := by rw [lev_tmap, ht]
  rw [← h1, hf, LinearMap.smul_apply]
  exact ((tl_lev_surj_ker K l B 1).2 _).2 ⟨φ t, by rw [pow_one]⟩

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem tmap_injective_card_coker_of_isIsogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧
      Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  intro K _ l _ hl A B f hf
  have hsurj : Function.Surjective (ptMap f) := (surjective_iff_ptMap_surjective K A B f).1 hf.2
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hdiv : ∀ x : A.Pt, ∃ y, y ^ l = x := pt_divisible K A l (Fact.out : l.Prime).ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.T.tateModuleMap_coker_card_eq_kerTorsion_card l A.Pt B.Pt (ptMap f) hdiv hsurj hfin
  exact ⟨h1, h2.trans (GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree K l hl A B f hf)⟩

end GlobalTheory.AV.AbVar
end
