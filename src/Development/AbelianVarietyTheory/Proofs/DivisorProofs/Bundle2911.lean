module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDvrOfCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumMult

theorem chartExpOn_of_tExp_gen {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (e : ℕ) (b : thickObj R I e G ⟶ thickObj R I e G) (n : ℕ)
    (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U b n 0) (hF : Small I (w := id) F)
    (hf : ∀ β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (f β) x z J = sval (F β) x z J)
    (hτ : TExp U τ (w := id) F) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W))
    (hg : ∀ (z : (thickObj R I e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG I e G).left) = i' 0 →
      gs (𝟙 _) z W g = sval τ (𝟙 _) z J') : ChartExpOn U e n i' W g f := by
  classical
  let S : Finset D.toPre.X := (hF e).toFinset
  have hS : ∀ α ∉ S, Van I (F α) e := fun α hα => by_contra fun h => hα ((hF e).mem_toFinset.2 h)
  refine ⟨S, fun α hα j => fn_ext fun y hy => ?_, ?_⟩
  · choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
    rw [Category.id_comp]
    have h0 : sval (f α) (DVR.pGl U e) y J = 0 := (hf α _ _ y J hJ).trans (hS α hα _ (U.gt e).q.left y J hJ)
    exact (sec_trans (f α) _ y hy (Good.mem hJ _ _)).trans ((congrArg _ h0).trans (mul_zero _))
  · rintro ⟨p₁, p₂⟩ jf jt hj hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ _ hc (by
      rintro (a | a | a)
      exacts [mem_pull.1 hy.1.1.1.1, Set.mem_iInter.1 (U.expW_le_f e _ _ jf jt a.1.2 hy.1) a.2,
        Set.mem_iInter.1 (U.expWeight_le_chart_weight e _ _ jf jt a.1.2 hy.1) a.2])
    obtain ⟨J', hJ', eJ'⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit.{1}) (fun _ => 𝟙 _ ≫ (fstG I e G).left)
      (fun _ => p₂ PUnit.unit) (fun _ _ _ => rfl) (fun _ => mem_pull.1 hy.1.1.1.2)
    have e₀ : J (𝟙 _ ≫ (U.gt e).pG.left) = p₁ PUnit.unit := by rw [Category.id_comp]; exact eJ (.inl PUnit.unit)
    have e₁ : J' (𝟙 _ ≫ (fstG I e G).left) = p₂ PUnit.unit := eJ' PUnit.unit
    have H := hτ S hS _ (𝟙 _) y J J' hJ hJ'
    rw [evalE, zpow_zero, _root_.mul_one, zpow_natCast, e₀, e₁] at H
    refine ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _) y inf_le_right hy g).trans
      (hg y J' hy.2 hJ' (e₁.trans hj.symm))))).trans
      (H.trans (Eq.symm ?_))
    · rw [← Units.val_pow_eq_pow_val, gs_unit (𝟙 _) y _ hy, map_pow]
      exact congrArg (fun u => (u ^ n).val) (gm_res (𝟙 _) y _ hy _)
    · refine (DVR.gs_fsum (𝟙 _) y _ hy _ _).trans (Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (Finset.sum_attach S _))
      have l₁ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expW_le_f e (p₁, p₂) i' jf jt α.2)
      have l₂ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expWeight_le_chart_weight e (p₁, p₂) i' jf jt α.2)
      have a₁ := (gs_res (𝟙 _) y l₁ hy (((DVR.pGl U e).app _).hom ((f α.1).f (jf α.1)))).trans
        (gs_pull (𝟙 _) (DVR.pGl U e) y (LB.wchart D.toPre.P.L (D.toPre.famφB α.1) (jf α.1)) (l₁ hy) ((f α.1).f (jf α.1)))
      have a₂ := (gs_unit (𝟙 _) y _ hy (res l₂ ((DVR.tG U e α.1).s (jt α.1)))).trans
        (congrArg Units.val (gm_res (𝟙 _) y l₂ hy _))
      have b₁ := sval_of (f α.1) (𝟙 _ ≫ DVR.pGl U e) y J (jf α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inl (α, a))))
      have b₂ := val_of (DVR.tG U e α.1) (𝟙 _) y J (jt α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inr (α, a))))
      exact (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (a₁.trans (b₁.symm.trans (hf α.1 _ _ y J hJ)))
        (a₂.trans (congrArg Units.val b₂.symm)))

theorem chartExpOn_of_tExp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U.toUnifPre b n 0), Small (maximalIdeal R) (w := id) F → (∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f β) x z J = sval (F β) x z J)) → TExp U.toUnifPre τ (w := id) F → ∀ (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R (maximalIdeal R) e G).left.Opens) (g : Γ((thickObj R (maximalIdeal R) e G).left, W)), (∀ (z : (thickObj R (maximalIdeal R) e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG (maximalIdeal R) e G).left) = i' 0 → gs (𝟙 _) z W g = sval τ (𝟙 _) z J') → GlobalTheory.MumMult.ChartExpOn U.toUnifPre e n i' W g f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U e b n F f τ hF hf hτ i' W g hg =>
    chartExpOn_of_tExp_gen U.toUnifPre e b n F f τ hF hf hτ i' W g hg

end GlobalTheory.MumMult
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DenseGlue

open GlobalTheory.PicGlue GlobalTheory.CechPic

theorem cls_pull_comp {P T T' : Scheme.{0}} {W : P.Opens} {L : LB P} (hL : IsOn W L) (g : T ⟶ P)
    (hg : ∀ z, g z ∈ W) (s : T' ⟶ T) {g' : T' ⟶ P} (w : s ≫ g = g') (h : (L.pull g).IsLB)
    (h' : (L.pull g').IsLB) : cls (L.pull g') h' = CechPic.pull s (cls (L.pull g) h) := by
  subst w
  rw [← cls_pull h s (pull_isLB h s)]
  exact ((cls_eq_iff _ _).2 (isOn_pull_comp P _ _ _ L g s hL hg)).symm

theorem exists_rigidify {X P : Scheme.{0}} (p : P ⟶ X) {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {V : X.Opens} {M : LB P}
    (hM : IsOn (p ⁻¹ᵁ V) M) : ∃ M' : LB P, IsOn (p ⁻¹ᵁ V) M' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ P),
      (∀ z, g z ∈ p ⁻¹ᵁ V) → ∀ (h₁ : (M'.pull g).IsLB) (h₂ : (M.pull g).IsLB) (h₃ : (M.pull (g ≫ p ≫ e)).IsLB),
        cls _ h₁ = cls _ h₂ - cls _ h₃ := by
  have hpe := retract_section_apply p e he
  have hι : ∀ z, (p ⁻¹ᵁ V).ι z ∈ p ⁻¹ᵁ V := fun z ↦ z.2
  have hι' : ∀ z, ((p ⁻¹ᵁ V).ι ≫ p ≫ e) z ∈ p ⁻¹ᵁ V := fun z ↦ by
    change p (e (p _)) ∈ V
    rw [hpe]
    exact z.2
  have k₁ := pull_isLB_of_isOn P _ _ M _ hM hι
  have k₂ := pull_isLB_of_isOn P _ _ M _ hM hι'
  obtain ⟨N, hN, hc⟩ := cls_surj (cls _ k₁ - cls _ k₂)
  obtain ⟨M', hM', hi⟩ := exists_isOn_of_openImmersion P _ (p ⁻¹ᵁ V).ι N hN
  rw [Scheme.Opens.opensRange_ι] at hM'
  refine ⟨M', hM', fun T g hg h₁ h₂ h₃ ↦ ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : T ⟶ (p ⁻¹ᵁ V).toScheme, t ≫ (p ⁻¹ᵁ V).ι = g :=
    ⟨IsOpenImmersion.lift (p ⁻¹ᵁ V).ι g (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg z), IsOpenImmersion.lift_fac _ _ _⟩
  have k₃ := pull_isLB_of_isOn P _ _ M' _ hM' hι
  rw [cls_pull_comp hM' _ hι t ht k₃, cls_pull_comp hM _ hι t ht k₁,
    cls_pull_comp hM _ hι' t (by rw [reassoc_of% ht]) k₂, ← map_sub, ← hc, (cls_eq_iff k₃ hN).2 hi]

theorem exists_glue_of_rigid {X P : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X]
    (U : X.Opens) [IsDominant U.ι] (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P}
    (he : e ≫ p = 𝟙 X) {L₀ : LB P} (h₀ : IsOn (p ⁻¹ᵁ U) L₀) (t₀ : ∃ t : LB.Gen (L₀.pull (U.ι ≫ e)), t.IsGen)
    {Ix : Type} (V : Ix → X.Opens) (hV : ∀ y, ∃ i, y ∈ V i) (L : Ix → LB P) (hL : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i))
    (t : ∀ i, ∃ t : LB.Gen ((L i).pull ((V i).ι ≫ e)), t.IsGen)
    (hi : ∀ i, LBIso ((L i).pull (p ⁻¹ᵁ (V i ⊓ U)).ι) (L₀.pull (p ⁻¹ᵁ (V i ⊓ U)).ι)) :
    ∃ N : LB P, N.IsLB ∧ ∀ i, ∃ v : Cmp (p ⁻¹ᵁ V i) N (L i), IsoOn (p ⁻¹ᵁ V i) N (L i) v := by
  have hpe := retract_section_apply p e he
  have hR : ∀ {W : X.Opens} {M : LB P}, IsOn (p ⁻¹ᵁ W) M → (∃ t : LB.Gen (M.pull (W.ι ≫ e)), t.IsGen) →
      ∃ r : RigD e M, RigOn e M r := fun {W M} hM ht ↦
    rigOn_of_triv_open P X e W M (fun a y hy ↦ by
      have : p (e y) ∈ W := hM.le a hy
      rwa [hpe] at this) ht
  obtain ⟨r₀, hr₀⟩ := hR h₀ t₀
  choose r hr using fun i ↦ hR (hL i) (t i)
  have hv : ∀ i, ∃ v : Cmp (p ⁻¹ᵁ (V i ⊓ U)) (L i) L₀, IsoOn _ (L i) L₀ v ∧
      PicGlue.Norm e _ (L i) L₀ v (r i) r₀ := fun i ↦ by
    obtain ⟨w, hw⟩ := isoOn_of_lbIso P _ (L i) L₀ (hi i)
    exact exists_norm P X p e he _ _ _ (L i) L₀ w (r i) r₀ (hL i) h₀ (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr i) hr₀
  choose v hv hn using hv
  obtain ⟨w, hw, hc⟩ := exists_cocycle U p he h₀ r₀ V L hL r v hv hn
  exact lb_glue P Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL hw hc

theorem exists_glue {X P U Q : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : Dense (Set.range j)) (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p]
    {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {a : Q ⟶ P} {π : Q ⟶ U} (sq : IsPullback a π p j) {eU : U ⟶ Q}
    (w : eU ≫ a = j ≫ e) {L : LB Q} (hL : L.IsLB) (hrig : ∃ t : LB.Gen (L.pull eU), t.IsGen)
    (H : ∀ y : X, y ∉ Set.range j → ∃ V : X.Opens, y ∈ V ∧ ∃ M : LB P, IsOn (p ⁻¹ᵁ V) M ∧
      LBIso (M.pull ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a)) (L.pull (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι)) :
    ∃ M : LB P, M.IsLB ∧ LBIso (M.pull a) L := by
  have hpe := retract_section_apply p e he
  have : IsOpenImmersion a := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip ‹_›
  let U₀ : X.Opens := j.opensRange
  have : IsDominant U₀.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hj⟩
  have hD : a.opensRange = p ⁻¹ᵁ U₀ := by
    ext x
    change x ∈ Set.range a ↔ p x ∈ Set.range j
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨π q, by rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]⟩
    · intro hx
      obtain ⟨q, rfl⟩ : x ∈ Set.range (pullback.fst p j) := by
        rw [Scheme.Pullback.range_fst]
        exact hx
      exact ⟨sq.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_fst]⟩
  obtain ⟨L₀, h₀, i₀⟩ := exists_isOn_of_openImmersion P Q a L hL
  rw [hD] at h₀
  have ha : ∀ z, a z ∈ p ⁻¹ᵁ U₀ := fun z ↦ hD ▸ ⟨z, rfl⟩
  have k₀ := pull_isLB_of_isOn P _ _ L₀ a h₀ ha
  have c₀ : cls _ k₀ = cls L hL := (cls_eq_iff _ _).2 i₀

  have z₀ : ∀ (T : Scheme.{0}) (s : T ⟶ X), (∀ z, s z ∈ U₀) → ∀ h : (L₀.pull (s ≫ e)).IsLB, cls _ h = 0 := by
    intro T s hs h
    let κ := IsOpenImmersion.lift j s (by rintro _ ⟨z, rfl⟩; exact hs z)
    have hκ : κ ≫ j = s := IsOpenImmersion.lift_fac _ _ _
    rw [cls_pull_comp h₀ a ha (κ ≫ eU) (by rw [Category.assoc, w, reassoc_of% hκ]) k₀, c₀, pull_comp,
      ← cls_pull hL eU (pull_isLB hL eU), (cls_eq_zero_iff _).2 hrig, map_zero]
  have hse : ∀ {T : Scheme.{0}} (s : T ⟶ X) {W : X.Opens}, (∀ z, s z ∈ W) → ∀ z, (s ≫ e) z ∈ p ⁻¹ᵁ W :=
    fun s W hs z ↦ by
      change p (e (s z)) ∈ W
      rw [hpe]
      exact hs z
  have t₀ : ∃ t : LB.Gen (L₀.pull (U₀.ι ≫ e)), t.IsGen :=
    (cls_eq_zero_iff (pull_isLB_of_isOn P _ _ L₀ _ h₀ (hse U₀.ι fun z ↦ z.2))).1 (z₀ _ U₀.ι (fun z ↦ z.2) _)
  have key : ∀ o : Option X, ∃ (V : X.Opens) (M : LB P), (∀ y, o = some y → y ∉ U₀ → y ∈ V) ∧
      (o = none → V = U₀ ∧ M = L₀) ∧ IsOn (p ⁻¹ᵁ V) M ∧ (∃ t : LB.Gen (M.pull (V.ι ≫ e)), t.IsGen) ∧
      LBIso (M.pull (p ⁻¹ᵁ (V ⊓ U₀)).ι) (L₀.pull (p ⁻¹ᵁ (V ⊓ U₀)).ι) := fun o ↦ by
    by_cases ho : ∃ y, o = some y ∧ y ∉ U₀
    swap
    · have k := pull_isLB_of_isOn P _ _ L₀ (p ⁻¹ᵁ (U₀ ⊓ U₀)).ι h₀ fun z ↦ z.2.1
      exact ⟨U₀, L₀, fun y h h' ↦ (ho ⟨y, h, h'⟩).elim, fun _ ↦ ⟨rfl, rfl⟩, h₀, t₀, (cls_eq_iff k k).1 rfl⟩
    obtain ⟨y, rfl, hy⟩ := ho
    obtain ⟨V, hyV, M, hM, iM⟩ := H y hy
    obtain ⟨M', hM', hc⟩ := exists_rigidify p he hM
    have hb : ∀ z, ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a) z ∈ p ⁻¹ᵁ V := fun z ↦ z.2
    have kb := pull_isLB_of_isOn P _ _ M _ hM hb
    have cmp : ∀ (T : Scheme.{0}) (g : T ⟶ P), (∀ z, g z ∈ p ⁻¹ᵁ (V ⊓ U₀)) → ∀ (h₁ : (M.pull g).IsLB)
        (h₂ : (L₀.pull g).IsLB), cls _ h₁ = cls _ h₂ := fun T g hg h₁ h₂ ↦ by
      let t := IsOpenImmersion.lift ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a) g (by
        rintro _ ⟨z, rfl⟩
        obtain ⟨q, hq⟩ : g z ∈ a.opensRange := hD ▸ (hg z).2
        exact ⟨⟨q, show a q ∈ p ⁻¹ᵁ V from hq ▸ (hg z).1⟩, hq⟩)
      have ht : t ≫ (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a = g := IsOpenImmersion.lift_fac _ _ _
      rw [cls_pull_comp hM _ hb t ht kb, (cls_eq_iff kb (pull_isLB hL _)).2 iM,
        cls_pull_comp h₀ a ha (t ≫ (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι) (by rw [Category.assoc, ht]) k₀, c₀, pull_comp,
        cls_pull hL]
    refine ⟨V, M', fun y' h _ ↦ by cases h; exact hyV, fun h ↦ (by cases h), hM', ?_, ?_⟩
    · have hs := hse V.ι fun z ↦ z.2
      have k₂ := pull_isLB_of_isOn P _ _ M _ hM hs
      have e₁ : (V.ι ≫ e) ≫ p ≫ e = V.ι ≫ e := by rw [Category.assoc, reassoc_of% he]
      refine (cls_eq_zero_iff (pull_isLB_of_isOn P _ _ M' _ hM' hs)).1 ?_
      rw [hc _ _ hs _ k₂ (e₁.symm ▸ k₂), sub_eq_zero]
      exact (cls_pull_comp hM _ hs (𝟙 _) (by rw [Category.id_comp, e₁]) k₂ _).trans (pull_id _) |>.symm
    · let g := (p ⁻¹ᵁ (V ⊓ U₀)).ι
      have hg : ∀ z, g z ∈ p ⁻¹ᵁ (V ⊓ U₀) := fun z ↦ z.2
      have hg' : ∀ z, ((g ≫ p) ≫ e) z ∈ p ⁻¹ᵁ (V ⊓ U₀) := hse (g ≫ p) hg
      have k₁ := pull_isLB_of_isOn P _ _ M' g hM' fun z ↦ (hg z).1
      have k₂ := pull_isLB_of_isOn P _ _ M g hM fun z ↦ (hg z).1
      have k₃ := pull_isLB_of_isOn P _ _ M _ hM fun z ↦ (hg' z).1
      have k₄ := pull_isLB_of_isOn P _ _ L₀ g h₀ fun z ↦ (hg z).2
      have k₅ := pull_isLB_of_isOn P _ _ L₀ _ h₀ fun z ↦ (hg' z).2
      refine (cls_eq_iff k₁ k₄).1 ?_
      rw [hc _ g (fun z ↦ (hg z).1) k₁ k₂ k₃, cmp _ g hg k₂ k₄]
      exact sub_eq_self.2 ((cmp _ _ hg' k₃ k₅).trans (z₀ _ (g ≫ p) (fun z ↦ (hg z).2) k₅))
  choose V M h₁ h₂ h₃ h₄ h₅ using key
  obtain ⟨N, hN, hv⟩ := exists_glue_of_rigid U₀ p he h₀ t₀ V (fun y ↦ by
    by_cases hy : y ∈ U₀
    · exact ⟨none, (h₂ none rfl).1 ▸ hy⟩
    · exact ⟨some y, h₁ _ y rfl hy⟩) M h₃ h₄ h₅
  obtain ⟨v, hv⟩ := hv none
  have i₁ := lbIso_pull_of_isoOn P Q _ N (M none) v a hv fun z ↦ (h₂ none rfl).1 ▸ ha z
  rw [(h₂ none rfl).2] at i₁
  exact ⟨N, hN, (cls_eq_iff (pull_isLB hN a) hL).1 (((cls_eq_iff _ k₀).2 i₁).trans c₀)⟩

end GlobalTheory.DenseGlue
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OrthPt

variable {R : Type} [CommRing R]

theorem iSup_parCov {A B : Over (Sp R)} {K : Type} {W : K → (A ⊗ B).left.Opens} (hW : ⨆ i, W i = ⊤)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : ⨆ i, parCov W x i = ⊤ := by
  unfold parCov
  exact (x ▷ B).left.iSup_preimage_eq_top hW

theorem sm_parCov {A B : Over (Sp R)} {K : Type} {W : K → (A ⊗ B).left.Opens}
    {D D' E : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E]
    (φ : D →ₐ[R] D') (x : Pt A D) (z : Pt (SpAlg R D' ⊗ B) E) (h : Sm (parCov W (spOver φ ≫ x)) z) :
    Sm (parCov W x) (z ≫ spOver φ ▷ B) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  unfold parCov at hi ⊢
  rw [comp_whiskerRight, Over.comp_left, Scheme.Hom.comp_preimage] at hi
  rw [Over.comp_left, Scheme.Hom.comp_preimage]
  exact hi

theorem sumMul_elim {B : Over (Sp R)} {D : Type} [CommRing D] [Algebra R D] {I₁ I₂ I₃ : Type} [Fintype I₁]
    [Fintype I₂] [Fintype I₃] (d₁ : I₁ → D) (d₂ : I₂ → D) (d₃ : I₃ → D)
    (β₁ : I₁ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (β₂ : I₂ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (β₃ : I₃ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E')
    (z : Pt (SpAlg R D ⊗ B) E) :
    sumMul (Sum.elim d₁ (Sum.elim (fun i ↦ -d₂ i) (fun i ↦ -d₃ i)))
        (fun i ↦ fv (Sum.elim β₁ (Sum.elim β₂ β₃) i)) E E' ψ z =
      sumMul d₁ (fun i ↦ fv (β₁ i)) E E' ψ z - sumMul d₂ (fun i ↦ fv (β₂ i)) E E' ψ z -
        sumMul d₃ (fun i ↦ fv (β₃ i)) E E' ψ z := by
  simp only [sumMul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, neg_mul, Finset.sum_neg_distrib]
  ring

theorem exists_isCob_of_mem_fil : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (K : Type) (W : K → (A ⊗ B).left.Opens), ⨆ i, W i = ⊤ → ∀ (J : Type) [Fintype J] (a : J → Fn1 A) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → IsCupCob W a (fun i ↦ fv (β i)) n → ∀ y ∈ Fil B, ∃ k : Fn0 A, IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, a i D D' φ x * algebraMap R D' (y ⟨_, hβ i⟩)) k := by
  intro H R _ A B _ g hB hg K W hW J _ a β hβ n ha hn y hy
  have hP : ∀ f : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f ∈ primDR B := fun f ↦ by
    have h : primDR B = ⊤ := ((GlobalTheory.abelianDeRham_free_baseChange_rigid H).1 R B g hB hg).1
    rw [h]; trivial
  have hfv : ∀ f : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)), IsCoc (whole B) (fv f) := fun f ↦ (fv_isCoc_and_ev_eq R B f).1
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ (m : ℕ) (d : Fin m → D) (c : Fin m → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (k : Fn0 (SpAlg R D ⊗ B)),
        IsCob (parCov W x) ((parCoc a (fun i ↦ fv (β i)) n x).add (sumMul d fun i ↦ fv (c i)).neg) k := by
    intro D _ _ x
    obtain ⟨u, hu, k₁, h₁⟩ := GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary R _ K (parCov W x) (iSup_parCov hW x) _
      (GlobalTheory.PtExt.parCoc_isCoc R A B K W J a _ n ha (fun i ↦ hfv _) hn D x)
    obtain ⟨m, d, c, k₂, h₂⟩ := GlobalTheory.T.cocycle_spec_prod_abelian_cohomologous_sum_mul H R B g hB hg D u hu
    refine ⟨m, d, c, fun E _ _ z ↦ k₁ E z + k₂ E z, ?_⟩
    intro E _ _ E' _ _ ψ z hz
    have e₁ := h₁ E E' ψ z hz
    have e₂ := h₂ E E' ψ z (sm_whole z)
    simp only [Fn1.add, Fn1.neg] at e₁ e₂ ⊢
    rw [map_add (f := _)]
    linear_combination e₁ + e₂
  choose m d c k hk using key
  refine ⟨fun D _ _ x ↦ ∑ j, d D x j * algebraMap R D (y ⟨_, hP (c D x j)⟩), ?_⟩
  intro D _ _ D' _ _ φ x _
  have hcob : IsCob (parCov W (spOver φ ≫ x))
      (sumMul (Sum.elim (d D' (spOver φ ≫ x)) (Sum.elim (fun i ↦ -φ (d D x i)) (fun i ↦ -a i D D' φ x)))
        (fun i ↦ fv (Sum.elim (c D' (spOver φ ≫ x)) (Sum.elim (c D x) β) i)))
      (fun E _ _ z ↦ k D x E (z ≫ spOver φ ▷ B) - k D' (spOver φ ≫ x) E z) := by
    intro E _ _ E' _ _ ψ z hz
    have e₁ := hk D' (spOver φ ≫ x) E E' ψ z hz
    have e₂ := hk D x E E' ψ (z ≫ spOver φ ▷ B) (sm_parCov φ x z hz)
    have e₃ := congrArg (fun u : Fn1 (SpAlg R D' ⊗ B) ↦ u E E' ψ z)
      (GlobalTheory.PtExt.parCoc_spOver R A B J a (fun i ↦ fv (β i)) n ha D D' φ x)
    have e₄ := congrArg (fun u : Fn1 (SpAlg R D' ⊗ B) ↦ u E E' ψ z)
      ((GlobalTheory.PtExt.SumMulFacts.main R D B _ (d D x) (fun i ↦ fv (c D x i))).2 D' φ)
    rw [sumMul_elim]
    simp only [Fn1.add, Fn1.neg, Fn1.pull] at e₁ e₂ e₃ e₄
    beta_reduce
    rw [map_sub, Category.assoc]
    linear_combination e₂ - e₁ + e₃ + e₄
  have h0 := GlobalTheory.T.sum_mul_hodgeFil_eq_zero_of_deRham_coboundary H R B g hB hg y hy D' _ _ _ (fun i ↦ hP _)
    (GlobalTheory.PtExt.isCob_whole_of_isCob_cover R _ K _ (iSup_parCov hW (spOver φ ≫ x)) _
      ((GlobalTheory.PtExt.SumMulFacts.main R D' B _ _ _).1 fun i ↦ hfv _) _ hcob)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at h0

  simp only [map_sum, map_mul, AlgHom.commutes]
  linear_combination -h0

end GlobalTheory.PtExt.OrthPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstants_firstJets_linearIndependent : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  first | exact @GlobalTheory.MBLow.TRank.main | exact GlobalTheory.MBLow.TRank.main | (intros; apply GlobalTheory.MBLow.TRank.main <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_scalar_cuspForm_indefinite_unitaryShimura : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → 1 ≤ Dw.p → 1 ≤ Dw.q → ¬ (∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)) → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  first | exact @GlobalTheory.ScalarCuspTwist.exists_scalar_cusp_indefinite | exact GlobalTheory.ScalarCuspTwist.exists_scalar_cusp_indefinite | (intros; apply GlobalTheory.ScalarCuspTwist.exists_scalar_cusp_indefinite <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  first | exact @GlobalTheory.AmpleFibre.isAmpleLB_fibre | exact GlobalTheory.AmpleFibre.isAmpleLB_fibre | (intros; apply GlobalTheory.AmpleFibre.isAmpleLB_fibre <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem pol_chernDens_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → HermLB p) (c : AlgChart p σ D), ∀ y ∈ c.e.source, FibreProj.pol (fun n => c.chernDens ((ArInt.comb L n).φ σ) y) = D.factorial * dens (fun i => MLine.ofHerm (L i) σ) c y := by
  intro k _ X p σ D L c y hy
  set H : Fin D → Matrix (Fin D) (Fin D) ℂ := fun j => MixDens.chernMat ((L j).φ σ) c y with hH
  have hc (n : Fin D → ℤ) : c.chernDens ((ArInt.comb L n).φ σ) y =
      D.factorial / Real.pi ^ D * (∑ j, (n j : ℂ) • H j).det.re := by
    rw [← MixDens.chernMat_comb k X p σ D (Fin D) L n c y hy]
    rfl
  have key := GlobalTheory.T.sum_neg_one_pow_card_det_sum_eq_sum_perm_det D H
  simp only [FibreProj.pol, hc, dens, MLine.ofHerm]
  have e2 : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => c.hess ((L (τ l)).φ σ) (pick ((L (τ l)).φ σ).isLB y) y j l).det)
      = ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := rfl
  rw [e2, ← key, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have : ((-1 : ℂ) ^ S.card) = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  trans (-1) ^ S.card * (D.factorial / Real.pi ^ D * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det.re)
  · simp only [apply_ite (Int.cast : ℤ → ℂ), Int.cast_neg, Int.cast_one, Int.cast_zero]
  · ring

end GlobalTheory.Mix
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.nefOnFiniteFieldFibres_pow_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → NefFib A → NefFib ((L.pow n).tens A) := by
  first | exact @GlobalTheory.NefFibTens.nefFib_pow_tens | exact GlobalTheory.NefFibTens.nefFib_pow_tens | (intros; apply GlobalTheory.NefFibTens.nefFib_pow_tens <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arithHeight_nonneg_vertical_of_nefOnFibres : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (C : HermLB p) (h : X → ℝ), NefFib C → C.IsArithHeight h → ∀ z : X, ¬ CharZero (X.residueField z) → 0 ≤ h z := by
  first | exact @GlobalTheory.VertHeight.height_nonneg_of_vertical | exact GlobalTheory.VertHeight.height_nonneg_of_vertical | (intros; apply GlobalTheory.VertHeight.height_nonneg_of_vertical <;> assumption)
end
