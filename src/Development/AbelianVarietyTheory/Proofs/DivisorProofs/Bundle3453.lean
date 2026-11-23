module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPelUniformisationOfNormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GensOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_approxPoincareSeries_at_thetaSetup_points : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), IsE8 W → ThetaInt F W i → 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∃ d : ℕ, 1 ≤ d ∧ ApproxAt X₁ φ d := by
  first | exact @GlobalTheory.Poinc.exists_approxAt | exact GlobalTheory.Poinc.exists_approxAt | (intros; apply GlobalTheory.Poinc.exists_approxAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.CanonFam

theorem gm_iso {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (x : X) (p q : B.ι × A.ι)
    (hp : x ∈ B.U p.1 ⊓ A.U p.2) (hq : x ∈ B.U q.1 ⊓ A.U q.2) :
    gm (𝟙 X) x _ (w.s p) =
      gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x _ (w.s q) := by
  have hm : (𝟙 X : X ⟶ X) x ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2) := ⟨hp, hq⟩
  have e := congrArg (gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2))) (hw p q)
  exact (gm_res _ x _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) x p q hm) (gm_res _ x _ hm _))))

theorem lbIso_trans {X : Scheme.{0}} {A B C : LB X} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B) (H' : LBIso B C) :
    LBIso A C := by
  obtain ⟨w, hw⟩ := H
  obtain ⟨w', hw'⟩ := H'

  have cself : ∀ (x : X) (r : C.ι) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      gm (𝟙 X) x (C.U r ⊓ C.U r) (C.g r r) = 1 := by
    intro x r p hr hp
    have e := gm_iso hw' x (r, p) (r, p) ⟨hr, hp⟩ ⟨hr, hp⟩
    rw [gm_self hB (𝟙 X) x hp, inv_one, _root_.mul_one] at e
    exact mul_eq_right.1 e.symm
  have glue : ∀ (r : C.ι) (i : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U i)ˣ, ∀ (x : X) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      x ∈ A.U i → gm (𝟙 X) x _ s = gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := by
    intro r i
    let W : B.ι → X.Opens := fun p => C.U r ⊓ B.U p ⊓ A.U i
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U i := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => hx.1
    have l₂ : ∀ p, W p ≤ B.U p ⊓ A.U i := fun p x hx => ⟨hx.1.2, hx.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₁ p) (w'.s (r, p)) * res (l₂ p) (w.s (p, i))
    have hu : ∀ (x : X) (p : B.ι) (hx : x ∈ W p), gm (𝟙 X) x (W p) (u p) =
        gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := fun x p hx =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x (l₁ p) hx _) (gm_res _ x (l₂ p) hx _))
    obtain ⟨s, hs⟩ := glue_unit (C.U r ⊓ A.U i) W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, ⟨⟨hx.1, hp⟩, hx.2⟩⟩) u (fun p p' x hx => by
        rw [hu x p hx.1, hu x p' hx.2]
        have hr : x ∈ C.U r := hx.1.1.1
        have hp : x ∈ B.U p := hx.1.1.2
        have hp' : x ∈ B.U p' := hx.2.1.2
        have hi : x ∈ A.U i := hx.1.2
        rw [gm_iso hw' x (r, p) (r, p') ⟨hr, hp⟩ ⟨hr, hp'⟩, gm_iso hw x (p, i) (p', i) ⟨hp, hi⟩ ⟨hp', hi⟩]
        simp only []
        rw [cself x r p hr hp, gm_self hA (𝟙 X) x hi, inv_one]
        simp only [_root_.one_mul, _root_.mul_one]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun x p hr hp hi => ?_⟩
    have hx : x ∈ W p := ⟨⟨hr, hp⟩, hi⟩
    exact (gm_res _ x (l₀ p) hx s).symm.trans ((congrArg (gm (𝟙 X) x (W p)) (hs p)).trans (hu x p hx))
  choose s hs using glue
  refine ⟨⟨fun q => s q.1 q.2⟩, fun q q' => unit_ext fun x hx => ?_⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have hr : x ∈ C.U q.1 := hx.1.1
  have hi : x ∈ A.U q.2 := hx.1.2
  have hr' : x ∈ C.U q'.1 := hx.2.1
  have hi' : x ∈ A.U q'.2 := hx.2.2
  have hm : (𝟙 X : X ⟶ X) x ∈ C.U q.1 ⊓ A.U q.2 ⊓ (C.U q'.1 ⊓ A.U q'.2) := hx
  refine (gm_res _ x _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A C (𝟙 X) x q q' hm) (gm_res _ x _ hx _))).symm)
  show gm (𝟙 X) x _ (s q.1 q.2) = _ * _ * gm (𝟙 X) x _ (s q'.1 q'.2)
  rw [hs q.1 q.2 x p hr hp hi, hs q'.1 q'.2 x p hr' hp hi',
    gm_iso hw' x (q.1, p) (q'.1, p) ⟨hr, hp⟩ ⟨hr', hp⟩, gm_iso hw x (p, q.2) (p, q'.2) ⟨hp, hi⟩ ⟨hp, hi'⟩]
  simp only []
  rw [gm_self hB (𝟙 X) x hp, inv_one]
  simp only [_root_.one_mul, _root_.mul_one]
  ac_rfl

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

end GlobalTheory.Mum.CanonFam


open GlobalTheory.Mum.CanonFam in
theorem GlobalTheory.Mum.CanonFam.exists_unif_refines : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro R _ _ _ hR Q G _ _ P hG hC R' _ _ _ ρ hR' hinj hfin D ε hRef
  obtain ⟨D', F, hF, A', G', _, _, U', oA, oG, G₁, _, _, inc, pr, π, π₂, hG', hlin, hG₁, hinc, hpr, hip, hpi, hpb, hsq,
    hlb⟩ := GlobalTheory.T.refinement_isFactor_baseChange_canonicalMumfordFamily R hR Q G P hG hC R' ρ hR' hinj hfin D ε hRef
  obtain ⟨A, U, hU⟩ := GlobalTheory.T.idempotent_image_uniformised_by_factor_data R' (base_of_isCN hR') D D' F hF A' G' hG' U' oA oG hlin G₁ hG₁ inc pr hinc hpr hip hpi
  refine ⟨G₁, inferInstance, inferInstance, π, π₂, A, U, hpb, hsq, ?_⟩
  have l1 : (abelian₂ G₁ U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have l2 : (abelian₂ G' U'.LG.L).IsLB := DVR.linComb_isLB _ U'.LG.isLB _ _
  exact lbIso_trans l1 (pull_isLB l2 _) hU hlb
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.FamFrom

theorem rescale_inv_psi {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (χ : D.X) :
    (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) (fun y => (g y)⁻¹)).psi χ = D.psi χ := by
  show GlobalTheory.UU.scaleGen _ (GlobalTheory.UU.scaleGen _ _) = _
  unfold GlobalTheory.UU.scaleGen
  generalize D.psi χ = b
  cases b
  congr 1
  funext j
  have h1 : unitOn ((g χ)⁻¹) * unitOn (g χ) = 1 := by
    have hu : unitOn ((g χ)⁻¹ * g χ) = unitOn ((g χ)⁻¹) * unitOn (g χ) := map_mul _ _ _
    rw [← hu, inv_mul_cancel]
    exact Units.ext (map_one _)
  rw [← _root_.mul_assoc, ← map_mul, h1, map_one, _root_.one_mul]

theorem isPullDeg_rescale_inv {W R : Type} [CommRing W] [IsDomain W] [CommRing R] [IsDomain R] (φ : W →+* R)
    (D₀ : DegPre W) (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (hD : IsPullDeg φ D₀ D) :
    ∃ h : IsPullDeg φ D₀ (GlobalTheory.PolDeg.rescale (GlobalTheory.PolDeg.rescale D g) (fun y => (g y)⁻¹)),
      (∀ y, h.xe y = hD.xe y) ∧ h.e.hom.left = hD.e.hom.left :=
  ⟨{ hD with psi_pr := fun x => (rescale_inv_psi D g x).symm ▸ hD.psi_pr x }, fun _ => rfl, rfl⟩

end GlobalTheory.UCanon.FamFrom

namespace GlobalTheory.UCanon.FamFrom

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (iw : L.W →+* R), Function.Injective iw → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, s (.inl i) ∈ maximalIdeal R ∧ s (.inl i) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → (∀ i y, 0 ≤ ε (.inl i) y y) → (∀ y, y ≠ 0 → 0 < ∑ i, ε (.inl i) y y) → Nontrivial L.D.X → ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), DivFrom L P.D.toPre P.oD iw s ε e ∧ IsMonomial P.D.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e.toLinearMap (ε (.inl i))) := by
  intro E _ _ _ H Dl l c L R _ _ _ hB iw hiw m N s ε hε hs hu hpos hdef hnt
  letI := H.starRing
  have hw : H.w0 + star H.w0 = 1 := GlobalTheory.TauTwist.halfUnit_add_star H
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  letI iD : Module (𝓞 E) (mulDeg L.D l.M').X := L.mod
  obtain ⟨he0, hb0, hU0, oa0, hoa0, hW0⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen
  have hne : ∃ i, ε (.inl i) ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_ne (0 : L.D.X)
    have h := hdef y hy
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
    exact ⟨i, fun h0 => hi (by rw [h0]; rfl)⟩
  obtain ⟨D'', hD, iM, e, hxe, hPE, hTB, hPI, hfin, ⟨oa1, hoa1, hPW⟩, hmono, -, -, -⟩ :=
    GlobalTheory.UTautData.main L.W R (maximalIdeal R) iw hiw (mulDeg L.D l.M') (𝓞 E) oa0 H.w0 hw he0 hb0 hW0 hU0
      (fun i => s (.inl i)) (fun i => (hs i).2) (fun i => (hs i).1) (fun j => (hu j).unit) l.M' hM
      (fun i => ε (.inl i)) (fun j => ε (.inr j)) (fun i => hε _) hpos (fun j => hε _) hdef hne

  set T := GlobalTheory.UTautData.taut D'' e H.w0 (fun i => s (.inl i)) (fun i => (hs i).2) (fun j => (hu j).unit) l.M'
    (fun i => ε (.inl i)) (fun j => ε (.inr j)) with hT
  let D1 : DegData R (maximalIdeal R) := ⟨T, hPE, hTB, hPI, hfin⟩
  obtain ⟨t, P, hPD, hmod, hoD⟩ := GlobalTheory.T.exists_semiAbelian_pelUniformisation_of_norm H R hB D1 (inst := iM) oa1 hPW
  have key : ∀ (Dd : DegData R (maximalIdeal R)) [im : Module (𝓞 E) Dd.toPre.X] (od : Dd.toPre.OAct (𝓞 E)),
      Dd = D1 → HEq im iM → HEq od oa1 → ∃ e' : Dd.toPre.X ≃ₗ[𝓞 E] L.D.X,
        DivFrom L Dd.toPre od iw s ε e' ∧
        IsMonomial Dd.toPre (fun i => s (.inl i)) (fun i => (l.M' : ℤ) • pull e'.toLinearMap (ε (.inl i))) := by
    rintro Dd im od rfl h1 h2
    have h1' := eq_of_heq h1
    subst im
    have h2' := eq_of_heq h2
    subst od
    letI : Module (𝓞 E) D1.toPre.X := iM
    let e₁ : D1.toPre.X ≃ₗ[𝓞 E] L.D.X := e
    refine ⟨e₁, ?_, hmono⟩
    obtain ⟨h2p, hx2, he2⟩ := isPullDeg_rescale_inv iw (mulDeg L.D l.M') D''
      (GlobalTheory.UTautData.scaleFn (GlobalTheory.UTautData.coordsK (fun i => s (.inl i)) (fun i => (hs i).2) (fun j => (hu j).unit))
        H.w0 (GlobalTheory.UTautData.forms l.M' (fun i => pull e.toLinearMap (ε (.inl i)))
          (fun j => pull e.toLinearMap (ε (.inr j))))) hD
    refine ⟨_, h2p, fun y => ?_, fun y => (hx2 y).trans (hxe y).symm, fun x => ?_⟩
    · rw [inv_inv]
      refine (GlobalTheory.UTautData.scaleFn_coe _ _ _ _ _ _ _ _).trans ?_
      rw [Fintype.prod_sum_type]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        have h3 : e₁ (H.w0 • y) = H.w0 • e₁ y := e₁.map_smul H.w0 y
        show _ = algebraMap R (FractionRing R) (s (.inl i)) ^ ((l.M' : ℤ) * ε (.inl i) (e₁ y) (H.w0 • e₁ y))
        rw [← h3]
        rfl
      · refine Finset.prod_congr rfl fun j _ => ?_
        have h3 : e₁ (H.w0 • y) = H.w0 • e₁ y := e₁.map_smul H.w0 y
        show _ = algebraMap R (FractionRing R) (s (.inr j)) ^ ((l.M' : ℤ) * ε (.inr j) (e₁ y) (H.w0 • e₁ y))
        rw [← h3, (hu j).unit_spec]
        rfl
    · rw [he2]
      have h := hoa1 x
      rw [hoa0] at h
      exact h
  obtain ⟨e', h1, h2⟩ := key P.D P.oD hPD hmod hoD
  exact ⟨t, P, e', h1, h2⟩

end GlobalTheory.UCanon.FamFrom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_uSetup_ideal_over_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = A ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) ∧ UValThru Xo c C.i X₁.π Set.univ φ J₁ ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.UPoinc.exists_genericPoint_closure_eq_of_isClopen E H Dw hpq l Xo c C A hAc hAi hAm
  obtain ⟨X₁, -, hpr, hX₁⟩ := GlobalTheory.UPoinc.GSetup.exists_uSetup_proj E H Dw hpq l Xo c C η hη 0
  have hr := GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X₁ η A hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := GlobalTheory.T.unitary_exists_normalModel_effCartier_along_traits E H Dw hpq φ hφ l Xo c C X₁ hpr
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ := GlobalTheory.T.exists_idealSheaf_descending_divisor_power E H Dw hpq φ hφ l Xo c C X₁ ι Y πY D hι hhom hprop hnY hsupp hord
  obtain ⟨hs, ho⟩ := GlobalTheory.UPoinc.ideal_orders_of_proper_model E H Dw hpq φ hφ l Xo c C X₁ Y πY hhom hprop ι' J₁ hsupp' hord'
  exact ⟨X₁, ι', J₁, hι', hr, hs, ho⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegel_point_lifts_to_artinian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegelArtin.main | exact GlobalTheory.SiegelArtin.main | (intros; apply GlobalTheory.SiegelArtin.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.separate_two_points_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  first | exact @GlobalTheory.NefBigSep.separate_nef_big | exact GlobalTheory.NefBigSep.separate_nef_big | (intros; apply GlobalTheory.NefBigSep.separate_nef_big <;> assumption)
end
