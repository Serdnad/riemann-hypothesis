module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle054
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle132
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.ScaleEqv

theorem eqv_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ D A F _ _ N lab E h c
  let gg : F →+* Γ((TFK (R := R) F ⊗ A.A).left, ⊤) :=
    (fst (TFK (R := R) F) A.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hgg : ∀ u : F, gg u = (fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F u) := fun _ => rfl
  have inv1 : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens) (u : Fˣ), resTop W (gg u.val) * resTop W (gg (u⁻¹).val) = 1 := by
    intro W u
    simp only [resTop]
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let S : F → SecK A.L (snd (TFK (R := R) F) A.A).left N → SecK A.L (snd (TFK (R := R) F) A.A).left N :=
    fun u t => DVR.SecOps.secScale (gg u) t
  have Sf : ∀ u t j, (S u t).f j = resTop _ (gg u) * t.f j := fun _ _ _ => rfl
  have SS : ∀ (u : Fˣ) t, S u.val (S (u⁻¹).val t) = t := by
    intro u t
    apply DVR.SecOps.sec_ext
    intro j
    rw [Sf, Sf, ← _root_.mul_assoc, inv1, _root_.one_mul]
  have SS' : ∀ (u : Fˣ) t, S (u⁻¹).val (S u.val t) = t := by
    intro u t
    have := SS u⁻¹ t
    rwa [inv_inv] at this
  refine ⟨fun s => S c.val (E s), ⟨?_, ?_, ?_, h.onto, h.frame, h.lift, ?_⟩, fun s j => rfl⟩
  · constructor
    · intro s t hst
      apply h.bij.1
      have := congrArg (S (c⁻¹).val) hst
      simpa only [SS'] using this
    · intro t
      obtain ⟨s, hs⟩ := h.bij.2 (S (c⁻¹).val t)
      exact ⟨s, by simp only [hs, SS]⟩
  · intro s s' s'' hs j
    simp only [Sf]
    rw [h.add s s' s'' hs j, mul_add]
  · intro u s s' hs j
    simp only [Sf]
    rw [h.smul u s s' hs j, mul_left_comm]
  · intro p w θ s s' hw hθ hph j
    have key := h.act p w θ s s' hw hθ hph j
    have e : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left := by
      rw [← Over.comp_left, translT, lift_fst]
    have hψ : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens),
        ((translT A.A θ.pt).left.app W).hom (resTop W (gg c.val)) =
          resTop ((translT A.A θ.pt).left ⁻¹ᵁ W) (gg c.val) := by
      intro W
      simp only [resTop]
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
      congr 1
      rw [hgg]
      have hT : ((translT A.A θ.pt).left.appTop).hom (((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val)) =
          ((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
      exact hT
    erw [Sf, Sf]
    erw [map_mul, map_mul, map_mul, hψ, key, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, mul_left_comm]

end GlobalTheory.Mum.ScaleEqv
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.USep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

def IsCov (C : UCompact Xo c) {M : Scheme.{0}} (g : M ⟶ C.Z) (z₁ : M)
    (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) : Prop :=
  IsNormalScheme M ∧
    (∃ (U : C.Z.Opens) (g' : M ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = g ∧
      Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧
    ζ ≫ pullback.fst _ _ = M.fromSpecStalk z₁ ≫ g ∧
    ∀ p : Sp (M.presheaf.stalk z₁), p.asIdeal = ⊥ → ζ p ∈ Set.range C.iF

section

variable {A : Type} [CommRing A] [IsLocalRing A] (ζ : Sp A ⟶ pullback C.z (spMap C.b)) {N₁ : ℕ}
  (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ A)

def HasTraits : Prop :=
  ∀ (T : UTrait Xo c) (ev : A →+* T.V), IsLocalHom ev → jK T.V ≫ spMap ev ≫ ζ = T.y ≫ C.iF →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b)

def IsMember {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V)
    (ξ : Sp V ⟶ pullback C.z (spMap C.b)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X)
    (h : Fin (Φ.m y) ≃ Fin Cm.m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ ζ = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k ^ 2 = ρ (Cm.s (h k)) ∧ ∀ a b, Φ.δ y k a b = ((l.M' : ℤ) • Cm.δ (h k)) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (p : IsPullDeg ρ Cm.P.D.toPre D), GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ p.xe.symm
      fun mu c => Φ.u y (fun _ => e.symm mu) c * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) fun _ => e.symm mu

end

def DescAt {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) : Prop :=
  ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
    (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
    (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧
    w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a

theorem sepAtB_iff {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {m N : ℕ}
    (s : Fin m ⊕ Fin N → V) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) :
    GlobalTheory.UChart.SepAtB Q τ₀ s ev k₀ ↔ (∀ i, ev (s (.inl i)) = 0) ∧ DescAt Q ev k₀ ∧
      ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* V), GlobalTheory.UChart.FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
        ∀ i, ev (s (.inr i)) ∈ k₀ := Iff.rfl

end GlobalTheory.USep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.UpExt

theorem over_famPull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  intro R _ _ I D k F₀ E F _ _ _ _ _ _ s h α
  have hL := D.P.isLB
  have g1 : ∀ {W : Scheme.{0}} (w : W), gs (𝟙 W) w ⊤ (1 : Γ(W, ⊤)) = 1 := fun w => by
    rw [gs_eq _ w ⊤ trivial, map_one, map_one]
  have h1 := (secScal_iff_val hL _ _ _ _).1 (h α)
  refine (secScal_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  have e1 : (𝟙 _ ≫ (DegPre.prB D F).left) = (famMap D E F).left ≫ (𝟙 _ ≫ (DegPre.prB D E).left) := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, famMap_snd]
  have e2 : (𝟙 _ ≫ (famMap D E F).left) = (famMap D E F).left ≫ 𝟙 _ := by
    rw [Category.id_comp, Category.comp_id]
  change _ = _ * sval (termPull D E F k α (s.s α)) _ y J
  rw [g1, _root_.one_mul, show sval (termPull D E F k α (s.s α)) (𝟙 _) y J =
      sval (s.s α) (𝟙 _ ≫ (famMap D E F).left) y J from sval_pullOver _ _ _ _ hJ, e1, e2, GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ,
    GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ, h1 _ _ (fun ψ => hJ _), g1, _root_.one_mul]

end GlobalTheory.Mum.UpExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_expandsF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  intro R _ _ I hI hC D A G _ _ U hG F _ _ _ N hN w₀ hw₀ lab hlab
  haveI := hC
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have gf : GlobalFnsSt := hL.1.globalFns
  have hN1 : 1 ≤ N := hN.pos
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨b₁, b₂⟩ := hbij F N hN1 w₀ hw₀
  choose E hE using fun s => (b₂ s).exists
  obtain ⟨f, hf, hfN⟩ := GlobalTheory.TorsionIso.torsion_clause R I hI D A G hG U F N hN1
  have hlabf : ∀ p, lab p = f p := fun p => (hf.1 p (lab p)).1 (hlab p)
  have hSF := GlobalTheory.SymFrameClause.symFrame_clause R I hI D A G hG U F N hN
  refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hE⟩
  · refine ⟨fun s s' h => ?_, fun t => ?_⟩
    · have h1 := hE s
      rw [h] at h1
      exact (b₁ (E s')).unique h1 (hE s')
    · obtain ⟨s, hs, -⟩ := b₁ t
      exact ⟨s, (b₂ s).unique (hE s) hs⟩
  · intro s s' s'' h j
    have hT := hlin F N w₀ (E s) (E s') (SecOps.secAdd (E s) (E s')) s s' 1 (hE s) (hE s') (fun j => by
      simp [SecOps.secAdd, liftFun])
    have e : (1 : F) • s + s' = s'' := fam_ext fun α j => by rw [h]; simp
    rw [e] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ s'').unique (hE s'') hT)
  · intro c s s' hs j
    obtain rfl := (isSmul_iff c s s').1 hs
    obtain ⟨z, hz, -⟩ := b₁ SecOps.secZero
    have hz0 : z = 0 := by
      have h2 := hlin F N w₀ _ _ SecOps.secZero z z 1 hz hz (fun j => by simp [SecOps.secZero])
      have h3 := (b₁ _).unique hz h2
      rw [one_smul] at h3
      exact left_eq_add.1 h3
    have hT := hlin F N w₀ (E s) SecOps.secZero
      (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F c)) (E s)) s z c (hE s) hz (fun j => by
        show _ = _ + 0
        rw [add_zero]
        rfl)
    rw [hz0, add_zero] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ _).unique (hE _) hT)
  · intro x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := hf.2.1 x hx
      exact ⟨p, (hlabf p).trans hp⟩
    · rintro ⟨p, rfl⟩
      rw [hlabf]
      exact hfN p
  · intro p
    exact (hSF p).1.1
  · intro p
    exact ((hSF p).2 (lab p) (hlab p)).1
  · intro p w θ s s' hw hθ hrel
    obtain ⟨t', ht'⟩ := GlobalTheory.RootShift.exists_isActOf A.isLB θ (E s)
    obtain ⟨s'', hs'', -⟩ := b₁ t'
    have h1 := ((hSF p).2 (lab p) (hlab p)).2 θ hθ w₀ hw₀ w hw (E s) t' s s'' (hE s) hs'' ht'
    obtain rfl := GlobalTheory.ThetaTranslate.phiRel_unique gf p hw.1 hrel h1
    have e := (b₂ s').unique (hE s') hs''
    rw [← e] at ht'
    exact ht'

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem bdParam_ne_zero (k : Type) [Field k] (m e : ℕ) (i : Fin m) : bdParam k m e i ≠ 0 := fun h => by
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin e) 1)) h
  simp [bdParam, MvPowerSeries.coeff_X] at this

theorem exists_fractionRing_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

theorem exists_lift_normBl {X Z S : Scheme.{0}} (i : X ⟶ Z) (π : S ⟶ Z) (j : X ⟶ S) (J : Z.IdealSheafData)
    (hN : GlobalTheory.Poinc.IsNormBl π J) (hji : j ≫ π = i) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ X) (hy : jK R ≫ a = y ≫ i) (f : R) (hf : f ≠ 0)
    (hJ : idlAlong J a = Ideal.span {f}) : ∃ ξ : Sp R ⟶ S, jK R ≫ ξ = y ≫ j := by
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, -⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  obtain ⟨c, ⟨hc1, -⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  exact ⟨c, hc1⟩

theorem taut_exists_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∃ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT
  obtain ⟨hm, hs, -⟩ := hT
  have hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).charZero
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  have hBase : GlobalTheory.Mum.Base (ChartRing k m e) := ⟨hAdm, hcF⟩
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  obtain ⟨⟨-, -, hi, -, -, -, -⟩, -, hext, ⟨-, -, hval⟩, ⟨hbl, -, -, -, hji, -, -, -⟩, -⟩ := hU
  obtain ⟨ξZ, hξZ, -⟩ := hext _ hBase C.t ⟨C.P⟩ C.y C.gen (spMap C.b) C.y_over.symm
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) C.P.D.toPre.X
  have hPF := hpf C.P.D.toPre.X C.rank
  have hnat : ∀ i, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • C.δ i) = n := fun i =>
    hPF.exists_nat (Submodule.smul_mem _ _ (C.cone.mem i)) (fun y => by
      simpa using mul_nonneg (by positivity : (0 : ℤ) ≤ l.M') (C.cone.nonneg i y))
  choose b hb using hnat
  let a : Fin m → ℕ := fun i => d * b (Fin.cast hm.symm i)
  have hprod : ∏ i, bdParam k m e i ^ a i = ∏ i : Fin C.m, C.s i ^ (d * b i) :=
    (Fintype.prod_equiv (finCongr hm) _ _ (fun j => by simp [a, hs j])).symm
  have hI : idlAlong J ξZ = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
    refine GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr k m e _ a fun W _ _ _ hW ψ hψi hψl => ?_
    haveI := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hne : ∀ i, ψ (C.s i) ≠ 0 := fun i h0 => by
      have : C.s i = 0 := hψi (h0.trans (map_zero ψ).symm)
      rw [hs i] at this
      exact bdParam_ne_zero k m e _ this
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible (hne i) hϖ
    obtain ⟨fK, hκ⟩ := exists_fractionRing_map ψ hψi
    obtain ⟨t, tK, P, h1, h2, be, hbe, hmono, hφ⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ hBase C W hW ψ hψi hψl ϖ hϖ w hw (spMap fK) hκ
    obtain ⟨n, hn, hIn⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξZ) (spMap fK ≫ C.y)
      (by rw [Category.assoc, ← hξZ, ← Category.assoc, hκ, Category.assoc]) t tK h1 h2 P be hbe hmono
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hIn, hprod, map_prod]
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    have hnw : n = ∑ i, w i * (d * b i) := by
      have : (n : ℝ) = ∑ i, (w i : ℝ) * (d * b i) := by
        rw [hn, hφ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hb i]; ring
      exact_mod_cast this
    have : Associated (∏ i, ψ (C.s i ^ (d * b i))) (∏ i : Fin C.m, (ϖ ^ w i) ^ (d * b i)) :=
      Associated.prod _ _ _ fun i _ => by rw [map_pow]; exact (hw i).pow_pow
    rw [hnw]
    refine (this.trans ?_).symm
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [← pow_mul]
    exact Associated.refl _
  have hf0 : ∏ i, bdParam k m e i ^ a i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (bdParam_ne_zero k m e _)
  obtain ⟨ξ, hξ⟩ := exists_lift_normBl i π j J hbl hji _ ξZ C.y hξZ _ hf0 hI
  exact ⟨ξ, hξ.symm⟩

end GlobalTheory.UChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem GlobalTheory.Mum.Desc.lab_onto_of_labExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (N : ℕ), 1 ≤ N → ∀ (lab : QkPt D (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (lab' : QkPt D F N → (TFK (R := R) F ⟶ A.A)), LabExt em lab lab' → (∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x) → ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab p = x := by
  intro R _ _ _ D A N hN lab F _ _ _ em lab' hext hon x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D F em N hN
  have cancel : ∀ y y' : TFK (R := R) (Kb R) ⟶ A.A, baseEm em ≫ y = baseEm em ≫ y' → y = y' := by
    intro y y' h
    apply Over.OverMorphism.ext
    have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    exact spec_map_field_cancel em.toRingHom y.left y'.left (congrArg CommaMorphism.left h)
  have hlab : ∀ p p', QkExt em.toRingHom p p' → lab' p' = baseEm em ≫ lab p := by
    intro p p' hp
    apply Over.OverMorphism.ext
    exact hext p p' hp
  constructor
  · intro hx
    have hx' : (baseEm em ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    obtain ⟨p', hp'⟩ := (hon _).1 hx'
    obtain ⟨p, hp, -⟩ := h2 p'
    refine ⟨p, cancel _ _ ?_⟩
    rw [← hlab p p' hp, hp']
  · rintro ⟨p, rfl⟩
    obtain ⟨p', hp', -⟩ := h1 p
    have h3 := (hon (lab' p')).2 ⟨p', rfl⟩
    rw [hlab p p' hp'] at h3
    apply cancel
    rw [MonObj.comp_pow, h3, MonObj.comp_one]
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernPart_complement_dense_open_null_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (B : LB X) (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε (ptsIn p σ U)ᶜ = 0 := by
  first | exact @GlobalTheory.ChernNullField.chernPart_compl_null | exact GlobalTheory.ChernNullField.chernPart_compl_null | (intros; apply GlobalTheory.ChernNullField.chernPart_compl_null <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.semiPositive_pullback_generically_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  first | exact @GlobalTheory.SemiPosUp.semiPos_pull_of_etale | exact GlobalTheory.SemiPosUp.semiPos_pull_of_etale | (intros; apply GlobalTheory.SemiPosUp.semiPos_pull_of_etale <;> assumption)
end
