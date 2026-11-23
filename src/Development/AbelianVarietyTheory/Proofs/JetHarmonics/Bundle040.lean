module

public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

open Formalism.REAL Finset

namespace GlobalTheory


open Finset in
theorem _root_.GlobalTheory.covector_multiplier_shift : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), _root_.Formalism.REAL.GlRel E → _root_.Formalism.REAL.GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), _root_.Formalism.REAL.qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b - if a = j then x b else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), _root_.Formalism.REAL.qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t - if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  obtain ⟨hF, hqF⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  obtain ⟨hF', hqF'⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ W) n E' hE'
  have hιF : ∀ (a b : Fin n) (w : W), ι ((-E' b a) w) = (-E b a) (ι w) := by
    intro a b w
    simp only [LinearMap.neg_apply, map_neg, hι]
  have hνF : Function.Injective (fun s : Fin n => (1 : ℂ) - n - ν s) := by
    intro s t h
    apply hν
    have h' : (1 - n - ν s : ℂ) = 1 - n - ν t := h
    linear_combination -h'
  have hqE' : ∀ (u : ℂ) (w : W), (_root_.Formalism.REAL.qdet (fun a b => -E' b a) u) w
      = (∏ s, (u + (1 - n - ν s))) • w := by
    intro u w
    rw [hqF', LinearMap.smul_apply, hq, smul_smul]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hxF : ∀ (a b k : Fin n), (-E b a) * x k = x k * (-E b a) + if b = k then x a else 0 := by
    intro a b k
    rw [neg_mul, mul_neg, hx b a k]
    abel
  obtain ⟨v, hv1, hv2⟩ := _root_.GlobalTheory.qdet_vector_multiplier_shift_plus V W n (fun a b => -E b a)
    (fun a b => -E' b a) ι x (fun s => 1 - n - ν s) hF hF' hιF hνF hqE' hxF j w
  · refine ⟨v, hv1, fun s u => ?_⟩
    have h := hv2 s ((n : ℂ) - 1 - u)
    rw [hqF, show (n : ℂ) - 1 - ((n : ℂ) - 1 - u) = u by ring, LinearMap.smul_apply] at h
    have h2 := congrArg (((-1 : ℂ) ^ n) • ·) h
    simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul] at h2
    rw [h2]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    split_ifs <;> ring

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lift_translT_general {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (f : S' ⟶ S)
    (P : Over S') (x : P ⟶ (Over.pullback f).obj G) (T : Over S) (e : T.left ⟶ P.left) (r g : T ⟶ G)
    (hg : g.left = e ≫ x.left ≫ pullback.fst G.hom f) :
    ∃ ρ : T.left ⟶ (P ⊗ (Over.pullback f).obj G).left,
      ρ ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      ρ ≫ (snd P ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f = r.left ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (snd P ((Over.pullback f).obj G)).left ≫
        pullback.fst G.hom f = (r * g).left := by
  have hx : x.left ≫ pullback.snd G.hom f = P.hom := Over.w x
  have hT : T.hom = (e ≫ P.hom) ≫ f := by
    rw [← Over.w g, hg, ← hx]
    simp only [Category.assoc, pullback.condition]
  let T' : Over S' := Over.mk (e ≫ P.hom)
  let e' : T' ⟶ P := Over.homMk e rfl
  let r' : T' ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift r.left (e ≫ P.hom) ((Over.w r).trans hT)) (pullback.lift_snd _ _ _)
  have hr' : r'.left ≫ pullback.fst G.hom f = r.left := pullback.lift_fst _ _ _
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) ((Category.id_comp _).trans hT)
  have hU : ∀ z : T ⟶ G, (U ≫ z).left = z.left := fun z => Category.id_comp _
  have h1 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ fst _ _ = e' := by
    simp [translT]
  have h2 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ snd _ _ = (e' ≫ x) * r' := by
    simp only [translT, translPt, lift_snd, Hom.mul_def]
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have h3 := (isGrpPullback_pullback G f).2 T' (e' ≫ x) r' (U ≫ g) (U ≫ r)
    ((hU g).trans (hg.trans (Category.assoc _ _ _).symm)) ((hU r).trans hr'.symm)
  refine ⟨(lift e' r').left, congrArg (fun z => z.left) (lift_fst e' r'), ?_, ?_, ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z : T' ⟶ (Over.pullback f).obj G => z.left ≫ pullback.fst G.hom f) (lift_snd e' r'))).trans hr'
  · exact (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h1)
  · have h4 : ((lift e' r').left ≫ (translT ((Over.pullback f).obj G) x).left) ≫
        (snd P ((Over.pullback f).obj G)).left = ((e' ≫ x) * r').left :=
      (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h2)
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst G.hom f) h4)).trans (h3.symm.trans ?_)
    rw [← MonObj.comp_mul, hU, mul_comm]

theorem exists_lift_translT : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  intro R _ _ G _ _ F _ _ x T e r g hg
  exact exists_lift_translT_general G (jK R) (TFK (R := R) F) x T e r g hg

end GlobalTheory
end
