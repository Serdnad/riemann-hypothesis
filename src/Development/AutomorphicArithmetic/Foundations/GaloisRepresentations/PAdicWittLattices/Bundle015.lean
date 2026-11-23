module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3.BaseChangeTowers

private noncomputable def cmp {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    pullback p ab ⟶ pullback p a :=
  pullback.lift (pullback.fst p ab) (pullback.snd p ab ≫ b)
    (by rw [pullback.condition, Category.assoc, h])

private theorem cmp_fst {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.fst p a = pullback.fst p ab := pullback.lift_fst _ _ _

private theorem cmp_snd {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.snd p a = pullback.snd p ab ≫ b := pullback.lift_snd _ _ _

private theorem cmp_isPullback {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp p a ab b h) (pullback.snd p ab) (pullback.snd p a) b := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p a) (h₂₂ := a) (v₁₃ := p) ?_ (cmp_snd p a ab b h)
    (IsPullback.of_hasPullback p a)
  rw [cmp_fst, h]
  exact IsPullback.of_hasPullback p ab

private theorem cmp_bcMap {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp q a ab b h ≫ bcMap a f hf = bcMap ab f hf ≫ cmp p a ab b h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, cmp_fst, bcMap_fst, ← Category.assoc, cmp_fst]
  · rw [Category.assoc, Category.assoc, bcMap_snd, cmp_snd, cmp_snd, ← Category.assoc, bcMap_snd]

private theorem cmp_bcMap_isPullback {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp q a ab b h) (bcMap ab f hf) (bcMap a f hf) (cmp p a ab b h) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p ab) (v₂₂ := pullback.snd p a) (h₃₁ := b) ?_
    (cmp_bcMap p q f hf a ab b h) (cmp_isPullback p a ab b h)
  rw [bcMap_snd, bcMap_snd]
  exact cmp_isPullback q a ab b h

end UpperTheory.Gal.G3.BaseChangeTowers

open UpperTheory.Gal.G3.BaseChangeTowers in
theorem UpperTheory.Gal.G3.jBCTower :
    UpperTheory.Gal.Seam.NiceBc → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BCTower := by
  intro hN k K F _ _ _ τ φ H hH
  refine ⟨hN k K τ H hH, ⟨?_⟩⟩
  have hab : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom (φ.comp τ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let a := Spec.map (CommRingCat.ofHom τ)
  let ab := Spec.map (CommRingCat.ofHom (φ.comp τ))
  let b := Spec.map (CommRingCat.ofHom φ)
  have hz : IsPullback (cmp H.q a ab b hab) (UpperTheory.Gal.Int.Geo.bcAlong H (φ.comp τ)).q
      (UpperTheory.Gal.Int.Geo.bcAlong H τ).q b := cmp_isPullback H.q a ab b hab
  refine
    { z := cmp H.q a ab b hab
      hz := hz
      y := fun j => cmp (H.s j ≫ H.q) a ab b hab
      hs := fun j => ?_
      ht := fun j => ?_ }
  · exact cmp_bcMap_isPullback H.q (H.s j ≫ H.q) (H.s j) rfl a ab b hab
  · exact cmp_bcMap H.q (H.s j ≫ H.q) (H.t j) (H.comm j) a ab b hab
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8

universe u

namespace UpperTheory.Gal.G3

def TrBc : Prop := ∀ {B B' : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (g : B ⟶ B') {Z Y : Scheme.{0}} (p : Z ⟶ B')
  (q : Y ⟶ B') (s : Y ⟶ Z) [IsFinite s] [Etale s] (hs : s ≫ p = q) (tr : T.H (pullback.snd q g) →ₗ[R] T.H (pullback.snd p g)),
  T.IsTr (pullback.snd p g) (pullback.snd q g) (bcMap g s hs) tr → (T.bc g).IsTr p q s tr

def HodgeOpBc : Prop := ∀ (k F : Type) [Field k] [Field F] (φ : k →+* F) (H : HTower k) (g : H.Γ) [IsFinite (H.s g)] [Etale (H.s g)]
  (a b : ℕ), IsFinite ((bcAlong H φ).s g) ∧ Etale ((bcAlong H φ).s g) ∧
  ∃ tr, ((hodge F a b).bc (Spec.map (CommRingCat.ofHom φ))).IsTr H.q (H.s g ≫ H.q) (H.s g) tr ∧
    ∀ (_ : IsFinite ((bcAlong H φ).s g)) (_ : Etale ((bcAlong H φ).s g)) (x : hodgeH (bcAlong H φ).q a b),
      hodgeTrace (s := (bcAlong H φ).q) (s' := (bcAlong H φ).s g ≫ (bcAlong H φ).q) (f := (bcAlong H φ).s g) rfl a b
        (hodgePull (s := (bcAlong H φ).q) (s' := (bcAlong H φ).s g ≫ (bcAlong H φ).q) ((bcAlong H φ).comm g) a b x) =
      tr (((hodge F a b).bc (Spec.map (CommRingCat.ofHom φ))).pull (H.t g) (H.comm g) x)

def HopLies : Prop := ∀ (l : ℕ) [Fact l.Prime] {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k], (l : k) ≠ 0 →
  ∀ {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) (D : LowData C), Nice H → ∀ (Ω : Type) [Field Ω] [Algebra k Ω] (g : H.Γ),
  hop l H Ω g ∘ₗ (etG l k Ω).pull (piK C) (piK_snd C) =
    (D.m g : ℚ_[l]) • ((etG l k Ω).pull (piK C) (piK_snd C) ∘ₗ hop l (low D) Ω g)

def GenIso : Prop := ∀ {O O' k K : Type} [CommRing O] [CommRing O'] [Field k] [Field K] [Algebra O k] [Algebra O' K]
  (φ : O →+* O') (τ : k →+* K), (∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x)) → ∀ {X : Scheme.{0}} (p : X ⟶ sp O),
  ∃ e : pullback (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) (gen O' K) ≅
      pullback (pullback.snd p (gen O k)) (Spec.map (CommRingCat.ofHom τ)),
    e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
    e.hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _

def ModBc : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) {O : Type} [CommRing O] [IsNoetherianRing O]
  (φ : O →+* ↥(CrystallineSemistableComparison.OK l K.1)) {Y W : Scheme.{0}} (p : Y ⟶ sp O) (d : ℕ), SmoothOfRelativeDimension d p → IsProjOver p →
  ∀ (c : W ⟶ Y) [IsFinite c] [Etale c],
    (⟨_, pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ)))

def LowCov : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (H : HTower E) (θ : H.Γ → Qbar l) (w : HeightOneSpectrum (𝓞 E))
    (C : Cover H θ (Ow w)) (D : LowData C) (K : FinExt l) (τK : E →+* ↥K.1),
    (∀ x : Ow w, ‖(τK (x : E) : Qbar l)‖ ≤ 1) → HasGoodCovers (bcAlong (low D) τK) id

theorem matEx_of (h : RepEx) : MatEx := fun E Ω _ _ _ _ _ l _ H θ hN => by
  obtain ⟨d, ρ, -, -, ρ₀, h₀, -⟩ := h E Ω l H θ hN
  exact ⟨d, ρ₀, h₀⟩

theorem coverLow_of_cov (hC : CoverOf) (hL : LowCov) : CoverLow := fun hG E _ _ l _ H θ w C D K τK hτ n =>
  hC hG l K (bcAlong (low D) τK) id (hL E l H θ w C D K τK hτ) n

end UpperTheory.Gal.G3

end
end
