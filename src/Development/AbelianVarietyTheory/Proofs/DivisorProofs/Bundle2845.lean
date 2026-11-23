module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle119
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle116
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.InvAlg.Levels

abbrev red {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k n : ℕ} (h : k ≤ n) :
    A ⧸ I ^ n →ₐ[R] A ⧸ I ^ k :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)

theorem red_red {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k l n : ℕ} (h₁ : k ≤ l)
    (h₂ : l ≤ n) (z : A ⧸ I ^ n) : red (R := R) I h₁ (red (R := R) I h₂ z) = red (R := R) I (h₁.trans h₂) z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem red_refl {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {n : ℕ}
    (z : A ⧸ I ^ n) : red (R := R) I (le_refl n) z = z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem red_evalₐ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k n : ℕ} (h : k ≤ n)
    (x : AdicCompletion I A) :
    red (R := R) I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x :=
  GlobalTheory.InvAlg.factorPow_evalₐ I h x

theorem compat_le {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1))
    (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z))
    {k n : ℕ} (h : k ≤ n) (z : A ⧸ I ^ (n + 1)) :
    red (R := R) J (Nat.succ_le_succ h) (β n z) = β k (red (R := R) I (Nat.succ_le_succ h) z) := by
  induction n, h using Nat.le_induction with
  | base => rw [red_refl, red_refl]
  | succ n hkn ih =>
    rw [← red_red (R := R) J (Nat.succ_le_succ hkn) (Nat.le_succ (n + 1)), hβ, ih, red_red]

theorem exists_equiv {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, (A ⧸ I ^ (n + 1)) ≃ₐ[R] (B ⧸ J ^ (n + 1)))
    (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)) :
    ∃ Ψ : AdicCompletion I A ≃ₐ[R] AdicCompletion J B,
      ∀ n y, AdicCompletion.evalₐ J (n + 1) (Ψ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by
  have hβ' : ∀ n z, red (R := R) I (Nat.le_succ (n + 1)) ((β (n + 1)).symm z) =
      (β n).symm (red (R := R) J (Nat.le_succ (n + 1)) z) := by
    intro n z
    apply (β n).injective
    rw [AlgEquiv.apply_symm_apply, ← hβ, AlgEquiv.apply_symm_apply]
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (I : Ideal A) (J : Ideal B)
      (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1))
      (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)),
      ∃ Φ : AdicCompletion I A →ₐ[R] AdicCompletion J B,
        ∀ n y, AdicCompletion.evalₐ J (n + 1) (Φ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by
    intro A B _ _ _ _ I J β hβ
    let f : ∀ n, AdicCompletion I A →ₐ[R] B ⧸ J ^ n := fun n =>
      (red (R := R) J (Nat.le_succ n)).comp ((β n).comp ((AdicCompletion.evalₐ I (n + 1)).restrictScalars R))
    have hf : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f k := by
      intro k n hle
      refine AlgHom.ext fun y => ?_
      change red (R := R) J hle (red (R := R) J (Nat.le_succ n) (β n (AdicCompletion.evalₐ I (n + 1) y))) =
        red (R := R) J (Nat.le_succ k) (β k (AdicCompletion.evalₐ I (k + 1) y))
      rw [red_red, ← red_red (R := R) J (Nat.le_succ k) (Nat.succ_le_succ hle), compat_le I J β hβ hle, red_evalₐ]
    refine ⟨AdicCompletion.liftAlgHom J f hf, fun n y => ?_⟩
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) (AdicCompletion.evalₐ I (n + 1 + 1) y)) = _
    rw [hβ, red_evalₐ]
  obtain ⟨Φ, hΦ⟩ := key I J (fun n => (β n).toAlgHom) hβ
  obtain ⟨Φ', hΦ'⟩ := key J I (fun n => (β n).symm.toAlgHom) hβ'
  have ev : ∀ {A : Type} [CommRing A] [Algebra R A] (I : Ideal A) (x y : AdicCompletion I A),
      (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y := by
    intro A _ _ I x y h
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [← red_evalₐ (R := R) I (Nat.le_succ n) x, ← red_evalₐ (R := R) I (Nat.le_succ n) y, h]
  refine ⟨AlgEquiv.ofAlgHom Φ Φ' ?_ ?_, hΦ⟩
  · refine AlgHom.ext fun y => ?_
    refine ev J _ _ fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hΦ, hΦ']
    exact AlgEquiv.apply_symm_apply _ _
  · refine AlgHom.ext fun y => ?_
    refine ev I _ _ fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hΦ', hΦ]
    exact AlgEquiv.symm_apply_apply _ _

end GlobalTheory.InvAlg.Levels

namespace GlobalTheory.InvAlg.Levels

theorem levels_equiv : ∀ (R : Type) [CommRing R] (m : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (act : GlobalTheory.Mum.Gal (algebraMap R R') →* (C' ≃ₐ[R] C')),
    (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) →
    ∀ (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C')),
    (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) →
    (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) →
    (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧
      RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) =
        (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) →
    ∀ (IT : Ideal (TensorProduct R O R')) (IC : Ideal C'), IT = m.map (algebraMap R (TensorProduct R O R')) →
      IC = m.map (algebraMap R C') →
    ∀ (hT : ∀ σ, IT.map (GlobalTheory.InvAlg.galTensor O σ).toRingHom ≤ IT)
      (hC : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC),
    ∃ Ψ : AdicCompletion IT (TensorProduct R O R') ≃ₐ[R] AdicCompletion IC C',
      (∀ σ y, Ψ (GlobalTheory.InvAlg.cmap (GlobalTheory.InvAlg.galTensor O σ).toRingHom
          IT IT (hT σ) y) = GlobalTheory.InvAlg.cmap (act σ).toRingEquiv.toRingHom IC IC (hC σ) (Ψ y)) ∧
      ∀ e (x : O) (y : C'), Ideal.Quotient.mk ((m ^ (e + 1)).map (algebraMap R C')) y = i e x →
        AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT _ (x ⊗ₜ[R] (1 : R')))) =
          Ideal.Quotient.mk (IC ^ (e + 1)) y := by
  intro R _ m R' _ _ C' _ _ _ _ act hact O _ _ i hi1 hi2 hi3 IT IC hIT hIC hT hC
  subst hIT hIC
  let L : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C') := fun e =>
    Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
      fun _ _ => Commute.all _ _
  have hCpow : ∀ e, (m ^ (e + 1)).map (algebraMap R C') = (m.map (algebraMap R C')) ^ (e + 1) :=
    fun e => Ideal.map_pow _ _ _
  have hTpow : ∀ e, (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) =
      (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1) :=
    fun e => Ideal.map_pow _ _ _
  let E : ∀ e, (C' ⧸ (m ^ (e + 1)).map (algebraMap R C')) ≃ₐ[R] (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)) :=
    fun e => Ideal.quotientEquivAlgOfEq R (hCpow e)
  let L' : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m.map (algebraMap R C')) ^ (e + 1) := fun e =>
    (E e).toAlgHom.comp (L e)
  have hsurj : ∀ e, Function.Surjective (L' e) := fun e => (E e).surjective.comp (hi3 e).1
  have hker : ∀ e, RingHom.ker (L' e) = (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1) := by
    intro e
    ext t
    rw [RingHom.mem_ker, ← hTpow, ← (hi3 e).2, RingHom.mem_ker]
    exact map_eq_zero_iff (E e) (E e).injective
  let β : ∀ e, (TensorProduct R O R' ⧸ (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1)) ≃ₐ[R]
      (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)) := fun e =>
    (Ideal.quotientEquivAlgOfEq R (hker e).symm).trans (Ideal.quotientKerAlgEquivOfSurjective (hsurj e))
  have hβmk : ∀ e t, β e (Ideal.Quotient.mk _ t) = L' e t := fun e t => rfl
  have hL : ∀ e x r y, Ideal.Quotient.mk _ y = i e x →
      L' e (x ⊗ₜ[R] r) = Ideal.Quotient.mk _ (y * algebraMap R' C' r) := by
    intro e x r y hy
    change E e (L e (x ⊗ₜ[R] r)) = _
    rw [Algebra.TensorProduct.lift_tmul, ← hy]
    change E e (Ideal.Quotient.mk _ y * Ideal.Quotient.mk _ (algebraMap R' C' r)) = _
    rw [← map_mul]
    exact Ideal.quotientEquivAlgOfEq_mk _ _ _
  have hred : ∀ n z, red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (β (n + 1) z) =
      β n (red (R := R) (m.map (algebraMap R (TensorProduct R O R'))) (Nat.le_succ (n + 1)) z) := by
    intro n z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    change red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (L' (n + 1) t) = L' n t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i (n + 1) x)
      rw [hL (n + 1) x r y hy, hL n x r y (hi1 n x y hy)]
      rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  obtain ⟨Ψ, hΨ⟩ := exists_equiv _ _ β hred
  have ev : ∀ {A : Type} [CommRing A] (I : Ideal A) (x y : AdicCompletion I A),
      (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y := by
    intro A _ I x y h
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) x, ← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) y, h]
  refine ⟨Ψ, fun σ y => ev _ _ _ fun n => ?_, fun e x y hy => ?_⟩
  · rw [hΨ, GlobalTheory.InvAlg.evalₐ_cmap, GlobalTheory.InvAlg.evalₐ_cmap, hΨ]
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ (n + 1) y)
    rw [← ht, Ideal.quotientMap_mk, hβmk, hβmk]
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i n x)
      have h1 : (GlobalTheory.InvAlg.galTensor O σ).toRingHom (x ⊗ₜ[R] r) = x ⊗ₜ[R] σ.1 r := rfl
      rw [h1, hL n x _ y hy, hL n x r y hy, Ideal.quotientMap_mk]
      change _ = Ideal.Quotient.mk _ (act σ (y * algebraMap R' C' r))
      rw [map_mul (act σ), hact, map_mul (Ideal.Quotient.mk _), map_mul (Ideal.Quotient.mk _)]
      congr 1
      have h2 := hi2 n σ x y hy
      rw [← hy, Ideal.Quotient.eq, hCpow] at h2
      rw [Ideal.Quotient.eq, ← neg_sub]
      exact neg_mem h2
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  · rw [hΨ, AdicCompletion.evalₐ_of, hβmk, hL e x 1 y hy, map_one, _root_.mul_one]

end GlobalTheory.InvAlg.Levels
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

theorem act_proj₂ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} {A' B' : Over S'}
    (e : A' ⟶ (Over.pullback f).obj A) (e₂ : B' ⟶ (Over.pullback f).obj B) {u : A ⟶ B} {u' : A' ⟶ B'}
    (h : u' ≫ e₂ = e ≫ (Over.pullback f).map u) :
    u'.left ≫ e₂.left ≫ pullback.fst B.hom f = (e.left ≫ pullback.fst A.hom f) ≫ u.left := by
  have h1 : u'.left ≫ e₂.left = e.left ≫ ((Over.pullback f).map u).left := congrArg (·.left) h
  rw [← Category.assoc, h1, Category.assoc, map_left_fst, Category.assoc]

theorem torusHomOf_iff' {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') :
    TorusHomOf h t ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X'),
      gm (r ≫ t.left) z ⊤ (charUnit S X' χ) = gm r z ⊤ (charUnit S X (h χ)) := by
  constructor
  · intro H Z r z χ
    rw [← H χ]
    exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm
  · intro H χ
    refine unit_ext fun z _ => ?_
    rw [← H]
    exact (gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)



theorem linPull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (D₁' D₂' : DegData R' I') (A₁' A₂' : PolAV (Sp (FractionRing R'))) (hD₁ : IsPullDeg φ D₁.toPre D₁'.toPre) (hD₂ : IsPullDeg φ D₂.toPre D₂'.toPre) (U₁' : Unif I' D₁' A₁' ((Over.pullback (specOf φ)).obj G₁)) (U₂' : Unif I' D₂' A₂' ((Over.pullback (specOf φ)).obj G₂)), IsPullUnif φ hD₁ (Iso.refl _) U₁ U₁' → IsPullUnif φ hD₂ (Iso.refl _) U₂ U₂' → ∀ (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁.toUnifPre U₂.toUnifPre a b h → ∃ (b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A) (h' : D₂'.toPre.X →+ D₁'.toPre.X), Lin U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) b' h' ∧ b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ∧ ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) := by
  intro R R' _ _ _ _ I I' φ D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ D₁' D₂' A₁' A₂' hD₁ hD₂ U₁' U₂' hU₁ hU₂ a b h hL
  obtain ⟨homA, homB, hq0, hi0⟩ := hL
  obtain ⟨_wL₁, -, _he₁, -, H₁⟩ := (isPullUnif_iff_stalks R R' I I' φ D₁ D₁' hD₁ A₁ A₁' G₁ _ (Iso.refl _) U₁ U₁').1 hU₁
  obtain ⟨_wL₂, -, _he₂, -, H₂⟩ := (isPullUnif_iff_stalks R R' I I' φ D₂ D₂' hD₂ A₂ A₂' G₂ _ (Iso.refl _) U₂ U₂').1 hU₂
  choose h₁ hf₁ hpt₁ _hw₁ using H₁
  choose h₂ hf₂ hpt₂ _hw₂ using H₂
  have := hD₁.e_hom
  have := hD₂.e_hom
  obtain ⟨b', homB', hB⟩ : ∃ b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A, IsMonHom b' ∧
      b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b :=
    ⟨hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ≫ hD₂.e.inv, inferInstance, by simp⟩
  obtain ⟨h', hx⟩ : ∃ h' : D₂'.toPre.X →+ D₁'.toPre.X, ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) :=
    ⟨hD₁.xe.symm.toAddMonoidHom.comp (h.comp hD₂.xe.toAddMonoidHom), fun χ => hD₁.xe.apply_symm_apply _⟩
  have hG : (Over.pullback (specOf φ)).map a ≫ (Iso.refl ((Over.pullback (specOf φ)).obj G₂)).hom =
      (Iso.refl ((Over.pullback (specOf φ)).obj G₁)).hom ≫ (Over.pullback (specOf φ)).map a := by simp
  have hact : ∀ e : ℕ, ((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left ≫ h₂ e =
      h₁ e ≫ ((Over.pullback (thick R I e)).map a).left := by
    intro e
    have hf' : h₂ e ≫ pullback.fst G₂.hom (thick R I e) =
        pullback.fst ((Over.pullback (specOf φ)).obj G₂).hom (thick R' I' e) ≫
          (Iso.refl ((Over.pullback (specOf φ)).obj G₂)).hom.left ≫ pullback.fst G₂.hom (specOf φ) := hf₂ e
    have hf₁' : h₁ e ≫ pullback.fst G₁.hom (thick R I e) =
        pullback.fst ((Over.pullback (specOf φ)).obj G₁).hom (thick R' I' e) ≫
          (Iso.refl ((Over.pullback (specOf φ)).obj G₁)).hom.left ≫ pullback.fst G₁.hom (specOf φ) := hf₁ e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G₂.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G₂.hom (thick R I e)), Category.assoc, hf', Category.assoc, map_left_fst,
      ← Category.assoc (h₁ e), hf₁',
      ← Category.assoc (((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left), map_left_fst,
      Category.assoc, act_proj₂ _ (Iso.refl _).hom (Iso.refl _).hom hG]
    simp only [Category.assoc]
  have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S} {e : ℕ}
      {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
      {B : Over (Spec (CommRingCat.of S))} (u : E.P.A ⟶ B), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
        pullback.fst B.hom (thick S J e) = g.pG.left ≫ u.left := by
    intro S _ _ J E e K _ _ g B u
    rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
  have hB' := act_proj₂ (specOf φ) hD₁.e.hom hD₂.e.hom hB
  have k₂ : ∀ e, (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)) ≫
      (U₂'.gt e).pG = (U₁'.gt e).pG ≫ b' := by
    intro e
    have k₁ : ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).pG.left =
        (U₁.gt e).pG.left ≫ b.left := by
      rw [← k, ← hq0 e]
      exact (Category.assoc _ _ _).symm
    refine ext_of_iso_pullback _ hD₂.e ?_
    change (((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left ≫ (U₂'.gt e).pG.left) ≫ _ =
      ((U₁'.gt e).pG.left ≫ b'.left) ≫ _
    rw [Category.assoc, Category.assoc, hB', (hpt₂ e).1,
      ← Category.assoc (U₁'.gt e).pG.left, (hpt₁ e).1, ← Category.assoc, hact, Category.assoc,
      Category.assoc, k₁]
  have hq : ∀ e : ℕ, (Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a) ≫ (U₂'.gt e).q =
      (U₁'.gt e).q ≫ (Over.pullback (thick R' I' e)).map b' := by
    intro e
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) (k₂ e)
  refine ⟨b', h', ⟨inferInstance, homB', hq, fun e => ?_⟩, hB, hx⟩
  obtain ⟨t, ht, hi⟩ := hi0 e
  have hk : ((U₁'.gt e).i ≫ (Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)) ≫ (U₂'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D₂'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U₁'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U₂'.gt e).isKernel.lift_fst _ _ hk
  generalize (U₂'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U₁.gt e) (U₁'.gt e) (hpt₁ e).1 ((hpt₁ e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U₂.gt e).i).left = (t' ≫ (U₂'.gt e).i).left ≫ h₂ e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U₂.gt e) (U₂'.gt e) hD₂.w ((hpt₂ e).2 χ).1 ((hpt₂ e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U₁.gt e) (U₁'.gt e) hD₁.w ((hpt₁ e).2 (h' χ)).1 ((hpt₁ e).2 (h' χ)).2 (𝟙 _) τ hτ z
  have e₃ := (torusHomOf_iff' _ t).1 ht _ τ.left z (hD₂.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.Mum.Two.PullLin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two


open GlobalTheory.EndData GlobalTheory.AbLaw in
theorem exists_hom_of_levels {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R}
    (hC : IsAdicComplete I R) (Y Z : Over (Spec (CommRingCat.of R))) (sY : Smooth Y.hom) (sZ : Smooth Z.hom)
    (pY : IsProjBy Y.hom) (pZ : IsProjBy Z.hom) (s : Y ⟶ Z) (f : ∀ e, (thickObj R I e Y).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom)
    (hc : ∀ e, thickMap R I e Y ≫ f (e + 1) = f e) :
    ∃ g : Y ⟶ Z, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  have w₁ : (fst Y Z).left ≫ Y.hom = (Y ⊗ Z).hom := Over.w _
  have w₂ : (snd Y Z).left ≫ Z.hom = (Y ⊗ Z).hom := Over.w _
  have sm : Smooth (Y ⊗ Z).hom := by
    show Smooth (pullback.fst Y.hom Z.hom ≫ Y.hom)
    infer_instance
  let p : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ (thickObj R I e Y).left := fun e =>
    ((Over.pullback (thick R I e)).map (fst Y Z)).left
  have hp : ∀ e, p e ≫ pullback.fst Y.hom (thick R I e) = pullback.fst (Y ⊗ Z).hom (thick R I e) ≫ (fst Y Z).left :=
    fun e => map_fst e _
  let F : ∀ e, (thickObj R I e (Y ⊗ Z)).left ⟶ pullback Y.hom Z.hom := fun e =>
    pullback.lift (p e ≫ pullback.fst Y.hom (thick R I e)) (p e ≫ f e) (by
      rw [Category.assoc, Category.assoc, hf])
  have F₁ : ∀ e, F e ≫ pullback.fst _ _ = p e ≫ pullback.fst Y.hom (thick R I e) := fun e => pullback.lift_fst _ _ _
  have F₂ : ∀ e, F e ≫ pullback.snd _ _ = p e ≫ f e := fun e => pullback.lift_snd _ _ _
  have tp : ∀ e, thickMap R I e (Y ⊗ Z) ≫ p (e + 1) = p e ≫ thickMap R I e Y := fun e => trans_map e _
  obtain ⟨g, hg⟩ := EndAlg.exists_end_of_thickenings R I hC (Y ⊗ Z) sm (isProjBy_tensor R Y Z pY pZ) F
    (fun e => by
      show F e ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = _
      rw [← Category.assoc, F₁, hp, Category.assoc, w₁])
    (fun e => by
      show (thickMap R I e (Y ⊗ Z) ≫ F (e + 1) : _ ⟶ pullback Y.hom Z.hom) = F e
      apply pullback.hom_ext
      · rw [Category.assoc, F₁, F₁, ← Category.assoc, tp, Category.assoc, trans_fst]
      · rw [Category.assoc, F₂, F₂, ← Category.assoc, tp, Category.assoc, hc])
  refine ⟨lift (𝟙 Y) s ≫ g ≫ snd Y Z, fun e => ?_⟩
  have hj : ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s)).left ≫ p e = 𝟙 _ := by
    show ((Over.pullback (thick R I e)).map (lift (𝟙 Y) s) ≫ (Over.pullback (thick R I e)).map (fst Y Z)).left = _
    rw [← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id]
    rfl
  have k : F e ≫ (snd Y Z).left = p e ≫ f e := F₂ e
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← map_fst, Category.assoc,
    ← Category.assoc (pullback.fst _ _), hg]
  erw [k]
  rw [← Category.assoc]
  erw [hj]
  exact Category.id_comp _


open GlobalTheory.EndTorus in
theorem exists_abelian_level {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    {D₁ D₂ : DegPre R} {e : ℕ} {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [IsCommMonObj G₁]
    [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂)
    (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a] :
    ∃ b : thickObj R I e D₁.P.A ⟶ thickObj R I e D₂.P.A, IsMonHom b ∧ g₁.q ≫ b = a ≫ g₂.q := by
  obtain ⟨hN, -, -, hC⟩ := hR
  have := g₁.q_hom
  have := g₂.q_hom
  have := g₁.i_hom
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have : IsProper D₂.P.A.hom := D₂.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D₂.P.A) :=
    { comm := inferInstance
      smooth := by have := D₂.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D₂.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g₁.i ≫ a ≫ g₂.q = toUnit _ ≫ η[thickObj R I e D₂.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D₁.X _ hB (g₁.i ≫ a ≫ g₂.q) inferInstance).trans (Hom.one_def)
  exact FlatQuotient.exists_desc g₁.q g₁.i (a ≫ g₂.q) g₁.isKernel h1


open GlobalTheory.EndData in
theorem exists_abelian_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), IsMonHom a → ∃ b : D₁.toPre.P.A ⟶ D₂.toPre.P.A, IsMonHom b ∧ Over₀ U₁ U₂ a b := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a ha
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => exists_abelian_level hR (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a)
  have hql : ∀ e, (U₁.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).q.left :=
    fun e => congrArg (·.left) (hq e)
  obtain ⟨aB, haB⟩ := exists_hom_of_levels hC D₁.toPre.P.A D₂.toPre.P.A D₁.toPre.P.isAb.smooth
    D₂.toPre.P.isAb.smooth (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _))
    (AbProj.isProjBy_of_isPullback D₂.toPre.P (IsPullback.id_horiz _)) 1
    (fun e => (b e).left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D₂.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w, pullback.condition])
    (fun e => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      have : Epi (U₁.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U₁.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U₁.gt (e + 1)).q.left, hql, ← Category.assoc (U₁.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G₂), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D₂.toPre.P.isAb
    D₁.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact (hq e).symm

end GlobalTheory.Mum.Two
end
