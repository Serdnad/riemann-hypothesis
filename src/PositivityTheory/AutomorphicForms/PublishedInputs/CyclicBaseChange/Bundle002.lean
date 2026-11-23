module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.CBC.GaloisActionOnAdeles

variable {M : Type} [Field M]

theorem isometry_withAbs (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) :
    Isometry (WithAbs.congr v.1 w.1 τ) := by
  refine AddMonoidHomClass.isometry_of_norm (WithAbs.congr v.1 w.1 τ) fun x => ?_
  exact h _

def locMap (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) : v.Completion →+* w.Completion :=
  (AbsoluteValue.Completion.ofCompletion (v := w.1)).comp
    ((UniformSpace.Completion.mapRingHom (WithAbs.congr v.1 w.1 τ).toRingHom
      (isometry_withAbs τ v w h).continuous).comp AbsoluteValue.Completion.toCompletion)

theorem continuous_locMap (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) :
    Continuous (locMap τ v w h) :=
  (AbsoluteValue.Completion.continuous_ofCompletion w.1).comp
    (UniformSpace.Completion.continuous_map.comp (AbsoluteValue.Completion.continuous_toCompletion v.1))

theorem locMap_coe (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) (x : M) :
    locMap τ v w h (x : v.Completion) = ((τ x : M) : w.Completion) := by
  rw [locMap, RingHom.comp_apply, RingHom.comp_apply, AbsoluteValue.Completion.toCompletion_coe]
  calc
    _ = AbsoluteValue.Completion.ofCompletion (v := w.1) (WithAbs.toAbs w.1 (τ x)) :=
      congrArg (AbsoluteValue.Completion.ofCompletion (v := w.1))
        (UniformSpace.Completion.mapRingHom_coe (isometry_withAbs τ v w h).continuous (WithAbs.toAbs v.1 x))
    _ = _ := AbsoluteValue.Completion.ofCompletion_coe (WithAbs.toAbs w.1 (τ x))

theorem locMap_comp (τ τ' : M ≃+* M) (u v w : InfinitePlace M) (h : ∀ x, v (τ x) = u x) (h' : ∀ x, w (τ' x) = v x)
    (h'' : ∀ x, w ((τ.trans τ') x) = u x) (y : u.Completion) :
    locMap τ' v w h' (locMap τ u v h y) = locMap (τ.trans τ') u w h'' y := by
  induction y using AbsoluteValue.Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_locMap _ _ _ _).comp (continuous_locMap _ _ _ _)) (continuous_locMap _ _ _ _)
  | ih a =>
    have e1 := locMap_coe τ u v h (WithAbs.equiv u.1 a)
    have e2 := locMap_coe τ' v w h' (τ (WithAbs.equiv u.1 a))
    have e3 := locMap_coe (τ.trans τ') u w h'' (WithAbs.equiv u.1 a)
    change locMap τ' v w h' (locMap τ u v h (WithAbs.equiv u.1 a : u.Completion)) = _
    rw [e1, e2]
    change _ = locMap (τ.trans τ') u w h'' (WithAbs.equiv u.1 a : u.Completion)
    rw [e3]
    rfl

theorem locMap_eq_self (τ : M ≃+* M) (hτ : ∀ x, τ x = x) (u : InfinitePlace M) (h : ∀ x, u (τ x) = u x)
    (y : u.Completion) : locMap τ u u h y = y := by
  induction y using AbsoluteValue.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_locMap _ _ _ _) continuous_id
  | ih a =>
    change locMap _ u u h (WithAbs.equiv u.1 a : u.Completion) = _
    rw [locMap_coe, hτ]
    rfl

def placePerm (σ : M ≃+* M) : InfinitePlace M ≃ InfinitePlace M where
  toFun w := w.comap σ.symm.toRingHom
  invFun w := w.comap σ.toRingHom
  left_inv w := InfinitePlace.ext _ _ fun x => by
    change ((w.comap σ.symm.toRingHom).comap σ.toRingHom) x = w x
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply]
    simp
  right_inv w := InfinitePlace.ext _ _ fun x => by
    change ((w.comap σ.toRingHom).comap σ.symm.toRingHom) x = w x
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply]
    simp

theorem placePerm_apply (σ : M ≃+* M) (w : InfinitePlace M) (x : M) : placePerm σ w (σ x) = w x := by
  rw [show placePerm σ w = w.comap σ.symm.toRingHom from rfl, InfinitePlace.comap_apply]
  simp

theorem placePerm_symm_apply (σ : M ≃+* M) (w : InfinitePlace M) (x : M) : w (σ.symm x) = placePerm σ w x := by
  rw [← placePerm_apply σ w (σ.symm x), RingEquiv.apply_symm_apply]

def locEquiv (σ : M ≃+* M) (w : InfinitePlace M) : w.Completion ≃+* (placePerm σ w).Completion where
  __ := locMap σ w (placePerm σ w) (placePerm_apply σ w)
  invFun := locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w)
  left_inv y := by
    change locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w)
      (locMap σ w (placePerm σ w) (placePerm_apply σ w) y) = y
    rw [locMap_comp σ σ.symm w (placePerm σ w) w _ _ (fun x => by simp)]
    exact locMap_eq_self _ (fun x => by simp) _ _ y
  right_inv y := by
    change locMap σ w (placePerm σ w) (placePerm_apply σ w)
      (locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w) y) = y
    rw [locMap_comp σ.symm σ (placePerm σ w) w (placePerm σ w) _ _ (fun x => by simp)]
    exact locMap_eq_self _ (fun x => by simp) _ _ y

theorem continuous_locEquiv (σ : M ≃+* M) (w : InfinitePlace M) : Continuous (locEquiv σ w) :=
  continuous_locMap σ w (placePerm σ w) (placePerm_apply σ w)

def infEquiv (σ : M ≃+* M) : InfiniteAdeleRing M ≃+* InfiniteAdeleRing M :=
  (RingEquiv.piCongrRight fun w => locEquiv σ w).trans
    (RingEquiv.piCongrLeft (fun v : InfinitePlace M => v.Completion) (placePerm σ))

theorem continuous_infEquiv (σ : M ≃+* M) : Continuous (infEquiv σ) :=
  (Homeomorph.piCongrLeft (Y := fun v : InfinitePlace M => v.Completion) (placePerm σ)).continuous.comp
    (continuous_pi fun w => (continuous_locEquiv σ w).comp (continuous_apply w))

theorem infEquiv_algebraMap (σ : M ≃+* M) (x : M) :
    infEquiv σ (algebraMap M (InfiniteAdeleRing M) x) = algebraMap M (InfiniteAdeleRing M) (σ x) := by
  funext v
  obtain ⟨w, rfl⟩ := (placePerm σ).surjective v
  change (Equiv.piCongrLeft (fun v : InfinitePlace M => v.Completion) (placePerm σ)
    (fun w => locEquiv σ w (algebraMap M (InfiniteAdeleRing M) x w))) (placePerm σ w) = _
  rw [Equiv.piCongrLeft_apply_apply, InfiniteAdeleRing.algebraMap_apply,
    InfiniteAdeleRing.algebraMap_apply]
  exact locMap_coe σ w (placePerm σ w) (placePerm_apply σ w) x

variable [NumberField M]

theorem conjFin_symm_conjFin (σ : M ≃+* M) (y : Af M) : conjFin σ.symm (conjFin σ y) = y := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField M
  refine congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := M)).equalizer
    ((continuous_conjFin _).comp (continuous_conjFin _)) continuous_id (funext fun k => ?_)) y
  simp only [Function.comp_apply, id]
  rw [conjFin_algebraMap, conjFin_algebraMap, RingEquiv.symm_apply_apply]

def finEquiv (σ : M ≃+* M) : Af M ≃+* Af M where
  __ := conjFin σ
  invFun := conjFin σ.symm
  left_inv y := conjFin_symm_conjFin σ y
  right_inv y := by simpa using conjFin_symm_conjFin σ.symm y

end UpperTheory.CBC.GaloisActionOnAdeles


open UpperTheory.CBC.GaloisActionOnAdeles in
def UpperTheory.CBC.SGalAdEx : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] (σ : M ≃+* M), ∃ s : Ad M ≃+* Ad M, UpperTheory.CBC.IsGalAd σ s

open UpperTheory.CBC.GaloisActionOnAdeles in
theorem UpperTheory.CBC.SGalAdEx_holds : UpperTheory.CBC.SGalAdEx := by
  intro M _ _ σ
  refine ⟨RingEquiv.prodCongr (infEquiv σ) (finEquiv σ), ?_, fun x => ?_, fun x => rfl⟩
  · exact (continuous_infEquiv σ).prodMap (continuous_conjFin σ)
  · exact Prod.ext (infEquiv_algebraMap σ x) (conjFin_algebraMap σ x)
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC

def SCuspOf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) sat inf, IsCusp (F := F) n sat inf → ∃ π : Cusp F n, π.sat = sat ∧ π.inf = inf

def SIsCusp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n), IsCusp (F := F) n π.sat π.inf

def SIsoSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π π' : Cusp F n), π.Iso π' → ∀ w B, π.sat w B → π'.sat w B

def STwSat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n) (η : HChar F),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ ∀ B, π.sat v B → (π.twist η).sat v (B.map (· * η.val v))

def SSatEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.sat v B

def SSatUniq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : Cusp F n) v B B', π.sat v B → π.sat v B' → B = B'

def SConjSpaceC : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] (σ : M ≃+* M) (s : Ad M ≃+* Ad M), IsGalAd σ s →
    ∀ (n : ℕ) (P : CuspSub M n), ∃ P' : CuspSub M n,
      (Cusp.cx P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space

def SConjSpaceR : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsTotallyReal M] (σ : M ≃+* M) (s : Ad M ≃+* Ad M), IsGalAd σ s →
    ∀ (n : ℕ) (P : UpperTheory.V.TR.CuspSub M n), ∃ P' : UpperTheory.V.TR.CuspSub M n,
      (Cusp.re P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.re P).space

def SConjSatC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [_root_.NumberField.IsTotallyComplex M] (σ : M ≃ₐ[K] M)
    (s : Ad M ≃+* Ad M), IsGalAd σ.toRingEquiv s → ∀ (n : ℕ) (P P' : CuspSub M n),
    (Cusp.cx P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space →
    ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
      (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, (CG.mk P).HasSat (g w) B → (CG.mk P').HasSat w B

def SConjSatR : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsTotallyReal M] (σ : M ≃ₐ[K] M)
    (s : Ad M ≃+* Ad M), IsGalAd σ.toRingEquiv s → ∀ (n : ℕ) (P P' : UpperTheory.V.TR.CuspSub M n),
    (Cusp.re P').space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.re P).space →
    ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
      (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, P.HasSat (g w) B → P'.HasSat w B

def SNormPow : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f

end UpperTheory.CBC
end
end
