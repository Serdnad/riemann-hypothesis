module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle122
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing

theorem odd_of_involution {k₀ k : Type} [Field k₀] [Field k] [Fintype k₀] [Finite k] (ι : k₀ →+* k) (q d : ℕ)
    (h0 : Fintype.card k₀ = q ^ 2) (hk : Nat.card k = q ^ (2 * d)) (τ : k ≃+* k) (hτ : ∀ z, τ (τ z) = z)
    (x y : k₀) (hxy : τ (ι x) = ι y) (hne : x ≠ y) : Odd d := by
  classical
  have hfix : ∀ m : ℕ, τ (ι x) ≠ (ι x) ^ (q ^ (2 * m)) := by
    intro m h
    rw [← map_pow, pow_mul, ← h0, FiniteField.pow_card_pow, hxy] at h
    exact hne (ι.injective h).symm
  letI := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let τA : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := τ) (fun r => by
    have := RingHom.ext_zmod ((τ : k →+* k).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)
    exact DFunLike.congr_fun this r)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 τA
  have hord := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k
  have hsq : τA ^ 2 = 1 := AlgEquiv.ext fun z => hτ z
  have hdvd : Module.finrank (ZMod p) k ∣ 2 * n.1 := by
    have := orderOf_dvd_iff_pow_eq_one.2
      (show FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * n.1) = 1 by
        rw [pow_mul']; exact (congrArg (· ^ 2) hn).trans hsq)
    rwa [hord] at this
  have hcard : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hτz : ∀ z, τ z = z ^ (p ^ n.1) := by
    intro z
    have h1 := DFunLike.congr_fun hn z
    simp only at h1
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h1
    exact h1.symm
  have hN := n.2
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hh
    push_neg at hh
    nlinarith
  interval_cases c
  · exfalso
    have hn0 : n.1 = 0 := by omega
    apply hfix 0
    rw [hτz, hn0]; simp
  · have hpq : p ^ n.1 = q ^ d := by
      have e1 : p ^ (2 * n.1) = q ^ (2 * d) := by
        rw [← hk, Nat.card_eq_fintype_card, hcard, hc, mul_one]
      have e : (p ^ n.1) ^ 2 = (q ^ d) ^ 2 := by
        rw [← pow_mul, ← pow_mul, mul_comm n.1 2, mul_comm d 2]; exact e1
      exact Nat.pow_left_injective two_ne_zero e
    by_contra hodd
    obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hodd
    apply hfix m
    rw [hτz, hpq, hm, two_mul]

end GlobalTheory.UnitLemma.ResDeg

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing

variable {K : UQ}

def sigmaAdj (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g) :
    Algebra.adjoin K.O ({B.g} : Set B.A) ≃+* Algebra.adjoin K.O ({B.g} : Set B.A) where
  toFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  invFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  left_inv y := Subtype.ext (B.σ_σ (y : B.A))
  right_inv y := Subtype.ext (B.σ_σ (y : B.A))
  map_mul' x y := Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
  map_add' x y := Subtype.ext (map_add B.σ (x : B.A) (y : B.A))

theorem card_residueField (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) :
    ∃ d : ℕ, Odd d ∧
      Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) := by
  set_option synthInstance.maxHeartbeats 200000 in
  classical
  haveI := hl
  haveI : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
    Module.Finite.iff_fg.mpr hi.fg_adjoin_singleton
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  haveI : Finite (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) :=
    Module.finite_of_finite (ResidueField K.O)
  letI : Fintype (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))) := Fintype.ofFinite _
  set τ := ResidueField.mapEquiv (sigmaAdj B hu hi)
  have hτ : ∀ z, τ (τ z) = z := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    simp only [τ, ResidueField.mapEquiv_apply, ResidueField.map_residue]
    congr 1
    exact Subtype.ext (B.σ_σ r)
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  refine ⟨Module.finrank (ResidueField K.O) (ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A))),
    odd_of_involution (algebraMap (ResidueField K.O) _) K.q _ ?_ ?_ τ hτ (residue K.O x) (residue K.O y) ?_ ?_, ?_⟩
  · rw [← K.card_res, Nat.card_eq_fintype_card]
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]
  · show ResidueField.map _ (residue _ (algebraMap K.O _ x)) = residue _ (algebraMap K.O _ y)
    rw [ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hxy, ← IsScalarTower.algebraMap_apply]
  · intro h
    exact hne (Ideal.Quotient.eq.1 h)
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ResidueField K.O), ← Nat.card_eq_fintype_card,
      K.card_res, pow_mul]

theorem card_residueField_prod : ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)),
      ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField
        (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  intro K _ B₁ B₂ h₁ h₂ _ i₁ i₂ hl
  exact card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl

end GlobalTheory.UnitLemma.ResDeg
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.NormClass

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial

section Orb

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

def mulLatEquiv (u : Aˣ) : Submodule O A ≃ Submodule O A where
  toFun := mulLat O (u : A)
  invFun := mulLat O ((u⁻¹ : Aˣ) : A)
  left_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.inv_mul_cancel_left]
  right_inv L := by
    ext y
    simp only [mem_mulLat, inv_inv, Units.mul_inv_cancel_left]

end Orb

variable {K : UQ}

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem isLat_mulLat_unit {E : Type} [Field E] [Algebra E A] (u : Aˣ) (L : Submodule O A)
    (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) : _root_.GlobalTheory.UnitLemma.IsLat O E (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  unfold _root_.GlobalTheory.UnitLemma.IsLat at hL ⊢
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    exact hL.1.map _
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    rw [Submodule.map_coe]
    have e : (⇑(LinearMap.mulLeft O (u : A))) = ⇑(LinearMap.mulLeft E (u : A)) := rfl
    rw [e, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨((u⁻¹ : Aˣ) : A) * z, by simp⟩

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem forall_mem_mulLat_unit_iff (u : Aˣ) (L : Submodule O A) (P : A → Prop) :
    (∀ z ∈ _root_.GlobalTheory.UnitLemma.mulLat O (u : A) L, P z) ↔ ∀ z ∈ L, P (u * z) := by
  constructor
  · intro h z hz
    exact h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L _).mpr (by rwa [Units.inv_mul_cancel_left]))
  · intro h z hz
    have := h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L z).mp hz)
    rwa [Units.mul_inv_cancel_left] at this

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
private theorem herm_mul_unit_sigma (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ) (a b : B.A) :
    B.herm (x * (u * B.σ (u : B.A))) a b = B.herm x (u * a) (u * b) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  simp only [map_mul]
  congr 1
  ring

open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
private theorem mem_X_mul_unit_sigma_iff (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ)
    (L : Submodule K.O B.A) :
    L ∈ B.X (x * (u * B.σ (u : B.A))) ↔ _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.X
  simp only [Set.mem_setOf_eq]
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine ⟨isLat_mulLat_unit u L, fun h => ?_⟩
    have := isLat_mulLat_unit (u⁻¹) _ h
    have hL : _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L) = L :=
      (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv L
    rwa [hL] at this
  · rw [forall_mem_mulLat_unit_iff]
    constructor
    · intro h z hz
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left]
      exact h z hz
    · intro h z hz
      have := h z hz
      rwa [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left] at this
  · constructor
    · intro h w
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, h, forall_mem_mulLat_unit_iff]
      simp only [herm_mul_unit_sigma, Units.mul_inv_cancel_left]
    · intro h w
      have := h (u * w)
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, Units.inv_mul_cancel_left, forall_mem_mulLat_unit_iff] at this
      rw [this]
      simp only [herm_mul_unit_sigma]

open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem mulLat_unit_comm (u t : Aˣ) (L : Submodule O A) :
    _root_.GlobalTheory.UnitLemma.mulLat O (u : A) (_root_.GlobalTheory.UnitLemma.mulLat O (t : A) L) =
      _root_.GlobalTheory.UnitLemma.mulLat O (t : A) (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  ext y
  simp only [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat]
  rw [mul_left_comm]


open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
theorem _root_.GlobalTheory.UnitLemma.NormClass.N_norm_class : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ),
    B.N (x * (u * B.σ (u : B.A))) = B.N x ∧
      K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  intro K B x u
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum
    simp only [one_mul]
    let wt : Submodule K.O B.A → ℚ := fun L =>
      ((_root_.GlobalTheory.UnitLemma.stabLat K.O L ⊓ B.T).relIndex (_root_.GlobalTheory.UnitLemma.intUnits K.O B.A ⊓ B.T) : ℚ)
    have hwt : ∀ (t : B.Aˣ) (L : Submodule K.O B.A), wt (_root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) = wt L := by
      intro t L
      simp only [wt, _root_.GlobalTheory.UnitLemma.Orbit.stabLat_mulLat]
    have hrel : ∀ (X : Set (Submodule K.O B.A)) (a b : X),
        (∃ t ∈ B.T, (b : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) a) → wt a = wt b := by
      rintro X a b ⟨t, -, h⟩
      rw [h, hwt]
    have hout : ∀ (X : Set (Submodule K.O B.A)) (o : Quot (fun L M : X => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L)),
        wt ((Quot.out o : X) : Submodule K.O B.A) = Quot.lift (fun a : X => wt a) (hrel X) o := by
      intro X o
      conv_rhs => rw [← Quot.out_eq o]
    show (∑ᶠ o : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X (x * (u * B.σ (u : B.A)))) : Submodule K.O B.A)) =
      ∑ᶠ o : Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X x) : Submodule K.O B.A)
    simp only [hout]
    have hφ : ∀ L : B.X (x * (u * B.σ (u : B.A))), _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x :=
      fun L => (mem_X_mul_unit_sigma_iff B x u L).mp L.2
    have hψ : ∀ M : B.X x, _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M ∈ B.X (x * (u * B.σ (u : B.A))) := by
      intro M
      refine (mem_X_mul_unit_sigma_iff B x u _).mpr ?_
      have hM : _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M) = M :=
        (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A)
      rw [hM]
      exact M.2
    let e : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) ≃
        Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) :=
      { toFun := Quot.map (fun L => ⟨_, hφ L⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u t (a : Submodule K.O B.A))
        invFun := Quot.map (fun M => ⟨_, hψ M⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u⁻¹ t (a : Submodule K.O B.A))
        left_inv := by
          intro o
          induction o using Quot.ind with
          | mk L => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv (L : Submodule K.O B.A)))
        right_inv := by
          intro o
          induction o using Quot.ind with
          | mk M => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A))) }
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun o => ?_
    induction o using Quot.ind with
    | mk L => exact (hwt u (L : Submodule K.O B.A)).symm
  · let φ : B.A ≃ₗ[K.E] B.A :=
      { LinearMap.mulLeft K.E (u : B.A) with
        invFun := fun z => ((u⁻¹ : B.Aˣ) : B.A) * z
        left_inv := fun z => Units.inv_mul_cancel_left u z
        right_inv := fun z => Units.mul_inv_cancel_left u z }
    have e : B.gramDet (x * (u * B.σ (u : B.A))) =
        (Matrix.of fun i j => B.herm x (((Module.finBasis K.E B.A).map φ) i)
          (((Module.finBasis K.E B.A).map φ) j)).det := by
      unfold _root_.GlobalTheory.UnitLemma.InvAlg.gramDet
      simp only [herm_mul_unit_sigma, Module.Basis.map_apply]
      rfl
    rw [e, _root_.GlobalTheory.UnitLemma.Orbit.eta_gram]

end GlobalTheory.UnitLemma.NormClass
end
end

section

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.NB

namespace GlobalTheory.WachTie

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

def piNorm : O⟦X⟧ := ∏ δ ∈ W.DelF, W.γ₀ δ X

def FrTie (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) : Prop :=
  Function.Injective j ∧
  (∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  (∀ a, j (R.φ a) = W.φ₀ (j a)) ∧
  (∀ a, j (R.γ a) = W.γ₀ W.gam (j a)) ∧
  R.χ = W.χΓ W.gam ∧
  R.s = W.DelF.card ∧
  Associated (j X) (X ^ R.s) ∧
  Associated (j R.E) W.q₀

def EETie (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) : Prop :=
  (∀ a : ZMod n → O⟦X⟧, jE (fun i => R.ι (a i)) = algebraMap (LetA O n) W.EE (fun i => j (a i))) ∧
  Function.Injective jE ∧
  (∀ y, (∃ x, jE x = y) ↔ ∀ δ ∈ W.DelF, W.γE δ y = y) ∧
  (∀ x, jE (fun i => R.φE (x (i - 1))) = W.φE (jE x)) ∧
  (∀ x, jE (fun i => R.γE (x i)) = W.γE W.gam (jE x))

def coord (R : Fr l O) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ}
    (b : Fin r → W.DD T) : DD R n r →ₗ[O] W.DD T where
  toFun x := ∑ k, jE (fun i => x i k) • b k
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul, ← map_add (f := _)]; rfl
  map_smul' c x := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_assoc, ← map_smul]; rfl

theorem coord_apply (R : Fr l O) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ}
    (b : Fin r → W.DD T) (x : DD R n r) :
    coord W R jE T b x = ∑ k, jE (fun i => x i k) • b k := rfl

def DDinv (T : LocLat G Qp LL O) : Submodule O (W.DD T) where
  carrier := {x | ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := fun δ _ => map_zero _
  add_mem' := fun ha hb δ hδ => by rw [map_add (f := _), ha δ hδ, hb δ hδ]
  smul_mem' := fun c a ha δ hδ => by rw [map_smul, ha δ hδ]

def wachDeltaInvariantCoboundaries (T : LocLat G Qp LL O) : Submodule O (W.DD T × W.DD T) :=
  (DDinv W T).map ((W.φD T - LinearMap.id).prod (W.γD T W.gamK - LinearMap.id))

def SysTie (R : Fr l O) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (S : Sys R n r) : Prop :=
  let Θ := coord W R jE T (fun k => (b k : W.DD T))
  (∀ k, (b k : W.DD T) ∈ W.NΔ T) ∧
  Function.Injective Θ ∧
  LinearMap.range Θ = DDinv W T ∧
  (∀ x, Θ x ∈ W.NΔ T ↔ ∀ i, x i ∈ R.N0 r) ∧
  (∀ x, Θ (S.φD x) = W.φD T (Θ x)) ∧
  (∀ x, Θ (S.γD x) = W.γD T W.gam (Θ x)) ∧
  S.Z1.map (Θ.prodMap Θ) = W.wachCocyclesDelta T ∧
  S.B1.map (Θ.prodMap Θ) = wachDeltaInvariantCoboundaries W T

end GlobalTheory.WachTie
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory.JR.ScaleHaarL

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  intro F E _ _ _ _ U A μ hμ c S
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := GlobalTheory.JR.EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  let u : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) c
  have hu : (u : A.L) = algebraMap A.K A.L (c : A.K) := rfl
  have hset : {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = u • S := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, Units.smul_def, hu, smul_eq_mul]
    exact ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩
  have hc1 : Continuous (b.equivFun.symm : (Fin 2 → A.K) → A.L) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F)
  have hc2 : Continuous (b.equivFun : A.L → (Fin 2 → A.K)) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)
  let e : (Fin 2 → A.K) ≃ₜ+ A.L :=
    { b.equivFun.symm.toAddEquiv with
      continuous_toFun := hc1
      continuous_invFun := hc2 }
  have key : distribHaarChar A.L u = distribHaarChar A.K c ^ 2 := by
    rw [GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e c u (fun x => ?_),
      GlobalTheory.JR.ModuleNorm.distribHaarChar_pi_two]
    change b.equivFun.symm ((c : A.K) • x) = (u : A.L) * b.equivFun.symm x
    rw [map_smul, Algebra.smul_def, hu]
  rw [hset, ← distribHaarChar_mul μ u S, key, GlobalTheory.JR.EtMeas.absK_unit]
  rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.JR.ScaleHaarL
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  first | exact @GlobalTheory.JR.NormInt.main | exact GlobalTheory.JR.NormInt.main | (intros; apply GlobalTheory.JR.NormInt.main <;> assumption)
end
