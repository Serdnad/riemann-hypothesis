module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.RingTheory.Etale.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Etale.Weakly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

section

noncomputable section

namespace GlobalTheory

theorem dvr_loc_principal_prime : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  intro L _ A t hN ht hp hfr
  set p : Ideal A := Ideal.span {t} with hpdef
  haveI : IsFractionRing A L := IsFractionRing.of_field A L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V0 : Subalgebra A L := Localization.subalgebra.ofField L p.primeCompl p.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime V0 p := Localization.subalgebra.isLocalization_ofField _ _ _
  haveI : IsLocalRing V0 := IsLocalization.AtPrime.isLocalRing V0 p
  haveI : IsNoetherianRing V0 := IsLocalization.isNoetherianRing p.primeCompl V0 hN
  have hmax : IsLocalRing.maximalIdeal V0 = Ideal.span {algebraMap A V0 t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p V0, hpdef, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap A V0 t ≠ 0 := fun h => ht (congrArg Subtype.val h)
  have hnf : ¬ IsField V0 := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact ht0
  have hdvr : IsDiscreteValuationRing V0 :=
    ((IsDiscreteValuationRing.TFAE V0 hnf).out 1 5).2
      (⟨⟨_, hmax⟩⟩ : (IsLocalRing.maximalIdeal V0).IsPrincipal)
  haveI : IsFractionRing V0 L := IsFractionRing.of_field V0 L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨algebraMap A V0 ⟨a, ha⟩, algebraMap A V0 ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V : ValuationSubring L :=
    { V0.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger V0 x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact Or.inl (hy ▸ y.2)
        · exact Or.inr (hy ▸ y.2) }
  have hA : ∀ a ∈ A, a ∈ V := fun a ha => V0.algebraMap_mem (⟨a, ha⟩ : A)
  refine ⟨V, hA, hdvr, ?_, ?_, ?_, ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  · intro s hs
    exact IsLocalization.map_units V0 (⟨s, hs⟩ : p.primeCompl)
  · intro f
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective p.primeCompl (show V0 from f)
    refine ⟨x, y, y.2, ?_⟩
    have := congrArg (algebraMap V0 L) (IsLocalization.mk'_spec V0 x y)
    have hxy' : IsLocalization.mk' V0 x y = (show V0 from f) := hxy
    rw [hxy', map_mul] at this
    exact this
  · have h := (RingHom.essFiniteType_algebraMap (R := A) (S := V0)).2
      (Algebra.EssFiniteType.of_isLocalization V0 p.primeCompl)
    exact h

end GlobalTheory
end
end

section

open TensorProduct

namespace GlobalTheory

theorem etale_adjoin_baseChange_image (R S B : Type) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S)
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀)
    (S' : Subalgebra R S) (h : A₀ ≤ S') :
    ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))))
      (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))),
      Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  set C := Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) with hC
  letI : Algebra A₀ S' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let ι : S' →ₐ[A₀] S :=
    { toRingHom := S'.val.toRingHom
      commutes' := fun _ => rfl }
  let Φ : S' ⊗[A₀] B₀ →ₐ[A₀] S ⊗[A₀] B₀ := Algebra.TensorProduct.map ι (AlgHom.id A₀ B₀)
  let Ψ : S' ⊗[A₀] B₀ →+* B := (e.symm : S ⊗[A₀] B₀ →+* B).comp Φ.toRingHom
  haveI : Module.Flat A₀ B₀ := inferInstance
  have hΦ : Function.Injective Φ := by
    have hl : (Φ.toLinearMap : S' ⊗[A₀] B₀ →ₗ[A₀] S ⊗[A₀] B₀) = LinearMap.rTensor B₀ ι.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      rfl
    have : Function.Injective (LinearMap.rTensor B₀ ι.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b hab => Subtype.ext hab)
    rw [← hl] at this
    exact this
  have hΨ : Function.Injective Ψ := e.symm.injective.comp hΦ
  have htmul : ∀ (s : S') (b : B₀), Ψ (s ⊗ₜ b) = algebraMap S B s * e.symm (1 ⊗ₜ b) := by
    intro s b
    have : ((s : S) ⊗ₜ[A₀] b : S ⊗[A₀] B₀) = algebraMap S (S ⊗[A₀] B₀) s * (1 ⊗ₜ b) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    show e.symm ((s : S) ⊗ₜ[A₀] b) = _
    rw [this, map_mul, AlgEquiv.commutes]
  have h1 : e.symm ((1 : S) ⊗ₜ[A₀] (1 : B₀)) = 1 := by
    rw [← Algebra.TensorProduct.one_def, map_one]
  have hsub : ∀ x, Ψ x ∈ C := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      rw [htmul]
      exact C.mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, s.2, rfl⟩))
        (Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add (f := _)]; exact C.add_mem hx hy
  have hsurj : (C : Set B) ⊆ Set.range Ψ := by
    have := Algebra.adjoin_eq_ring_closure (R := R)
      ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))
    intro y hy
    have hy' : y ∈ (C.toSubring) := hy
    rw [hC, this] at hy'
    have hle : Subring.closure (Set.range (algebraMap R B) ∪
        ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))
        ≤ Ψ.range := by
      rw [Subring.closure_le]
      rintro z (⟨r, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨b, rfl⟩)
      · refine ⟨(algebraMap R S' r) ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one, IsScalarTower.algebraMap_apply R S B]
        rfl
      · refine ⟨(⟨s, hs⟩ : S') ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one]
      · refine ⟨1 ⊗ₜ b, ?_⟩
        rw [htmul]; simp
    exact hle hy'
  let f : S' ⊗[A₀] B₀ →+* C := Ψ.codRestrict C.toSubring hsub
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => hΨ (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj hy
    exact ⟨x, rfl⟩
  let eqv : S' ⊗[A₀] B₀ ≃+* C := RingEquiv.ofBijective f hf
  letI alg : Algebra S' C := (f.comp (algebraMap S' (S' ⊗[A₀] B₀))).toAlgebra
  have tower : IsScalarTower R S' C := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    apply Subtype.ext
    show algebraMap R B r = Ψ (algebraMap S' (S' ⊗[A₀] B₀) (algebraMap R S' r))
    rw [Algebra.TensorProduct.algebraMap_apply, htmul, h1, mul_one,
      IsScalarTower.algebraMap_apply R S B]
    rfl
  refine ⟨alg, tower, ?_⟩
  let eA : S' ⊗[A₀] B₀ ≃ₐ[S'] C := AlgEquiv.ofRingEquiv (f := eqv) (fun _ => rfl)
  haveI : Algebra.Etale S' (S' ⊗[A₀] B₀) := Algebra.Etale.baseChange A₀ B₀ S'
  exact Algebra.Etale.of_equiv eA

end GlobalTheory
end

section

open IsLocalRing Polynomial TensorProduct

namespace GlobalTheory

theorem tensor_directedSystem_of_flat (R : Type) [CommRing R] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] (k₀ : ι) (P : ι → Type) [∀ k, CommRing (P k)]
    [instP : ∀ k, Algebra R (P k)] (Q : Type) [CommRing Q] [Algebra R Q]
    (E₀ : Type) [CommRing E₀] [Algebra R E₀] [Module.Flat R E₀]
    (inc : ∀ k l, k ≤ l → P k →ₐ[R] P l) (sub : ∀ k, P k →ₐ[R] Q)
    (hinc_id : ∀ k (hkk : k ≤ k) (p : P k), inc k k hkk p = p)
    (hinc_comp : ∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (p : P k),
      inc k m hkm p = inc l m hlm (inc k l hkl p))
    (hsub_comp : ∀ k l (hkl : k ≤ l) (p : P k), sub l (inc k l hkl p) = sub k p)
    (hsub_inj : ∀ k, Function.Injective (sub k))
    (hcov : ∀ q : Q, ∃ k p, sub k p = q) :
    ∃ (h : ∀ k l, k ≤ l → P k ⊗[R] E₀ →+* P l ⊗[R] E₀) (e : ∀ k, P k ⊗[R] E₀ →+* Q ⊗[R] E₀),
      (∀ k l (hkl : k ≤ l) (p : P k) (y : E₀), h k l hkl (p ⊗ₜ y) = inc k l hkl p ⊗ₜ y) ∧
      (∀ k (p : P k) (y : E₀), e k (p ⊗ₜ y) = sub k p ⊗ₜ y) ∧
      (∀ k l (hkl : k ≤ l) (y : P k ⊗[R] E₀), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : P k ⊗[R] E₀), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : P k ⊗[R] E₀),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ z : Q ⊗[R] E₀, ∃ k y, e k y = z) := by
  let h : ∀ k l, k ≤ l → P k ⊗[R] E₀ →+* P l ⊗[R] E₀ := fun k l hkl =>
    (Algebra.TensorProduct.map (inc k l hkl) (AlgHom.id R E₀)).toRingHom
  let e : ∀ k, P k ⊗[R] E₀ →+* Q ⊗[R] E₀ := fun k =>
    (Algebra.TensorProduct.map (sub k) (AlgHom.id R E₀)).toRingHom
  have hh : ∀ k l (hkl : k ≤ l) (p : P k) (y : E₀), h k l hkl (p ⊗ₜ y) = inc k l hkl p ⊗ₜ y :=
    fun k l hkl p y => by simp [h]
  have he : ∀ k (p : P k) (y : E₀), e k (p ⊗ₜ y) = sub k p ⊗ₜ y :=
    fun k p y => by simp [e]
  have hcompat : ∀ k l (hkl : k ≤ l) (y : P k ⊗[R] E₀), e l (h k l hkl y) = e k y := by
    intro k l hkl y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, he, he, hsub_comp]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]
  refine ⟨h, e, hh, he, hcompat, ?_, ?_, ?_, ?_⟩
  · intro k hkk y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, hinc_id]
    | add a b ha hb => rw [map_add (f := _), ha, hb]
  · intro k l m hkl hlm hkm y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, hh, hh, hinc_comp k l m hkl hlm hkm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  · intro k
    have hfun : ⇑(e k) = ⇑(LinearMap.rTensor E₀ (sub k).toLinearMap) := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul p y => rw [he, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    rw [hfun]
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (hsub_inj k)
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨k₀, 0, map_zero _⟩
    | tmul q y =>
      obtain ⟨k, p, rfl⟩ := hcov q
      exact ⟨k, p ⊗ₜ y, he k p y⟩
    | add a b ha hb =>
      obtain ⟨k₁, y₁, rfl⟩ := ha
      obtain ⟨k₂, y₂, rfl⟩ := hb
      obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) k₁ k₂
      exact ⟨m, h k₁ m h₁ y₁ + h k₂ m h₂ y₂, by rw [map_add (f := _), hcompat, hcompat]⟩

theorem directedSystem_etaleBaseChange : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (i₀ : ι), (∀ k, i₀ ≤ k) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E]
      (E₀ : Type) [CommRing E₀] [Algebra (Polynomial (𝒜 i₀)) E₀] [Algebra.Etale (Polynomial (𝒜 i₀)) E₀],
      (letI : Algebra (Polynomial (𝒜 i₀)) (Polynomial T) :=
          (Polynomial.mapRingHom (𝒜 i₀).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i₀)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) →
    ∃ (Ek : ι → Type) (_ : ∀ k, CommRing (Ek k)) (_ : ∀ k, Algebra (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra (𝒜 k) (Ek k)) (_ : ∀ k, IsScalarTower (𝒜 k) (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra.Etale (Polynomial (𝒜 k)) (Ek k))
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k, (e k).comp (algebraMap (Polynomial (𝒜 k)) (Ek k)) =
          (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 k).subtype)) ∧
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) ∧
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : Ek k), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : Ek k),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ x : E, ∃ k y, e k y = x) := by
  intro T _ ι _ _ 𝒜 hA hcov i₀ h₀ E _ _ E₀ _ _ _ hφ
  obtain ⟨φ⟩ := hφ
  letI instA : ∀ k, Algebra (𝒜 i₀)[X] (𝒜 k)[X] := fun k =>
    (mapRingHom (Subring.inclusion (hA (h₀ k)))).toAlgebra
  letI instT : Algebra (𝒜 i₀)[X] T[X] := (mapRingHom (𝒜 i₀).subtype).toAlgebra
  have hincl : ∀ {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c),
      (Subring.inclusion (hA hbc)).comp (Subring.inclusion (hA hab)) =
        Subring.inclusion (hA (hab.trans hbc)) := by
    intro a b c hab hbc; ext x; rfl
  have hsub : ∀ {a b : ι} (hab : a ≤ b),
      (𝒜 b).subtype.comp (Subring.inclusion (hA hab)) = (𝒜 a).subtype := by
    intro a b hab; ext x; rfl
  let inc : ∀ k l, k ≤ l → (𝒜 k)[X] →ₐ[(𝒜 i₀)[X]] (𝒜 l)[X] := fun k l hkl =>
    { toRingHom := mapRingHom (Subring.inclusion (hA hkl))
      commutes' := fun p => by
        change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hincl (h₀ k) hkl] }
  let sub : ∀ k, (𝒜 k)[X] →ₐ[(𝒜 i₀)[X]] T[X] := fun k =>
    { toRingHom := mapRingHom (𝒜 k).subtype
      commutes' := fun p => by
        change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hsub (h₀ k)] }
  haveI : Module.Flat (𝒜 i₀)[X] E₀ := inferInstance
  have hcovT : ∀ q : T[X], ∃ k p, sub k p = q := by
    intro q
    have hq : ∃ k, ∀ n, q.coeff n ∈ 𝒜 k := by
      induction q using Polynomial.induction_on' with
      | add p q hp hq =>
        obtain ⟨k₁, h₁⟩ := hp
        obtain ⟨k₂, h₂⟩ := hq
        obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) k₁ k₂
        exact ⟨m, fun n => by
          rw [coeff_add]; exact add_mem (hA hm₁ (h₁ n)) (hA hm₂ (h₂ n))⟩
      | monomial n c =>
        obtain ⟨j, hj⟩ := hcov c
        refine ⟨j, fun m => ?_⟩
        rw [coeff_monomial_apply]
        split_ifs
        · exact hj
        · exact zero_mem _
    obtain ⟨k, hk⟩ := hq
    have hsubset : (↑q.coeffs : Set T) ⊆ 𝒜 k := by
      intro c hc
      obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact hk n
    refine ⟨k, q.toSubring (𝒜 k) hsubset, ?_⟩
    show Polynomial.map (𝒜 k).subtype _ = q
    exact Polynomial.map_toSubring _ _ _
  obtain ⟨h, e', hh, he, hcompat, hid, hcomp, hinj, hcov'⟩ :=
    tensor_directedSystem_of_flat (𝒜 i₀)[X] i₀ (fun k => (𝒜 k)[X]) (instP := instA) T[X] E₀ inc sub
      (fun k hkk p => by
        have hid : Subring.inclusion (hA hkk) = RingHom.id _ := by ext; rfl
        show Polynomial.map _ p = p
        rw [hid, Polynomial.map_id])
      (fun k l m hkl hlm hkm p => by
        show Polynomial.map _ p = Polynomial.map _ (Polynomial.map _ p)
        rw [Polynomial.map_map, hincl hkl hlm])
      (fun k l hkl p => by
        show Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hsub hkl])
      (fun k p q hpq => Polynomial.map_injective _ Subtype.val_injective hpq)
      hcovT
  let instC : ∀ k, Algebra (𝒜 k) (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀) := fun k =>
    ((algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)).comp (Polynomial.C)).toAlgebra
  have instS : ∀ k, @IsScalarTower (𝒜 k) (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀) _ _
      (instC k).toSMul := fun k =>
    letI := instC k
    IsScalarTower.of_algebraMap_eq (fun a => by
        change (algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)) (Polynomial.C a) =
          (algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)) (algebraMap (𝒜 k) (𝒜 k)[X] a)
        rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply])
  refine ⟨fun k => TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀, fun k => inferInstance,
    fun k => inferInstance, instC, instS, fun k => inferInstance,
    fun k => φ.toRingHom.comp (e' k), h, ?_, ?_, ?_, hid, hcomp, ?_, ?_⟩
  · intro k
    refine RingHom.ext fun p => ?_
    show φ (e' k (p ⊗ₜ 1)) = algebraMap T[X] E (Polynomial.map (𝒜 k).subtype p)
    rw [he, ← φ.commutes]
    rfl
  · intro k l hkl a
    show h k l hkl (C a ⊗ₜ 1) = C (Subring.inclusion (hA hkl) a) ⊗ₜ 1
    rw [hh]
    show Polynomial.map _ (C a) ⊗ₜ 1 = _
    rw [Polynomial.map_C]
  · intro k l hkl y
    exact congrArg φ (hcompat k l hkl y)
  · intro k
    exact φ.injective.comp (hinj k)
  · intro x
    obtain ⟨k, y, hy⟩ := hcov' (φ.symm x)
    refine ⟨k, y, ?_⟩
    show φ (e' k y) = x
    rw [hy, AlgEquiv.apply_symm_apply]

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem formallyEtale_mvPolynomial_eval₂_tensor {k R B : Type} [CommRing k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B)
    (hf : (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale) :
    (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  set f := MvPolynomial.eval₂Hom (algebraMap k B) τ with hfdef
  set g := MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i) with hgdef
  letI : Algebra (MvPolynomial (Fin r) k) B := f.toAlgebra
  letI : Algebra (MvPolynomial (Fin r) R) (R ⊗[k] B) := g.toAlgebra
  letI : Algebra B (R ⊗[k] B) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra (MvPolynomial (Fin r) k) (R ⊗[k] B) :=
    (g.comp (algebraMap (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R))).toAlgebra
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) k) B := hf
  have key : g.comp (algebraMap (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R)) =
      (algebraMap B (R ⊗[k] B)).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C, f, g,
        MvPolynomial.eval₂Hom_C]
      show (algebraMap k R a) ⊗ₜ[k] (1 : B) = (1 : R) ⊗ₜ[k] algebraMap k B a
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X, f, g,
        MvPolynomial.eval₂Hom_X']
      rfl
  haveI : IsScalarTower k (MvPolynomial (Fin r) k) B := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, f, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_def]
  haveI : IsScalarTower k B (R ⊗[k] B) := IsScalarTower.of_algebraMap_eq fun x =>
    ((Algebra.TensorProduct.includeRight : B →ₐ[k] R ⊗[k] B).commutes x).symm
  haveI : IsScalarTower (MvPolynomial (Fin r) k) B (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, key]; rfl
  haveI : IsScalarTower (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower k (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq,
        Algebra.TensorProduct.algebraMap_apply]
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, g, MvPolynomial.algebraMap_eq,
        Algebra.TensorProduct.algebraMap_apply]
  haveI h1 : Algebra.IsPushout k B R (R ⊗[k] B) := inferInstance
  haveI h2 : Algebra.IsPushout (MvPolynomial (Fin r) k) B (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin r) k) R (MvPolynomial (Fin r) R)
      (T := B) (T' := R ⊗[k] B)).1 h1
  haveI : Algebra.IsPushout (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) B (R ⊗[k] B) :=
    h2.symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (R ⊗[k] B) :=
    Algebra.FormallyEtale.of_equiv
      (Algebra.IsPushout.equiv (MvPolynomial (Fin r) k) (MvPolynomial (Fin r) R) B (R ⊗[k] B))
  exact this

end GlobalTheory
end

section

noncomputable section
namespace GlobalTheory.DenseSec

def EtChart (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {g : ℕ} (t : Fin g → A) (h : A) : Prop :=
  letI : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h)

def pt {R A Ω : Type} [CommRing R] [CommRing A] [Algebra R A] [Field Ω] [Algebra R Ω] (a : A →ₐ[R] Ω) :
    TensorProduct R Ω A →ₐ[Ω] Ω :=
  Algebra.TensorProduct.lift (AlgHom.id Ω Ω) a (fun _ _ => Commute.all _ _)

end GlobalTheory.DenseSec
end
end
