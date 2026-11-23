module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.SepModel

theorem tmul_mem_cenOrder {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ}
    (hN : ¬ ℓ ∣ N) {c : F} (hc : IsIntegral ℤ ((N : F) * c)) :
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c ∈ cenOrder ℓ F := by
  have hu : IsUnit (N : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  obtain ⟨u, hu⟩ := hu
  have hmem : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) ∈ cenOrder ℓ F :=
    Algebra.subset_adjoin ⟨⟨_, hc⟩, rfl⟩
  have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c = (↑u⁻¹ : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c)) := by
    have h1 : (u : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) := by
      rw [hu, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]
    rw [← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [heq]
  exact Subalgebra.smul_mem _ hmem _

theorem exists_nat_integral {F : Type} [Field F] [NumberField F] (s : Finset F) :
    ∃ N : ℕ, 0 < N ∧ ∀ c ∈ s, IsIntegral ℤ ((N : F) * c) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := F) s
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun c hc => ?_⟩
  have h := hy c hc
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h; simpa using h
  · rw [e] at h
    have := h.neg
    simpa [neg_mul] using this

end GlobalTheory.SepModel

namespace GlobalTheory.SepModel

end GlobalTheory.SepModel
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzCovol

open NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def embPlace : (F →+* ℝ) ≃ {w : InfinitePlace F // IsReal w} where
  toFun τ := ⟨mk (Complex.ofRealHom.comp τ), IsTotallyReal.isReal _⟩
  invFun w := embedding_of_isReal w.2
  left_inv τ := by
    have h : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) :=
      isReal_of_mk_isReal (IsTotallyReal.isReal _)
    ext x
    apply Complex.ofReal_injective
    rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal h]
    rfl
  right_inv w := by
    apply Subtype.ext
    have : Complex.ofRealHom.comp (embedding_of_isReal w.2) = embedding w.1 := by
      ext x; simp
    simp only [this, mk_embedding]

theorem embPlace_symm_apply (w : {w : InfinitePlace F // IsReal w}) :
    (embPlace.symm w : F →+* ℝ) = embedding_of_isReal w.2 := rfl

instance isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩

def toMixed : RSp F ≃ₗ[ℝ] mixedSpace F where
  toFun x := (fun w => x (embPlace.symm w), 0)
  invFun p := WithLp.toLp 2 (fun τ => p.1 (embPlace τ))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by ext τ; simp
  right_inv p := by
    refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
    simp

theorem toMixed_remb (a : F) : toMixed (remb F a) = mixedEmbedding F a := by
  refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
  simp [toMixed, embPlace_symm_apply]

theorem measurePreserving_toMixed :
    MeasurePreserving (toMixed (F := F)).toContinuousLinearEquiv volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (F →+* ℝ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace F // IsReal w} => ℝ)
    (embPlace (F := F))
  have h3 : MeasurePreserving (fun y : {w : InfinitePlace F // IsReal w} → ℝ =>
      (y, (0 : {w : InfinitePlace F // IsComplex w} → ℂ))) volume volume := by
    refine ⟨measurable_id.prodMk measurable_const, ?_⟩
    rw [Measure.volume_eq_prod, show (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) =
      Measure.dirac 0 from Measure.volume_pi_eq_dirac 0, Measure.prod_dirac]
  have h := h3.comp (h2.comp h1)
  have he : ⇑(toMixed (F := F)).toContinuousLinearEquiv =
      (fun y : {w : InfinitePlace F // IsReal w} → ℝ =>
        (y, (0 : {w : InfinitePlace F // IsComplex w} → ℂ))) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {w : InfinitePlace F // IsReal w} => ℝ)
        (embPlace (F := F))) ∘ WithLp.ofLp := by
    funext x
    refine Prod.ext (funext fun w => ?_) rfl
    simp [toMixed, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact h

end GlobalTheory.LipschitzCovol

open scoped Classical in
open GlobalTheory.LipschitzCovol in
theorem GlobalTheory.LipschitzCovol.covolume_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)],
    ZLattice.covolume (latOf N) = covol N := by
  intro F _ _ _ N hN _ _
  have hmem : ∀ x : RSp F, x ∈ latOf N ↔
      toMixed x ∈ mixedEmbedding.idealLattice F (Units.mk0 N hN) := by
    intro x
    rw [mem_latOf, mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, by simpa using ha, (toMixed_remb a).symm⟩
    · rintro ⟨a, ha, h⟩
      refine ⟨a, by simpa using ha, toMixed.injective ?_⟩
      rw [toMixed_remb, h]
  have hL : latOf N = ZLattice.comap ℝ (mixedEmbedding.idealLattice F (Units.mk0 N hN))
      (toMixed (F := F)).toContinuousLinearEquiv.toLinearMap :=
    Submodule.ext fun x => hmem x
  have key := ZLattice.covolume_comap (mixedEmbedding.idealLattice F (Units.mk0 N hN)) volume volume
    (measurePreserving_toMixed (F := F))
  have hc := covol_eq_covolume (Units.mk0 N hN)
  rw [Units.val_mk0] at hc
  rw [hc, ← key]
  congr 1
end
end

section

open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_away : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (h : A),
    IsExcisionNbhd A A' h → ∀ a b : A', a * b - 1 ∈ Ideal.span {algebraMap A A' h} →
      IsExcisionNbhd A (Localization.Away a) h := by
  intro A A' _ _ _ h ⟨hE, hS, hI⟩ a b hab
  have hpow : ∀ n : ℕ, a ^ n * b ^ n - 1 ∈ Ideal.span {algebraMap A A' h} := by
    intro n
    have hd : a * b - 1 ∣ (a * b) ^ n - 1 ^ n := sub_dvd_pow_sub_pow _ _ _
    rw [one_pow, mul_pow] at hd
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    exact Ideal.mul_mem_right _ _ hab
  have hH : algebraMap A (Localization.Away a) h =
      algebraMap A' (Localization.Away a) (algebraMap A A' h) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hmap : ∀ x : A', x ∈ Ideal.span {algebraMap A A' h} →
      algebraMap A' (Localization.Away a) x ∈ Ideal.span {algebraMap A (Localization.Away a) h} := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [hH, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_, ?_⟩
  · haveI := hE
    haveI : Algebra.Etale A' (Localization.Away a) := inferInstance
    exact Algebra.Etale.comp A A' (Localization.Away a)
  · intro z
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) z
    obtain ⟨n, hn⟩ := s.2
    obtain ⟨c, hc⟩ := hS (y * b ^ n)
    refine ⟨c, ?_⟩
    have hs : IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n) =
        algebraMap A' (Localization.Away a) y := by
      have hn' : a ^ n = (s : A') := hn
      rw [hn']; exact IsLocalization.mk'_spec _ _ _
    have e1 : IsLocalization.mk' (Localization.Away a) y s - algebraMap A (Localization.Away a) c =
        -(IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n * b ^ n - 1)) +
          algebraMap A' (Localization.Away a) (y * b ^ n - algebraMap A A' c) := by
      rw [map_sub, map_sub, map_mul, map_mul, map_one, ← hs, ← IsScalarTower.algebraMap_apply]
      ring
    rw [e1]
    exact Ideal.add_mem _ ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (hmap _ (hpow n)))) (hmap _ hc)
  · intro x hx
    apply hI
    rw [hH] at hx
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hx
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) w
    obtain ⟨n, hn⟩ := s.2
    dsimp only at hw
    have hs : IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n) =
        algebraMap A' (Localization.Away a) y := by
      have hn' : a ^ n = (s : A') := hn
      rw [hn']; exact IsLocalization.mk'_spec _ _ _
    have key : algebraMap A' (Localization.Away a) (algebraMap A A' x * a ^ n - y * algebraMap A A' h) = 0 := by
      rw [map_sub, map_mul, map_mul, ← hs, ← IsScalarTower.algebraMap_apply A A' (Localization.Away a) x, ← hw,
        ← IsScalarTower.algebraMap_apply A A' (Localization.Away a) h]
      ring
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ _).1 key
    obtain ⟨N, hN⟩ := m.2
    have h1 : algebraMap A A' x * a ^ (N + n) ∈ Ideal.span {algebraMap A A' h} := by
      have e : algebraMap A A' x * a ^ (N + n) = (a ^ N * y) * algebraMap A A' h := by
        rw [← hN] at hm; rw [pow_add]; linear_combination hm
      rw [e]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have e2 : algebraMap A A' x = algebraMap A A' x * a ^ (N + n) * b ^ (N + n) -
        algebraMap A A' x * (a ^ (N + n) * b ^ (N + n) - 1) := by ring
    rw [e2]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ (hpow _))

end GlobalTheory.EtC
end

section

open GlobalTheory.EtC

namespace GlobalTheory.DivUnitForm

private lemma exists_sub_mem_span_pow_of_surj_mod_span {B A₂ : Type} [CommRing B] [CommRing A₂] [Algebra B A₂]
    (f : B) (hsurj : ∀ a' : A₂, ∃ a : B, a' - algebraMap B A₂ a ∈ Ideal.span {algebraMap B A₂ f})
    (n : ℕ) (a' : A₂) : ∃ a : B, a' - algebraMap B A₂ a ∈ Ideal.span {algebraMap B A₂ f ^ n} := by
  induction n generalizing a' with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih a'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨a₁, ha₁⟩ := hsurj r
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 ha₁
    refine ⟨a + f ^ n * a₁, Ideal.mem_span_singleton'.2 ⟨s, ?_⟩⟩
    have hr' : a' = r * algebraMap B A₂ f ^ n + algebraMap B A₂ a := by rw [hr]; ring
    have hs' : r = s * algebraMap B A₂ f + algebraMap B A₂ a₁ := by rw [hs]; ring
    rw [hr', hs', map_add (f := _), map_mul, map_pow]
    ring

theorem _root_.GlobalTheory.DivUnitForm.unit_form : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂]
    [Algebra B A₂] (f : B), _root_.GlobalTheory.EtC.IsExcisionNbhd B A₂ f →
    ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂),
      e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧
      algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) =
        (c : Localization.Away (algebraMap B A₂ f)) *
          algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  intro B A₂ _ _ _ f hf c
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj (algebraMap B A₂ f)
    (c : Localization.Away (algebraMap B A₂ f))
  obtain ⟨l, y, hy⟩ := IsLocalization.Away.surj (algebraMap B A₂ f)
    ((c⁻¹ : (Localization.Away (algebraMap B A₂ f))ˣ) : Localization.Away (algebraMap B A₂ f))
  have hxy : algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (x * y) =
      algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f ^ (k + l)) := by
    rw [map_mul, ← hx, ← hy, map_pow, pow_add]
    have hc : (c : Localization.Away (algebraMap B A₂ f)) *
        ((c⁻¹ : (Localization.Away (algebraMap B A₂ f))ˣ) : Localization.Away (algebraMap B A₂ f))
          = 1 := Units.mul_inv c
    linear_combination (algebraMap A₂ (Localization.Away (algebraMap B A₂ f))
      (algebraMap B A₂ f) ^ k * algebraMap A₂ (Localization.Away (algebraMap B A₂ f))
        (algebraMap B A₂ f) ^ l) * hc
  obtain ⟨⟨s, hs⟩, hsxy⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap B A₂ f))
    (Localization.Away (algebraMap B A₂ f))).1 hxy
  obtain ⟨N, rfl⟩ := hs
  simp only at hsxy
  set X := x * algebraMap B A₂ f ^ N with hX
  have hXy : X * y = algebraMap B A₂ f ^ (k + N + l) := by
    rw [hX, show k + N + l = N + (k + l) by ring, pow_add]
    linear_combination hsxy
  obtain ⟨b, hb⟩ := exists_sub_mem_span_pow_of_surj_mod_span f hf.2.1 (k + N + l + 1) X
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hb
  refine ⟨b, k + N, 1 - algebraMap B A₂ f * y * r, Ideal.mem_span_singleton'.2 ⟨-(y * r), by ring⟩, ?_⟩
  have hbX : algebraMap B A₂ b = X * (1 - algebraMap B A₂ f * y * r) := by
    have h1 : X * (1 - algebraMap B A₂ f * y * r) = X - algebraMap B A₂ f * r * (X * y) := by ring
    rw [h1, hXy]
    linear_combination hr
  rw [hbX, hX]
  simp only [map_mul, map_pow]
  rw [← hx]
  ring

end GlobalTheory.DivUnitForm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_away_of_isUnit_mod : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B),
    IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) →
    IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  intro B A' _ _ _ f s hA hs
  obtain ⟨hEt, h2, h3⟩ := hA
  obtain ⟨σ, hσ⟩ : ∃ σ : A', σ = algebraMap B A' s := ⟨_, rfl⟩
  rw [← hσ]

  obtain ⟨t, ht⟩ : ∃ t : B, s * t - 1 ∈ Ideal.span {f} := by
    obtain ⟨v, hv⟩ := hs.exists_right_inv
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective v
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
  have hpow : ∀ n : ℕ, (s * t) ^ n - 1 ∈ Ideal.span {f} := by
    intro n
    obtain ⟨c, hc⟩ := (sub_dvd_pow_sub_pow (s * t) 1 n)
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ ht
  haveI : Algebra.Etale A' (Localization.Away σ) := Algebra.Etale.of_isLocalizationAway σ
  haveI : Algebra.Etale B (Localization.Away σ) := Algebra.Etale.comp B A' (Localization.Away σ)
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x
    obtain ⟨⟨a', m⟩, hx⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) x
    have hxs : x * algebraMap A' (Localization.Away σ) m = algebraMap A' _ a' := by
      rw [← hx]; exact IsLocalization.mk'_spec _ _ _
    obtain ⟨n, hn⟩ := m.2
    rw [← hn] at hxs
    obtain ⟨b, hb⟩ := h2 (a' * algebraMap B A' t ^ n)
    refine ⟨b, ?_⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hpow n)
    have hc' := congrArg (algebraMap A' (Localization.Away σ)) hc
    have hv' := congrArg (algebraMap A' (Localization.Away σ)) (congrArg (algebraMap B A') hv)
    rw [Ideal.mem_span_singleton']
    refine ⟨-(x * algebraMap A' _ (algebraMap B A' v)) + algebraMap A' _ c, ?_⟩
    simp only [IsScalarTower.algebraMap_apply B A' (Localization.Away σ), map_mul, map_sub, map_pow, map_one,
      ← hσ] at hxs hc' hv' ⊢
    linear_combination hc' - x * hv' - (algebraMap A' (Localization.Away σ) (algebraMap B A' t)) ^ n * hxs
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨⟨c, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers σ) y
    have hys := IsLocalization.mk'_spec (Localization.Away σ) c (⟨σ ^ n, n, rfl⟩ : Submonoid.powers σ)
    have key : algebraMap A' (Localization.Away σ) (algebraMap B A' a * σ ^ n) =
        algebraMap A' (Localization.Away σ) (c * algebraMap B A' f) := by
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hy]
      simp only at hys
      rw [← hys]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers σ) _).1 key
    have hmem : algebraMap B A' (s ^ (k + n) * a) ∈ Ideal.span {algebraMap B A' f} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨σ ^ k * c, ?_⟩
      simp only at hk
      rw [map_mul, map_pow, ← hσ, pow_add]
      linear_combination -hk
    have h1 := h3 _ hmem
    have h4 := hpow (k + n)
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 h4
    rw [Ideal.mem_span_singleton']
    refine ⟨t ^ (k + n) * p - a * q, ?_⟩
    linear_combination t ^ (k + n) * hp - a * hq

end GlobalTheory.EtC
end

section

open scoped TensorProduct

namespace GlobalTheory.GoodEtaleFinite

theorem finite_of_trace_relation (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R) :
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  intro hT a ha n x y hrel htf
  set b : R := algebraMap A R a with hb

  have key : ∀ c : C, b • c = ∑ i, T (y i * c) • x i := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i
      rw [Algebra.smul_def, hT, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hrel]
    simp [Algebra.smul_def]
  let S : Submodule R C := Submodule.span R (Set.range x)
  have hmem : ∀ c : C, b • c ∈ S := by
    intro c
    rw [key c]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : C →ₗ[R] S := LinearMap.codRestrict S (b • LinearMap.id) (fun c => by simpa using hmem c)
  have hf : Function.Injective f := by
    intro c d hcd
    have : b • c = b • d := by simpa [f] using congrArg Subtype.val hcd
    have h0 : b • (c - d) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf a ha _ h0)
  haveI : Module.Finite R S := Module.Finite.span_of_finite R (Set.finite_range x)
  haveI : IsNoetherian R S := isNoetherian_of_isNoetherianRing_of_finite R S
  exact Module.Finite.of_injective f hf

end GlobalTheory.GoodEtaleFinite
end

section

open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem etale_localization_of_etaleLow : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := by
  intro A R C O _ _ _ _ _ _ _ Q _ hE hh
  have h := hE (Q.comap (algebraMap R O)) hh
  letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) :=
    (Localization.localRingHom _ Q (algebraMap R O) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply R O (Localization.AtPrime Q)]
  haveI := Algebra.Etale.baseChange (R := Localization.AtPrime (Q.comap (algebraMap R O)))
    (B := Localization.AtPrime Q) (A := Localization.AtPrime (Q.comap (algebraMap R O)) ⊗[R] C)
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange R
    (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) (Localization.AtPrime Q) C)

end GlobalTheory.GoodEtale
end
