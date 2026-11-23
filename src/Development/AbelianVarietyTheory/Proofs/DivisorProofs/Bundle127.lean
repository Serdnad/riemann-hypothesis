module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.RingHom.Flat
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
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.GroupTheory.Index

@[expose] public section

section

open TensorProduct LinearMap

namespace GlobalTheory

theorem flat_of_forall_finset_subset_flat :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M],
      (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) →
        Module.Flat R M := by
  intro R M _ _ _ h
  refine Module.Flat.iff_lTensor_injective'.mpr fun I => ?_
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨J, hfg, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype (R := R) (M := ↥I) x
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨N, hsN, hN⟩ := h s
  have hJN : J ≤ N := hs ▸ Submodule.span_le.mpr hsN
  obtain ⟨y', hy'⟩ : ∃ y' : ↥N ⊗[R] ↥I, y' = rTensor (↥I) (Submodule.inclusion hJN) y := ⟨_, rfl⟩
  have hxy : rTensor (↥I) J.subtype y = rTensor (↥I) N.subtype y' := by
    rw [hy', ← rTensor_comp_apply]; rfl
  rw [hxy] at hx ⊢
  have hcomm : lTensor M I.subtype (rTensor (↥I) N.subtype y') =
      rTensor R N.subtype (lTensor (↥N) I.subtype y') := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, lTensor_comp_rTensor, rTensor_comp_lTensor]
  rw [hcomm] at hx
  have hinj1 : Function.Injective (rTensor R N.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) N.subtype Subtype.val_injective
  have h0 : lTensor (↥N) I.subtype y' = 0 := hinj1 (by rw [hx, map_zero])
  have hinj2 : Function.Injective (lTensor (↥N) I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := ↥N) I.subtype Subtype.val_injective
  have : y' = 0 := hinj2 (by rw [h0, map_zero])
  rw [this, map_zero]

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem subsingleton_of_lTensor_flat_family (R : Type) [CommRing R] (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (hflat : ∀ i, Module.Flat R (B i))
    (hmax : ∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤)
    (M : Type) [AddCommGroup M] [Module R M] (h : ∀ i, Subsingleton (B i ⊗[R] M)) :
    Subsingleton M := by
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  set g : R →ₗ[R] M := LinearMap.toSpanSingleton R M x with hg
  set I : Ideal R := LinearMap.ker g with hIdef
  have hI : I ≠ ⊤ := by
    intro hT
    have h1 : (1 : R) ∈ I := hT ▸ Submodule.mem_top
    rw [hIdef, LinearMap.mem_ker, hg, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hx h1
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  obtain ⟨i, hi⟩ := hmax m hm
  let e : (R ⧸ I) →ₗ[R] M := (LinearMap.ker g).liftQ g le_rfl
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hinj : Function.Injective (e.lTensor (B i)) :=
    Module.Flat.lTensor_preserves_injective_linearMap e he
  haveI := h i
  haveI : Subsingleton (B i ⊗[R] (R ⧸ I)) := hinj.subsingleton
  haveI : Subsingleton ((R ⧸ I) ⊗[R] B i) := (TensorProduct.comm R (R ⧸ I) (B i)).toEquiv.injective.subsingleton
  haveI : Subsingleton (B i ⧸ (I • (⊤ : Submodule R (B i)))) :=
    (TensorProduct.quotTensorEquivQuotSMul (B i) I).symm.toEquiv.injective.subsingleton
  have htop : I • (⊤ : Submodule R (B i)) = ⊤ :=
    Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop
  exact hi (top_le_iff.mp (htop ▸ Ideal.map_mono hIm))

theorem bijective_of_lTensor_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) →
    (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) →
    (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  intro R _ N N' _ _ _ _ f J B _ _ hflat hmax hbij
  constructor
  · set K := LinearMap.ker f
    have hK : ∀ i, Subsingleton (B i ⊗[R] K) := by
      intro i
      have hinjK : Function.Injective (K.subtype.lTensor (B i)) :=
        Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.injective_subtype
      have hz : (f.lTensor (B i)).comp (K.subtype.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : f ∘ₗ K.subtype = 0 := by
          ext x
          exact LinearMap.mem_ker.mp x.2
        rw [this, LinearMap.lTensor_zero]
      refine ⟨fun a b => hinjK ((hbij i).1 ?_)⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax K hK
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  · set q := (LinearMap.range f).mkQ
    have hQ : ∀ i, Subsingleton (B i ⊗[R] (N' ⧸ LinearMap.range f)) := by
      intro i
      have hsurj : Function.Surjective (q.lTensor (B i)) :=
        LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective _)
      have hz : (q.lTensor (B i)).comp (f.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : q ∘ₗ f = 0 := by
          ext x
          simp [q]
        rw [this, LinearMap.lTensor_zero]
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨z, rfl⟩ := hsurj y
      obtain ⟨w, rfl⟩ := (hbij i).2 z
      rw [← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax _ hQ
    have htop : LinearMap.range f = ⊤ :=
      Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
    exact LinearMap.range_eq_top.mp htop

end GlobalTheory
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem flat_one_tmul_eq_zero_mem_map (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P) :
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  intro hI y hy
  subst hI
  set K := RingHom.ker (algebraMap P T)
  let f : (P ⧸ K) →ₗ[P] T := (Ideal.Quotient.liftₐ K (Algebra.ofId P T) (fun a ha => RingHom.mem_ker.mp ha)).toLinearMap
  have hf : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa [f] using hab
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := L) f hf
  have h0 : (1 : P ⧸ K) ⊗ₜ[P] y = 0 := by
    apply hinj
    rw [LinearMap.rTensor_tmul, map_zero]
    simpa [f] using hy
  have h1 := congrArg (TensorProduct.quotTensorEquivQuotSMul L K) h0
  rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Ideal.smul_top_eq_map] at h1
  exact h1

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem exists_fin_sum_of_mem_ideal_smul_top {B P : Type} [CommRing B] [AddCommGroup P]
    [Module B P] (I : Ideal B) {z : P} (hz : z ∈ I • (⊤ : Submodule B P)) :
    ∃ (n : ℕ) (b : Fin n → B) (p : Fin n → P), (∀ i, b i ∈ I) ∧ ∑ i, b i • p i = z := by
  refine Submodule.smul_induction_on hz
    (fun r hr m _ => ⟨1, fun _ => r, fun _ => m, fun _ => hr, by simp⟩) ?_
  rintro x y ⟨n, b, p, hb, rfl⟩ ⟨n', b', p', hb', rfl⟩
  refine ⟨n + n', Fin.append b b', Fin.append p p', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hb, hb']
  · simp [Fin.sum_univ_add]

theorem ker_inf_map_le_map_mul_ker_of_flat :
    ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A]
      [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B,
      RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  intro B P A _ _ _ _ _ _ Ψ hΨ I z hz
  have hz1 : Ψ z = 0 := RingHom.mem_ker.1 hz.1
  have hz2 : z ∈ I • (⊤ : Submodule B P) := by
    rw [Ideal.smul_top_eq_map]; exact hz.2
  obtain ⟨n, b, p, hb, rfl⟩ := exists_fin_sum_of_mem_ideal_smul_top I hz2
  have h0 : ∑ i, b i • Ψ (p i) = 0 := by

    simpa [map_sum, map_smul] using hz1
  obtain ⟨k, c, a, hx, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := B) (M := A)
    (f := b) (x := fun i => Ψ (p i)) h0
  choose q hq using fun j => hΨ (a j)
  have hzero : ∑ i, ∑ j, (b i * c i j) • q j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul, hc j, zero_smul]
  have key : ∑ i, b i • p i = ∑ i, b i • (p i - ∑ j, c i j • q j) := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, hzero, sub_zero]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hb i)) ?_
  rw [RingHom.mem_ker]

  simp only [map_sub, map_sum, map_smul, hq, ← hx i, sub_self]

end GlobalTheory
end

section

namespace GlobalTheory

open IsLocalization in
theorem localFlat_dvd_descends : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ Q _ f b h
  set P : Ideal B := Q.comap (algebraMap B D) with hP
  let φ : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (algebraMap B D) rfl
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := φ.toAlgebra
  have hφ : ∀ x : B, φ (algebraMap B (Localization.AtPrime P) x) = algebraMap B (Localization.AtPrime Q) x := by
    intro x
    simp [φ, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
  have hfl : φ.Flat := RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) Q P rfl
  haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime Q) := hfl
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) :=
    (inferInstance : IsLocalHom φ)
  haveI : Module.FaithfullyFlat (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have key : algebraMap B (Localization.AtPrime P) b ∈
      (Ideal.span {f}).map (algebraMap B (Localization.AtPrime P)) := by
    rw [Ideal.map_span, Set.image_singleton,
      ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Localization.AtPrime Q)
        (Ideal.span {algebraMap B (Localization.AtPrime P) f}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton]
    change φ _ ∈ Ideal.span {φ _}
    rw [hφ, hφ]; exact h
  obtain ⟨s, hs, h2⟩ := (algebraMap_mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P) _ b).1 key
  exact ⟨s, hs, h2⟩

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory.ValuativeQuotient

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem main : ∀ (V K B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing B] [Algebra V B] (JK : Ideal (K ⊗[V] B)),
    ∃! J : Ideal B, Module.Flat V (B ⧸ J) ∧
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) = JK := by
  intro V K B _ _ _ _ _ _ _ _ JK
  have hloc := IsLocalization.tensorRight (S := B) K (nonZeroDivisors V)
  set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors V) with hM
  have hmap : ∀ I : Ideal B,
      I.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) =
        I.map (algebraMap B (K ⊗[V] B)) := fun I => rfl
  have hsmul : ∀ (J : Ideal B) (v : V) (b : B),
      v • Ideal.Quotient.mk J b = Ideal.Quotient.mk J (algebraMap V B v * b) := by
    intro J v b
    rw [← Algebra.smul_def, ← Ideal.Quotient.mkₐ_eq_mk V, map_smul]
  have hflat : ∀ J : Ideal B, Module.Flat V (B ⧸ J) ↔ ∀ m ∈ M, ∀ b : B, m * b ∈ J → b ∈ J := by
    intro J
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
    constructor
    · rintro h m ⟨v, hv, rfl⟩ b hb
      have h0 := h (Ideal.Quotient.mk J b) ((Submodule.mem_torsion_iff _).mpr
        ⟨⟨v, hv⟩, by
          show v • Ideal.Quotient.mk J b = 0
          rw [hsmul, Ideal.Quotient.eq_zero_iff_mem]
          exact hb⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    · intro h x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨⟨v, hv⟩, hvb⟩ := (Submodule.mem_torsion_iff _).mp hx
      change v • Ideal.Quotient.mk J b = 0 at hvb
      rw [hsmul, Ideal.Quotient.eq_zero_iff_mem] at hvb
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h _ ⟨v, hv, rfl⟩ b hvb)
  refine ⟨JK.comap (algebraMap B (K ⊗[V] B)), ⟨?_, ?_⟩, ?_⟩
  · rw [hflat]
    intro m hm b hb
    rw [Ideal.mem_comap, map_mul] at hb
    exact (Ideal.unit_mul_mem_iff_mem JK (IsLocalization.map_units (K ⊗[V] B) ⟨m, hm⟩)).mp hb
  · rw [hmap]
    exact IsLocalization.map_under M (K ⊗[V] B) JK
  · rintro J' ⟨hJ'f, hJ'⟩
    rw [hmap] at hJ'
    rw [hflat] at hJ'f
    apply le_antisymm
    · rw [← hJ']
      exact Ideal.le_comap_map
    · intro b hb
      rw [Ideal.mem_comap, ← hJ', IsLocalization.mem_map_algebraMap_iff M] at hb
      obtain ⟨⟨x, m⟩, hxm⟩ := hb
      rw [← map_mul, IsLocalization.eq_iff_exists M] at hxm
      obtain ⟨c, hc⟩ := hxm
      apply hJ'f (c * m) (M.mul_mem c.2 m.2)
      have : (c : B) * (m : B) * b = c * x.1 := by rw [← hc]; ring
      rw [this]
      exact J'.mul_mem_left _ x.2

end GlobalTheory.ValuativeQuotient
end

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem unit_splits_of_projective_faithfullyFlat :
    ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  intro R D _ _ _ _ hP hF
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hP
  let ev : (D →ₗ[R] R) →ₗ[R] R :=
    { toFun := fun τ => τ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  by_cases hI : LinearMap.range ev = ⊤
  · obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp (hI ▸ Submodule.mem_top : (1 : R) ∈ LinearMap.range ev)
    exact ⟨τ, hτ⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal (LinearMap.range ev) hI
  exfalso
  have hcoord : ∀ x : D, s 1 x ∈ m := fun x =>
    hIm (LinearMap.mem_range.mpr ⟨Finsupp.lapply x ∘ₗ s, rfl⟩)
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by
    have : Finsupp.linearCombination R id (s 1) = (1 : D) := LinearMap.congr_fun hs 1
    rw [← this, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem_smul (hcoord x) Submodule.mem_top
  have hmul : ∀ d : D, ∀ y ∈ m • (⊤ : Submodule R D), d * y ∈ m • (⊤ : Submodule R D) := by
    intro d y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x z hx hz
      rw [mul_add]; exact Submodule.add_mem _ hx hz
  apply Module.FaithfullyFlat.submodule_ne_top (M := D) hm
  rw [eq_top_iff]
  intro d _
  simpa using hmul d 1 h1

end GlobalTheory
end

section

open IsDedekindDomain Polynomial

namespace GlobalTheory

theorem hensel_norm_lift_of_involution :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (τ : A →+* A), (∀ a, τ (τ a) = a) → IsUnit (2 : A) → (∀ a ∈ I, τ a ∈ I) → ∀ a t₀ : A, IsUnit a → τ a = a → IsUnit t₀ → t₀ * τ t₀ - a ∈ I → ∃ t : A, IsUnit t ∧ t * τ t = a := by
  intro A _ I _ τ hτ h2 hI a t₀ ha hτa ht₀ hclose
  set c := t₀ * τ t₀ with hc_def
  have hc : IsUnit c := ht₀.mul (ht₀.map τ)
  have hτc : τ c = c := by
    simp only [hc_def, map_mul, hτ]; ring
  obtain ⟨w, hw⟩ := hc.exists_right_inv
  have hτw : τ w = w := by
    apply hc.mul_left_cancel
    rw [hw, ← hτc, ← map_mul, hw, map_one]
  set b := a * w with hb_def
  have hτb : τ b = b := by simp only [hb_def, map_mul, hτa, hτw]
  have hb1 : 1 - b ∈ I := by
    have : 1 - b = w * (c - a) := by
      rw [hb_def]; linear_combination (-1 : A) * hw
    rw [this]; exact I.mul_mem_left w hclose
  obtain ⟨s, hs, hs1⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - C b)
    (monic_X_pow_sub_C b (by norm_num)) 1 (by simpa using hb1)
    (by
      have : (derivative (X ^ 2 - C b)).eval (1 : A) = 2 := by simp [one_add_one_eq_two]
      rw [this]; exact h2.map _)
  have hs2 : s ^ 2 = b := by
    have := hs.eq_zero; simp at this; linear_combination this
  have hτs2 : τ s ^ 2 = b := by rw [← map_pow, hs2, hτb]
  have hτs1 : τ s - 1 ∈ I := by
    have := hI _ hs1; simpa using this
  have hsum : IsUnit (s + τ s) := by
    have hj : (s - 1) + (τ s - 1) ∈ Ideal.jacobson (⊥ : Ideal A) :=
      by simpa only [Ideal.jacobson_bot] using HenselianRing.jac (Ideal.add_mem I hs1 hτs1)
    obtain ⟨v, hv⟩ := h2.exists_right_inv
    have hu := (Ideal.mem_jacobson_bot.1 hj) v
    have : s + τ s = (((s - 1) + (τ s - 1)) * v + 1) * 2 := by
      linear_combination (-(s - 1 + (τ s - 1))) * hv
    rw [this]; exact hu.mul h2
  have hfix : τ s = s := by
    have h0 : (s - τ s) * (s + τ s) = 0 := by linear_combination hs2 - hτs2
    have := (hsum.mul_left_eq_zero).1 h0
    linear_combination -this
  have hbu : IsUnit b := ha.mul (IsUnit.of_mul_eq_one_right c hw)
  have hsu : IsUnit s := by
    rw [← hs2, pow_two] at hbu; exact isUnit_of_mul_isUnit_left hbu
  refine ⟨t₀ * s, ht₀.mul hsu, ?_⟩
  rw [map_mul, hfix]
  have : t₀ * s * (τ t₀ * s) = c * s ^ 2 := by rw [hc_def]; ring
  rw [this, hs2, hb_def]
  linear_combination a * hw

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

def killedBy {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) :
    AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha, neg_zero]

theorem card_eq_card_ker_mul_card_range {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

end GlobalTheory
end
