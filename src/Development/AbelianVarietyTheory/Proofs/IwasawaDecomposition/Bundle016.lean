module

public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

theorem baseChange_inf_lattice_eq_subspace : ∀ {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V]
    [Module (FractionRing O) V] [Module O V]
    [IsScalarTower O (FractionRing O) V] (N : Submodule O V),
    Submodule.span (FractionRing O) (N : Set V) = ⊤ → ∀ (W : Submodule (FractionRing O) V),
    ∃ e : FractionRing O ⊗[O] ↥(N ⊓ W.restrictScalars O) →ₗ[FractionRing O] V,
      Function.Injective e ∧ LinearMap.range e = W ∧
      ∀ (c : FractionRing O) (x : ↥(N ⊓ W.restrictScalars O)), e (c ⊗ₜ[O] x) = c • (x : V) := by
  intro O V _ _ _ _ _ _ N hN W
  set K := FractionRing O
  have hV : IsBaseChange K (LinearMap.id : V →ₗ[O] V) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).1
      (isLocalizedModule_id (nonZeroDivisors O) V K)
  have hVt : ∀ (c : K) (v : V), hV.equiv (c ⊗ₜ[O] v) = c • v := fun c v => by
    rw [IsBaseChange.equiv_tmul]; rfl

  let fN : K ⊗[O] N →ₗ[K] V := hV.equiv.toLinearMap ∘ₗ N.subtype.baseChange K
  have hfN : ∀ y : N, fN (1 ⊗ₜ y) = y := fun y => by simp [fN, hVt]
  have hinjN : Function.Injective fN := hV.equiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := K) N.subtype N.injective_subtype)
  have hsurjN : Function.Surjective fN := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hN, Submodule.span_le]
    exact fun y hy => ⟨1 ⊗ₜ ⟨y, hy⟩, hfN _⟩
  have hbN : IsBaseChange K N.subtype :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective fN ⟨hinjN, hsurjN⟩) (fun y => hfN y)
  haveI hlN : IsLocalizedModule (nonZeroDivisors O) N.subtype :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K N.subtype).2 hbN

  set N' := N ⊓ W.restrictScalars O
  let e : K ⊗[O] N' →ₗ[K] V := hV.equiv.toLinearMap ∘ₗ N'.subtype.baseChange K
  have het : ∀ (c : K) (x : N'), e (c ⊗ₜ[O] x) = c • (x : V) := fun c x => by
    simp [e, hVt]
  refine ⟨e, hV.equiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := K) N'.subtype N'.injective_subtype), ?_, het⟩
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => rw [het]; exact W.smul_mem c x.2.2
    | add a b ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
  · intro v hv
    obtain ⟨⟨n, d⟩, hd⟩ := IsLocalizedModule.surj (nonZeroDivisors O) N.subtype v
    have hdv : (d : O) • v = (n : V) := hd
    have hdK : (d : O) • v = algebraMap O K d • v := (algebraMap_smul K (d : O) v).symm
    have hW : (n : V) ∈ W := by rw [← hdv, hdK]; exact W.smul_mem _ hv
    have hne : algebraMap O K d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    refine ⟨(algebraMap O K d)⁻¹ ⊗ₜ[O] (⟨n, n.2, hW⟩ : N'), ?_⟩
    rw [het]
    show (algebraMap O K d)⁻¹ • (n : V) = v
    rw [← hdv, hdK, smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory
end

section

open Finset ArithmeticFunction Filter Topology

noncomputable section

namespace GlobalTheory.MangoldtSeries

theorem sum_not_coprime_le (q N : ℕ) (hq : q ≠ 0) :
    ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n ≤ Nat.log 2 N * Real.log q := by
  classical
  set S := (Icc 1 N).filter (fun n => ¬ n.Coprime q) with hS
  set L := Nat.log 2 N with hL
  have hT0 : ∀ p n : ℕ, 0 ≤ (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro p n; split_ifs
    · exact Real.log_natCast_nonneg p
    · exact le_rfl
  have hpt : ∀ n ∈ S, Λ n ≤ ∑ p ∈ q.primeFactors,
      (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hnc⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with hpp
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      have hmin : (p ^ k).minFac = p := by rw [Nat.pow_minFac hk.ne', hp.minFac_eq]
      have hpq : p ∣ q := by
        by_contra h
        exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
      have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, hq⟩
      have hkL : k ∈ Icc 1 L := by
        rw [Finset.mem_Icc]
        refine ⟨hk, Nat.le_log_of_pow_le (by norm_num) ?_⟩
        exact (Nat.pow_le_pow_left hp.two_le k).trans hnN
      have hTp : (if p ^ k ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) = Real.log p :=
        if_pos (Finset.mem_image.2 ⟨k, hkL, rfl⟩)
      rw [hmin, ← hTp]
      exact Finset.single_le_sum (f := fun p' : ℕ => if p ^ k ∈ (Icc 1 L).image (p' ^ ·) then Real.log p' else 0)
        (fun p' _ => hT0 p' (p ^ k)) hpmem
    · exact Finset.sum_nonneg (fun p _ => hT0 p n)
  have hcard : ∀ p : ℕ, ((S ∩ (Icc 1 L).image (p ^ ·)).card : ℝ) ≤ L := by
    intro p
    have h1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := (Icc 1 L).image (p ^ ·)))
    have h2 := Finset.card_image_le (s := Icc 1 L) (f := (p ^ ·))
    have h3 : (Icc 1 L).card = L := by simp
    exact_mod_cast (h1.trans h2).trans h3.le
  calc ∑ n ∈ S, Λ n ≤ ∑ n ∈ S, ∑ p ∈ q.primeFactors,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_le_sum hpt
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ S,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, (L : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p _
        rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcard p) (Real.log_natCast_nonneg p)
    _ = (L : ℝ) * Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [← Finset.mul_sum, Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ (L : ℝ) * Real.log q := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.log_le_log
        · apply Finset.prod_pos
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q))

theorem norm_sub_primitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
      ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤
      Nat.log 2 N * Real.log q := by
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => ¬ n.Coprime q)]
  rw [Finset.sum_eq_zero (s := (Icc 1 N).filter (fun n => ¬¬ n.Coprime q)) ?_, add_zero]
  · calc _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q),
          ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
            ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter] at hn
          have hχ0 : χ (n : ZMod q) = 0 := by
            apply MulChar.map_nonunit
            rw [ZMod.isUnit_iff_coprime]
            exact hn.2
          rw [hχ0, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          calc Λ n * ‖χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ Λ n * 1 :=
                mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
                  ArithmeticFunction.vonMangoldt_nonneg
            _ = Λ n := mul_one _
      _ ≤ _ := sum_not_coprime_le q N (NeZero.ne q)
  · intro n hn
    rw [Finset.mem_filter, not_not] at hn
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn.2)
    push_cast at h
    rw [h, sub_self]

end GlobalTheory.MangoldtSeries
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_integral_dual_family (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] :
    ∃ (k : ℕ) (b : Fin k → 𝓞 M) (l : Fin k → M →ₗ[E] E),
      (∀ j (c : 𝓞 M), ∃ a : 𝓞 E, l j (c : M) = (a : E)) ∧
      ∀ y : M, y = ∑ j, (b j : M) * algebraMap E M (l j y) := by
  haveI : Module.Finite (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.Flat (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (𝓞 M) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (𝓞 M) := Module.Flat.projective_of_finitePresentation
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) (𝓞 M)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  haveI hL : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 M) (nonZeroDivisors (𝓞 E))) M :=
    IsIntegralClosure.isLocalization (𝓞 E) E M (𝓞 M)
  haveI hL' : IsLocalizedModule (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hL
  have hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x
  let l0 : Fin k → M →ₗ[𝓞 E] E := fun j =>
    IsLocalizedModule.lift (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu
  let l : Fin k → M →ₗ[E] E := fun j =>
    (l0 j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E
  have hl : ∀ j (c : 𝓞 M), l j (c : M) = ((σ c j : 𝓞 E) : E) := by
    intro j c
    exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu c
  refine ⟨k, fun j => π (Pi.single j 1), l, fun j c => ⟨_, hl j c⟩, ?_⟩
  have hc : ∀ c : 𝓞 M, (c : M) = ∑ j, ((π (Pi.single j 1) : 𝓞 M) : M) * algebraMap E M (l j c) := by
    intro c
    have h1 : c = ∑ j, σ c j • π (Pi.single j 1) := by
      have h2 : π (σ c) = c := LinearMap.congr_fun hσ c
      conv_lhs => rw [← h2, LinearMap.pi_apply_eq_sum_univ π (σ c)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ext i
      simp [Pi.single_apply, eq_comm]
    have h3 := congrArg (algebraMap (𝓞 M) M) h1

    rw [map_sum] at h3
    refine h3.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [hl, Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply]
    rfl
  intro y
  obtain ⟨⟨c, a⟩, ha⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap y
  have ha' : ((a : 𝓞 E) : E) • y = (c : M) := by
    have : (a : 𝓞 E) • y = (c : M) := ha
    rw [← this]
    exact algebraMap_smul E (a : 𝓞 E) y
  have hne : ((a : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero a.2
    exact_mod_cast this
  have h4 := hc c
  rw [← ha'] at h4
  apply smul_right_injective M hne
  dsimp only
  rw [h4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
  ring

theorem comap_single_span_algebraMap (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι) :
    (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap
      (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) =
    Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap
      (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  apply le_antisymm
  · obtain ⟨k, b, l, hl, hy⟩ := exists_integral_dual_family E M
    have key : ∀ j, ∀ w ∈ Submodule.span (𝓞 M)
        ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S), ∀ c : 𝓞 M,
        (fun i => l j ((c : M) * w i)) ∈ Submodule.span (𝓞 E) S := by
      intro j w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        intro c
        obtain ⟨a, ha⟩ := hl j c
        have : (fun i => l j ((c : M) * algebraMap E M (v i))) = a • v := by
          ext i
          rw [mul_comm, ← Algebra.smul_def, map_smul, ha, smul_eq_mul, mul_comm]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
      | zero =>
        intro c
        have : (fun i => l j ((c : M) * (0 : ι → M) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        intro c
        have : (fun i => l j ((c : M) * (x + y) i)) =
            (fun i => l j ((c : M) * x i)) + (fun i => l j ((c : M) * y i)) := by
          ext i; simp [mul_add]
        rw [this]; exact Submodule.add_mem _ (hx c) (hy c)
      | smul a x _ hx =>
        intro c
        have : (fun i => l j ((c : M) * (a • x) i)) =
            (fun i => l j (((c * a : 𝓞 M) : M) * x i)) := by
          ext i
          congr 1
          rw [Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
          simp
        rw [this]; exact hx _
    intro s hs
    rw [hy s]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 : ((b j : 𝓞 M) : M) * algebraMap E M (l j s) = b j • algebraMap E M (l j s) := rfl
    rw [h1]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨l j s, ?_, rfl⟩)
    have h2 := key j _ hs 1
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have key : ∀ v ∈ Submodule.span (𝓞 E) S, (fun i => algebraMap E M (v i)) ∈
        Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have : (fun i => algebraMap E M ((0 : ι → E) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have : (fun i => algebraMap E M ((x + y) i)) =
            (fun i => algebraMap E M (x i)) + (fun i => algebraMap E M (y i)) := by
          ext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        have : (fun i => algebraMap E M ((a • x) i)) =
            algebraMap (𝓞 E) (𝓞 M) a • (fun i => algebraMap E M (x i)) := by
          ext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
            ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have h2 := key _ hs
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]

end GlobalTheory
end

section

namespace GlobalTheory.RatCoordsAdjoin

theorem exists_rat_add_mul_of_mem_adjoin {E : Type} [Field E] [NumberField E] (d : ℕ) (s : E)
    (hs : s ^ 2 = -(d : E)) {x : E} (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) :
    ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  have halg : IsAlgebraic ℚ s := Algebra.IsAlgebraic.isAlgebraic s
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := ℚ) (S := ({s} : Set E))
      (by intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact halg)]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a * c - b * e * d, a * e + b * c, by
      push_cast; linear_combination ((b : E) * (e : E)) * hs⟩

end GlobalTheory.RatCoordsAdjoin
end

section

namespace GlobalTheory.NatSmulMemIntegral

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ b : RingOfIntegers E, (b : E) = (k : E) * a := by

  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have hi : IsIntegral ℤ (y • a) := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with hpos | hneg
  · refine ⟨⟨y • a, hi⟩, ?_⟩
    change y • a = _
    rw [zsmul_eq_mul]
    congr 1
    rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]
  · refine ⟨-⟨y • a, hi⟩, ?_⟩
    change -(y • a) = _
    rw [zsmul_eq_mul, ← neg_mul]
    congr 1
    rw [Nat.cast_natAbs, abs_of_nonpos (by omega), Int.cast_neg]

theorem exists_nat_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : E) • y ∈ Λ := by
  have hy : y ∈ Submodule.span E (↑Λ : Set (Fin n → E)) := by rw [h]; exact Submodule.mem_top
  simp only [Nat.cast_smul_eq_nsmul]
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hz
    refine ⟨m₂ * m₁, mul_ne_zero hm₂ hm₁, ?_⟩
    have ex : (m₂ * m₁) • x = m₂ • (m₁ • x) := by rw [mul_smul]
    have ez : (m₂ * m₁) • z = m₁ • (m₂ • z) := by rw [mul_comm, mul_smul]
    rw [smul_add, ex, ez]
    exact Λ.add_mem (Λ.nsmul_mem h₁ m₂) (Λ.nsmul_mem h₂ m₁)
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨k, hk, b, hb⟩ := exists_nat_mul_integral c
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have hbx : b • (m • x) ∈ Λ := Λ.smul_mem b hmx
    convert hbx using 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [Algebra.smul_def, show (algebraMap (RingOfIntegers E) E b) = (b : E) from rfl, hb]
    simp only [Pi.mul_apply, Pi.natCast_apply, Nat.cast_mul]
    ring

end GlobalTheory.NatSmulMemIntegral
end
