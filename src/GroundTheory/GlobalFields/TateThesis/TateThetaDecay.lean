module

public import GroundTheory.GlobalFields.TateThesis.TateTheta
import GroundTheory.GlobalFields.TateThesis.AdelePoisson
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import GroundTheory.GlobalFields.TateThesis.LatticePoissonBasic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem coe_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    ((moduleSection w t : IdeleGroup K) : 𝔸[K]) = (infiniteAdeleSingle w (posRealElem w t), 1) :=
  coe_infiniteEmbedding w _

theorem toFinite_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    toFinite K (moduleSection w t) = 1 := by
  refine Units.ext ?_
  rw [Units.val_one]
  change ((moduleSection w t : IdeleGroup K) : 𝔸[K]).2 = 1
  rw [coe_moduleSection]

theorem norm_moduleSection_apply (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) (v : InfinitePlace K) :
    ‖((moduleSection w t : IdeleGroup K) : 𝔸[K]).1 v‖ = if v = w then ‖posRealElem w t‖ else 1 := by
  rw [coe_moduleSection]
  change ‖infiniteAdeleSingle w (posRealElem w t) v‖ = _
  rw [infiniteAdeleSingle_apply]
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, norm_one]

theorem infiniteModule_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    infiniteModule (moduleSection w t) = t := by
  rw [infiniteModule, Finset.prod_eq_single w (fun v _ hv ↦ by
    rw [norm_moduleSection_apply, if_neg hv, one_pow]) (fun h ↦ absurd (Finset.mem_univ w) h),
    norm_moduleSection_apply, if_pos rfl]
  exact norm_posRealElem_pow w t.2.le

theorem norm_moduleSection_apply_le_one (w : InfinitePlace K) {t : {r : ℝ // 0 < r}}
    (ht : (t : ℝ) ≤ 1) (v : InfinitePlace K) :
    ‖((moduleSection w t : IdeleGroup K) : 𝔸[K]).1 v‖ ≤ 1 := by
  rw [norm_moduleSection_apply]
  split_ifs
  · have h := norm_posRealElem_pow w t.2.le
    have hm : w.mult ≠ 0 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
    have h2 : ‖posRealElem w t‖ ^ w.mult ≤ 1 := by rw [h]; exact ht
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm).1 h2
  · exact le_rfl

theorem normAtPlace_le_norm' (v : InfinitePlace K) (z : mixedSpace K) : normAtPlace v z ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun v ↦ normAtPlace v z) (Finset.mem_univ v)

theorem mixedEmbedding_norm_le_norm_pow (z : mixedSpace K) :
    mixedEmbedding.norm z ≤ ‖z‖ ^ Module.finrank ℚ K := by
  rw [mixedEmbedding.norm_apply, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (normAtPlace_nonneg _ _) _)
    fun v _ ↦ pow_le_pow_left₀ (normAtPlace_nonneg _ _) (normAtPlace_le_norm' v z) _

theorem norm_mul_le_of_normAtPlace_le_one {e : mixedSpace K} (he : ∀ v, normAtPlace v e ≤ 1)
    (z : mixedSpace K) : ‖e * z‖ ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace (e * z)]
  refine Finset.sup'_le _ _ fun v _ ↦ ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left (normAtPlace_nonneg _ _) (he v)).trans (normAtPlace_le_norm' v z)

theorem mixedEmbedding_norm_toInfinite (x : IdeleGroup K) :
    mixedEmbedding.norm (homeomorphMixedSpace K
      ((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) = infiniteModule x := by
  rw [mixedEmbedding.norm_apply]
  simp only [normAtPlace_homeomorphMixedSpace]
  rfl

theorem one_le_abs_norm_of_ne_zero {r : 𝓞 K} (hr : r ≠ 0) :
    (1 : ℝ) ≤ |((Algebra.norm ℚ (r : K) : ℚ) : ℝ)| := by
  rw [← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.2 hr
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ r| := Int.one_le_abs h
  exact_mod_cast h1

theorem exists_summable_majorant_moduleSection (w : InfinitePlace K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) (d : 𝓞 K) (hd : d ≠ 0) (r : ℕ) :
    ∃ (k : ℕ) (u : K → ℝ), Summable u ∧ (∀ ξ, 0 ≤ u ξ) ∧ ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x},
      1 ≤ (t : ℝ) → ∀ ξ : K, ξ ≠ 0 → (∃ s : 𝓞 K, (d : K) * ξ = s) →
      ((1 + ‖homeomorphMixedSpace K ((moduleSection w t * a) • algebraMap K 𝔸[K] ξ).1‖) ^ k)⁻¹
        ≤ ((t : ℝ) ^ r)⁻¹ * u ξ := by
  set dK : K := (d : K) with hdKdef
  have hdK : dK ≠ 0 := by
    intro h
    apply hd
    have h' : ((d : K)) = 0 := h
    exact_mod_cast h'
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK))
  have hJ : ∀ ξ : K, (∃ s : 𝓞 K, dK * ξ = s) → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rintro ξ ⟨s, hs⟩
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨s, ?_⟩
    rw [Algebra.smul_def]
    change (s : K) * dK⁻¹ = ξ
    rw [← hs, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]
  have hNd : ((Algebra.norm ℚ dK : ℚ) : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 hdK
  set κ₀ : ℝ := |((Algebra.norm ℚ dK : ℚ) : ℝ)|⁻¹
  have hκ₀ : 0 < κ₀ := inv_pos.2 (abs_pos.2 hNd)
  have hNξ : ∀ ξ : K, ξ ≠ 0 → (∃ s : 𝓞 K, dK * ξ = s) →
      κ₀ ≤ mixedEmbedding.norm (mixedEmbedding K ξ) := by
    rintro ξ hξ0 ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hξ0
      have h0 : dK * ξ = 0 := by rw [hs]; simp
      exact (mul_eq_zero.1 h0).resolve_left hdK
    have hmul : Algebra.norm ℚ dK * Algebra.norm ℚ ξ = Algebra.norm ℚ (s : K) := by
      rw [← map_mul, hs]
    have hξN : ((Algebra.norm ℚ ξ : ℚ) : ℝ) =
        ((Algebra.norm ℚ (s : K) : ℚ) : ℝ) * ((Algebra.norm ℚ dK : ℚ) : ℝ)⁻¹ := by
      rw [← hmul, Rat.cast_mul]
      field_simp
    rw [mixedEmbedding.norm_eq_norm, Rat.cast_abs, hξN, abs_mul, abs_inv]
    exact le_mul_of_one_le_left (by positivity) (one_le_abs_norm_of_ne_zero hs0)
  have hcm : Continuous fun a : IdeleGroup K ↦ (infiniteModule a)⁻¹ :=
    continuous_infiniteModule.inv₀ fun a ↦ (infiniteModule_pos a).ne'
  obtain ⟨B₂, hB₂⟩ := hC.exists_bound_of_continuousOn hcm.continuousOn
  set m : ℝ := (max B₂ 1)⁻¹
  have hm0 : 0 < m := inv_pos.2 (zero_lt_one.trans_le (le_max_right _ _))
  have hmC : ∀ a ∈ C, m ≤ infiniteModule a := by
    intro a ha
    have h1 : (infiniteModule a)⁻¹ ≤ max B₂ 1 := by
      have := hB₂ a ha
      rw [Real.norm_of_nonneg (inv_nonneg.2 (infiniteModule_pos a).le)] at this
      exact this.trans (le_max_left _ _)
    exact inv_le_of_inv_le₀ (infiniteModule_pos a) h1
  set kL := Module.finrank ℤ (idealLattice K J) + 1
  set n := Module.finrank ℚ K
  have hcont : Continuous fun a : IdeleGroup K ↦ ‖homeomorphMixedSpace K
      ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ :=
    continuous_norm.comp ((homeomorphMixedSpace K).continuous.comp (Units.continuous_val.comp
      ((IdeleGroup.continuous_toInfinite (K := K)).comp continuous_inv)))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  set κ := m * κ₀
  have hκ : 0 < κ := mul_pos hm0 hκ₀
  refine ⟨kL + n * r, fun ξ ↦ if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then
      B' ^ kL * (κ ^ r)⁻¹ * ((1 + ‖mixedEmbedding K ξ‖) ^ kL)⁻¹ else 0, ?_, ?_, ?_⟩
  · exact summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ B' ^ kL * (κ ^ r)⁻¹ * ((1 + ‖x‖) ^ kL)⁻¹)
      ((summable_inv_one_add_norm_pow_idealLattice J).mul_left (B' ^ kL * (κ ^ r)⁻¹))
  · intro ξ
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  intro a ha t ht ξ hξ0 hξs
  have hξJ := hJ ξ hξs
  set y := moduleSection w t * a
  set c := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K y : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  set c' := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  set e' := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K (moduleSection w t⁻¹) : (InfiniteAdeleRing K)ˣ) :
      InfiniteAdeleRing K)
  have hcc : c' * (e' * c) = 1 := by
    rw [← homeomorphMixedSpace_mul, ← homeomorphMixedSpace_mul, ← Units.val_mul, ← Units.val_mul,
      ← map_mul, ← map_mul, map_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel_right, inv_mul_cancel,
      map_one, Units.val_one, homeomorphMixedSpace_apply, map_one]
  have he' : ∀ v, normAtPlace v e' ≤ 1 := by
    intro v
    rw [normAtPlace_homeomorphMixedSpace]
    refine norm_moduleSection_apply_le_one w ?_ v
    change (t : ℝ)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ ht
  have hz_eq : homeomorphMixedSpace K ((y • algebraMap K 𝔸[K] ξ).1) =
      c * mixedEmbedding K ξ := by
    have h1 : (y • algebraMap K 𝔸[K] ξ).1 =
        ((IdeleGroup.toInfinite K y : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) *
          algebraMap K (InfiniteAdeleRing K) ξ := rfl
    rw [h1, homeomorphMixedSpace_mul, homeomorphMixedSpace_algebraMap]
  rw [hz_eq]
  dsimp only
  rw [if_pos hξJ]
  set x := mixedEmbedding K ξ
  set z := c * x
  have hx : ‖x‖ ≤ B' * ‖z‖ := by
    calc ‖x‖ = ‖c' * (e' * z)‖ := by rw [← mul_assoc, ← mul_assoc, mul_assoc c', hcc, one_mul]
      _ ≤ ‖c'‖ * ‖e' * z‖ := norm_mul_le _ _
      _ ≤ B' * ‖z‖ :=
        mul_le_mul (((norm_norm _).symm.trans_le (hB a ha)).trans (le_max_left _ _))
          (norm_mul_le_of_normAtPlace_le_one he' z) (norm_nonneg _) hB'0.le
  have hN : (t : ℝ) * κ ≤ mixedEmbedding.norm z := by
    rw [map_mul, mixedEmbedding_norm_toInfinite, infiniteModule_mul,
      infiniteModule_moduleSection]
    have h1 := hmC a ha
    have h2 := hNξ ξ hξ0 hξs
    have ht0 : (0 : ℝ) ≤ t := t.2.le
    calc (t : ℝ) * κ = (t : ℝ) * m * κ₀ := by rw [mul_assoc]
      _ ≤ (t : ℝ) * infiniteModule a * mixedEmbedding.norm x :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 ht0) h2 hκ₀.le
          (mul_nonneg ht0 (infiniteModule_pos a).le)
  have htκ : 0 < (t : ℝ) * κ := mul_pos t.2 hκ
  have hz : (t : ℝ) * κ ≤ (1 + ‖z‖) ^ n :=
    hN.trans ((mixedEmbedding_norm_le_norm_pow z).trans
      (pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg z]) n))
  have hx' : (1 + ‖x‖) / B' ≤ 1 + ‖z‖ := by
    rw [div_le_iff₀ hB'0]
    nlinarith [norm_nonneg z]
  have h1 : ((1 + ‖z‖) ^ kL)⁻¹ ≤ (((1 + ‖x‖) / B') ^ kL)⁻¹ :=
    inv_anti₀ (pow_pos (div_pos (by positivity) hB'0) kL)
      (pow_le_pow_left₀ (div_pos (by positivity) hB'0).le hx' kL)
  have h2 : (((1 + ‖z‖) ^ n) ^ r)⁻¹ ≤ (((t : ℝ) * κ) ^ r)⁻¹ :=
    inv_anti₀ (pow_pos htκ r) (pow_le_pow_left₀ htκ.le hz r)
  calc ((1 + ‖z‖) ^ (kL + n * r))⁻¹ = ((1 + ‖z‖) ^ kL)⁻¹ * (((1 + ‖z‖) ^ n) ^ r)⁻¹ := by
        rw [pow_add, pow_mul, mul_inv]
    _ ≤ (((1 + ‖x‖) / B') ^ kL)⁻¹ * (((t : ℝ) * κ) ^ r)⁻¹ :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = ((t : ℝ) ^ r)⁻¹ * (B' ^ kL * (κ ^ r)⁻¹ * ((1 + ‖x‖) ^ kL)⁻¹) := by
        rw [div_pow, inv_div, mul_pow, mul_inv]
        ring

theorem exists_decay_bound_tensor_cosetIndicator (w : InfinitePlace K) (φ : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]) {C : Set (IdeleGroup K)} (hC : IsCompact C)
    (r : ℕ) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) → ∀ ξ : K, ξ ≠ 0 →
      ‖schwartzBruhatTensor φ (cosetIndicator I b)
        ((moduleSection w t * a) • algebraMap K 𝔸[K] ξ)‖ ≤ ((t : ℝ) ^ r)⁻¹ * u ξ := by

  set S : Set 𝔸ᶠ[K] := (fun p : IdeleGroup K × 𝔸ᶠ[K] ↦
      ((IdeleGroup.toFinite K p.1⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * p.2) ''
    (C ×ˢ (b +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])))
  have hS : IsCompact S := (hC.prod ((isCompact_idealFiniteAdeles I).vadd b)).image
    ((Units.continuous_val.comp ((IdeleGroup.continuous_toFinite (K := K)).comp
      (continuous_inv.comp continuous_fst))).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  have hdenom : ∀ a ∈ C, ∀ ξ : K,
      ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈
        idealFiniteAdeles I → ∃ s : 𝓞 K, (d : K) * ξ = s := by
    intro a ha ξ hξ
    have hmem : algebraMap K 𝔸ᶠ[K] ξ ∈ S := by
      refine ⟨(a, ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ),
        ⟨ha, mem_vadd_idealFiniteAdeles.mpr hξ⟩, ?_⟩
      simp only [map_inv, Units.inv_mul_cancel_left]
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : (d : K) * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    exact ⟨r, hr.symm⟩
  obtain ⟨k, u, hu, hu0, hbound⟩ := exists_summable_majorant_moduleSection w hC d hd0 r
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ k
  refine ⟨fun ξ => A * u ξ, hu.mul_left A, fun a ha t ht ξ hξ => ?_⟩
  let y := moduleSection w t * a
  let z := homeomorphMixedSpace K (y • algebraMap K 𝔸[K] ξ).1
  have hy : (y • algebraMap K 𝔸[K] ξ).2 =
      ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ := by
    have h : IdeleGroup.toFinite K y = IdeleGroup.toFinite K a := by
      dsimp only [y]
      rw [map_mul, toFinite_moduleSection, one_mul]
    change ((IdeleGroup.toFinite K y : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ = _
    rw [h]
  have hval : schwartzBruhatTensor φ (cosetIndicator I b) (y • algebraMap K 𝔸[K] ξ) =
      φ z * cosetIndicator I b
        (((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ) := by
    simp only [schwartzBruhatTensor]
    rw [hy]
  change ‖schwartzBruhatTensor φ (cosetIndicator I b) (y • algebraMap K 𝔸[K] ξ)‖ ≤ _
  rw [hval, cosetIndicator_apply]
  beta_reduce
  by_cases hm : ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈
      idealFiniteAdeles I
  · rw [if_pos hm, mul_one]
    calc ‖φ z‖ ≤ A * ((1 + ‖z‖) ^ k)⁻¹ := hφ z
      _ ≤ A * (((t : ℝ) ^ r)⁻¹ * u ξ) :=
        mul_le_mul_of_nonneg_left (hbound a ha t ht ξ hξ (hdenom a ha ξ hm)) hA
      _ = ((t : ℝ) ^ r)⁻¹ * (A * u ξ) := by ring
  · rw [if_neg hm, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg hA (hu0 ξ))

theorem exists_decay_bound (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) (r : ℕ) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) → ∀ ξ : K, ξ ≠ 0 →
      ‖F ((moduleSection w t * a) • algebraMap K 𝔸[K] ξ)‖ ≤ ((t : ℝ) ^ r)⁻¹ * u ξ := by
  have hF' := schwartzBruhat_le_span_cosetIndicator hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_decay_bound_tensor_cosetIndicator w φ I b hC r
  | zero => exact ⟨0, summable_zero, fun _ _ _ _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨v, hv, hHv⟩ := hH
    refine ⟨u + v, hu.add hv, fun a ha t ht ξ hξ ↦ ?_⟩
    rw [Pi.add_apply, Pi.add_apply, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hGu a ha t ht ξ hξ) (hHv a ha t ht ξ hξ))
  | smul c G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖c‖ * u ξ, hu.mul_left _, fun a ha t ht ξ hξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hGu a ha t ht ξ hξ) (norm_nonneg c)

theorem exists_norm_adelicTheta_sub_le (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) {C : Set (IdeleGroup K)} (hC : IsCompact C) (r : ℕ) :
    ∃ M : ℝ, ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖adelicTheta F (moduleSection w t * a) - F 0‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  obtain ⟨u, hu, hFu⟩ := exists_decay_bound w hF hC r
  refine ⟨∑' ξ, |u ξ|, fun a ha t ht ↦ ?_⟩
  have hs : Summable fun ξ : K ↦ F ((moduleSection w t * a) • algebraMap K 𝔸[K] ξ) :=
    (summable_norm_smul_algebraMap _ hF).of_norm
  rw [adelicTheta, hs.tsum_eq_add_tsum_ite 0, smul_algebraMap_zero, add_sub_cancel_left,
    ← tsum_mul_left]
  refine tsum_of_norm_bounded ((hu.abs.mul_left _).hasSum) fun ξ ↦ ?_
  have ht0 : 0 < ((t : ℝ) ^ r)⁻¹ := inv_pos.2 (pow_pos t.2 r)
  split_ifs with h
  · rw [norm_zero]
    exact mul_nonneg ht0.le (abs_nonneg _)
  · exact (hFu a ha t ht ξ h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le)

def thetaConstant (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) : ℂ :=
  F 0 * ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K

theorem thetaIntegral_sub_thetaConstant (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    thetaIntegral w F χ t - thetaConstant F χ =
      ∫ u in normOneFundamentalDomain K, (adelicTheta F (moduleSection w t * (u : IdeleGroup K)) -
        F 0) * (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K := by
  rw [thetaIntegral, thetaConstant, ← integral_const_mul,
    ← integral_sub (integrableOn_thetaIntegrand w hF χ t) ((integrableOn_char χ).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only [thetaIntegrand]
  ring

theorem exists_norm_thetaIntegral_sub_le (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (r : ℕ) :
    ∃ M : ℝ, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaIntegral w F χ t - thetaConstant F χ‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  have hC : IsCompact ((Subtype.val : normOneSubgroup K → IdeleGroup K) ''
      closure (normOneFundamentalDomain K)) :=
    (isCompact_closure_normOneFundamentalDomain K).image continuous_subtype_val
  obtain ⟨M, hM⟩ := exists_norm_adelicTheta_sub_le w hF hC r
  refine ⟨M * (normOneMeasure K).real (normOneFundamentalDomain K), fun t ht ↦ ?_⟩
  rw [thetaIntegral_sub_thetaConstant w hF χ t, ← mul_assoc]
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top K)
    fun u hu ↦ ?_
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact hM _ ⟨u, subset_closure hu, rfl⟩ t ht

theorem continuous_thetaIntegral (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) : Continuous (thetaIntegral w F χ) := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  obtain ⟨N, hN, ht₀N⟩ := exists_compact_mem_nhds t₀
  have hC : IsCompact ((fun p : {r : ℝ // 0 < r} × normOneSubgroup K ↦
      moduleSection w p.1 * (p.2 : IdeleGroup K)) '' (N ×ˢ closure (normOneFundamentalDomain K))) :=
    (hN.prod (isCompact_closure_normOneFundamentalDomain K)).image
      (((continuous_moduleSection w).comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (continuous_adelicTheta hF).continuousOn
  have hfin : IsFiniteMeasure ((normOneMeasure K).restrict (normOneFundamentalDomain K)) :=
    isFiniteMeasure_restrict.2 (normOneMeasure_normOneFundamentalDomain_lt_top K).ne
  show ContinuousAt (fun t ↦ ∫ u, thetaIntegrand w F χ t u
    ∂((normOneMeasure K).restrict (normOneFundamentalDomain K))) t₀
  refine continuousAt_of_dominated (bound := fun _ ↦ M) ?_ ?_ (integrable_const M) ?_
  · exact Eventually.of_forall fun t ↦ (continuous_thetaIntegrand w hF χ t).aestronglyMeasurable
  · filter_upwards [ht₀N] with t ht
    filter_upwards [ae_restrict_mem (measurableSet_normOneFundamentalDomain K)] with u hu
    rw [thetaIntegrand, norm_mul, Circle.norm_coe, mul_one]
    exact hM _ ⟨(t, u), ⟨ht, subset_closure hu⟩, rfl⟩
  · refine Eventually.of_forall fun u ↦ Continuous.continuousAt ?_
    exact ((continuous_adelicTheta hF).comp ((continuous_moduleSection w).mul continuous_const)).mul
      continuous_const

end

end GroundTheory.Global
