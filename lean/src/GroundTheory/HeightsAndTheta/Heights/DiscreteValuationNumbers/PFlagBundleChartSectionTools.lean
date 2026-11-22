import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionFormsTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PProjIdealFormValue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagBundleChartSection

open FlagBundleSectionForms (chartPow chartMono liftNat)

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

alias chartPow_add := FlagBundleSectionForms.General.chartPow_add
alias chartPow_ne_zero := FlagBundleSectionForms.General.chartPow_ne_zero
alias chartPow_natCast := FlagBundleSectionForms.General.chartPow_natCast
alias segreVec_pow := FlagBundleSectionForms.General.segreVec_pow

section Dual

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

alias exists_flag_dual := FlagBundleSectionForms.General.exists_flag_dual

end Dual

section Forms

variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

alias chartMono_homog := FlagBundleSectionForms.General.chartMono_homog
alias eval_chartMono := FlagBundleSectionForms.General.eval_chartMono

theorem chartMono_mul (c : ∀ k, ι k) (α α' : K → ℕ) :
    chartMono (F := F) M c α * chartMono M c α' = chartMono M c (α + α') := by
  simp [chartMono, ← Finset.prod_mul_distrib, pow_add]

theorem chartMono_pow_dvd (c : ∀ k, ι k) (δ : K → ℕ) (D : ℕ) :
    chartMono (F := F) M c δ ^ D ∣
      (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ (D * ∑ k, δ k) := by
  rw [chartMono, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_
  rw [← pow_mul]
  refine pow_dvd_pow _ ?_
  calc δ k * D = D * δ k := Nat.mul_comm _ _
    _ ≤ D * ∑ k, δ k := Nat.mul_le_mul_left D (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k))

alias chartRing_forms := FlagBundleSectionForms.General.chartRing_forms

theorem chartRing_forms_fin (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {L : ℕ}
    {u : Fin L → Ω} (hu : ∀ l, u l ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (U : Fin L → MRing (bundleIdx ι M) F), (∀ l, IsMultiHomog (U l) (liftNat fun _ => n)) ∧
      ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) (U l) =
        algebraMap Ω Φ (u l * segreVec y c ^ n) := by
  have h := fun l => chartRing_forms (M := M) y w φ t c hc (hu l)
  choose n U hU hUe using h
  refine ⟨∑ l, n l, fun l => U l * chartMono M c (fun _ => ∑ l, n l - n l), fun l => ?_, fun l => ?_⟩
  · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    have hd : liftNat (K := K) (fun _ => ∑ l, n l) =
        liftNat (fun _ => n l) + liftNat (fun _ => ∑ l, n l - n l) := by
      funext o; cases o <;> simp [liftNat]; omega
    rw [hd]
    exact (hU l).mul (chartMono_homog M c _)
  · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    rw [eval₂_mul, hUe, eval_chartMono, ← map_mul]
    congr 1
    rw [Finset.prod_pow, mul_assoc, ← segreVec, ← pow_add, Nat.add_sub_cancel' hle]

alias eval_eq_zero_of_mem_projIdeal := FlagBundleSectionForms.General.eval_eq_zero_of_mem_projIdeal

end Forms

section New

variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem component_mem_projIdeal (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {q : MRing (bundleIdx ι M) F}
    (hq : q ∈ projIdeal F y w φ t) (d : Option K → ℕ) :
    weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q ∈ projIdeal F y w φ t := by
  classical
  rw [ProjIdealFormValue.proof F Ω K ι y N E w M φ Φ t d _
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
  rw [projIdeal, RingHom.mem_ker, coe_eval₂Hom] at hq
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) hq
  rw [← q.support_sum_monomial_coeff, eval₂_sum, coeff_sum, coeff_zero] at hc
  rw [weightedHomogeneousComponent_apply, eval₂_sum, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun m _ => ?_).trans hc
  rw [ProjIdealFormValue.eval₂_monomial_cone, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero]
  have hiff : Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm d ↔
      Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := by
    rw [Finsupp.ext_iff, funext_iff]
    exact forall_congr' fun o => by rw [ProjIdealFormValue.weight_blockWeight_apply]; rfl
  simp only [hiff]

theorem eval_trunc_eq_zero (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {t : Fin N → Φ} (ht : AlgebraicIndependent Ω t) (i : ℕ)
    {q : MRing (bundleIdx ι M) F} (hq : q ∈ projIdeal F y w φ (truncCoord t i)) (τ : Fin N → Φ) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord τ i)) q = 0 := by
  classical
  let G : (Σ o, bundleIdx ι M o) → MvPolynomial (Fin N) Ω := fun p =>
    match p with
    | ⟨none, l⟩ => ∑ j : Fin N, (if (j : ℕ) < i then X j else 0) * C (φ l (w j))
    | ⟨some k, p⟩ => C (y ⟨k, p⟩)
  have key : ∀ τ : Fin N → Φ, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord τ i)) q =
      aeval τ (eval₂ (C.comp (algebraMap F Ω)) G q) := by
    intro τ
    have h := eval₂_comp_left (aeval τ : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ).toRingHom
      (C.comp (algebraMap F Ω)) G q
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    rw [h]
    congr 1
    · ext r
      simp
    · funext p
      rcases p with ⟨_ | k, p⟩
      · simp [G, projCoord, truncCoord, map_sum, apply_ite]
      · simp [G, projCoord]
  have h0 : eval₂ (C.comp (algebraMap F Ω)) G q = 0 :=
    ht (by rw [map_zero, ← key t]; exact eval_eq_zero_of_mem_projIdeal y w φ _ hq)
  rw [key τ, h0, map_zero]

def substDeg (e d : Option K → ℕ) : Option K → ℕ :=
  fun o => Option.elim o 0 (fun k => d (some k)) + d none * e o

theorem bind₁_isMultiHomog (g : (Σ o, bundleIdx ι M o) → MRing (bundleIdx ι M) F) (e : Option K → ℕ)
    (hs : ∀ k (p : ι k), g ⟨some k, p⟩ = X ⟨some k, p⟩) (hn : ∀ l, IsMultiHomog (g ⟨none, l⟩) e)
    {q : MRing (bundleIdx ι M) F} {d : Option K → ℕ} (hq : IsMultiHomog q d) :
    IsMultiHomog (bind₁ g q) (substDeg e d) := by
  let Λ : (Option K → ℕ) →+ (Option K → ℕ) :=
    { toFun := substDeg e
      map_zero' := by funext o; cases o <;> simp [substDeg]
      map_add' := fun d d' => by funext o; cases o <;> simp [substDeg] <;> ring }
  have hg : ∀ v, IsWeightedHomogeneous (blockWeight (bundleIdx ι M)) (g v) (Λ (blockWeight _ v)) := by
    rintro ⟨_ | k, p⟩
    · have : Λ (blockWeight (bundleIdx ι M) ⟨none, p⟩) = e := by
        funext o; cases o <;> simp [Λ, substDeg, blockWeight]
      rw [this]
      exact hn p
    · have : Λ (blockWeight (bundleIdx ι M) ⟨some k, p⟩) = blockWeight (bundleIdx ι M) ⟨some k, p⟩ := by
        funext o; cases o <;> simp [Λ, substDeg, blockWeight, Pi.single_apply]
      rw [this, show g ⟨some k, p⟩ = X ⟨some k, p⟩ from hs k p]
      exact isWeightedHomogeneous_X F _ _
  rw [← q.support_sum_monomial_coeff, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := hq (mem_support_iff.mp hm)
  rw [bind₁_monomial]
  have := (isWeightedHomogeneous_C (blockWeight (bundleIdx ι M)) (coeff m q)).mul
    (IsWeightedHomogeneous.prod m.support (fun v => g v ^ m v) (fun v => m v • Λ (blockWeight _ v))
      (fun v _ => (hg v).pow (m v)))
  rw [zero_add] at this
  have hΛ : substDeg e d = ∑ v ∈ m.support, m v • Λ (blockWeight (bundleIdx ι M) v) := by
    show Λ d = _
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hΛ]
  exact this

theorem bind₁_scale (u : MRing (bundleIdx ι M) F) {q : MRing (bundleIdx ι M) F} {d : Option K → ℕ}
    (hq : IsMultiHomog q d) :
    bind₁ (fun v => u ^ blockWeight (bundleIdx ι M) v none * X v) q = u ^ d none * q := by
  conv_lhs => rw [← q.support_sum_monomial_coeff]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := hq (mem_support_iff.mp hm)
  have hs : ∑ v ∈ m.support, blockWeight (bundleIdx ι M) v none * m v = d none := by
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [mul_comm]
  rw [bind₁_monomial, monomial_eq, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, hs]
  ring

theorem bind₁_sub_mem {σ R : Type*} [CommRing R] (I : Ideal (MvPolynomial σ R)) (g g' : σ → MvPolynomial σ R)
    (h : ∀ v, g' v - g v ∈ I) (q : MvPolynomial σ R) : bind₁ g' q - bind₁ g q ∈ I := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact I.add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul, map_mul, bind₁_X_right, bind₁_X_right,
      show bind₁ g' p * g' v - bind₁ g p * g v =
        (bind₁ g' p - bind₁ g p) * g' v + bind₁ g p * (g' v - g v) by ring]
    exact I.add_mem (I.mul_mem_right _ hp) (I.mul_mem_left _ (h v))

theorem isMultiHomog_sub {f g : MRing (bundleIdx ι M) F} {d : Option K → ℕ} (hf : IsMultiHomog f d)
    (hg : IsMultiHomog g d) : IsMultiHomog (f - g) d :=
  (mem_weightedHomogeneousSubmodule F _ _ _).mp (Submodule.sub_mem _
    ((mem_weightedHomogeneousSubmodule F _ _ _).mpr hf) ((mem_weightedHomogeneousSubmodule F _ _ _).mpr hg))

end New

section SectionForm

variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem exists_section_form (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b) (a : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (t : Fin N → Φ) (i : Fin N)
    (c : ∀ k, ι k) (hsc : segreVec y c ≠ 0) :
    ∃ (dl : Option K → ℕ) (β : K → ℕ) (f : MRing (bundleIdx ι M) F), IsMultiHomog f dl ∧
      (fun o => (dl o : ℤ) - liftNat β o) = zetaDeg + liftDeg (b i - a) ∧
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
        t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
          (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (chartMono M c β) := by
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hsc) k (Finset.mem_univ _)
  obtain ⟨ψ, hψint, hψlow, hψi⟩ := exists_flag_dual y B w b hfl c hsc i
  obtain ⟨u, hu, hψ⟩ := hφ.generate c hsc ψ hψint
  have hstar : t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ =
      ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
        projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ := by
    have h1 : ∑ j, truncCoord t ((i : ℕ) + 1) j * algebraMap Ω Φ (ψ (w j)) =
        t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ := by
      rw [Finset.sum_eq_single i]
      · simp [truncCoord, hψi]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with h | h
        · simp [hψlow j h]
        · have : ¬ (j : ℕ) < (i : ℕ) + 1 := by
            have : (i : ℕ) < j := h
            omega
          simp [truncCoord, this]
      · simp
    rw [← h1, hψ]
    simp only [projCoord, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [chartPow, Pi.neg_apply]
    ring
  obtain ⟨n, U, hUh, hUe⟩ := chartRing_forms_fin (M := M) y w φ (truncCoord t ((i : ℕ) + 1)) c hsc hu
  let α : K → ℕ := fun k => (|a k| + |b i k| - a k).toNat
  let β : K → ℕ := fun k => (|a k| + |b i k| + n - b i k).toNat
  have hid : segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ α k =
      (∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i) * chartPow y c (-a) := by
    rw [segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_add hY, ← chartPow_add hY,
      ← chartPow_add hY]
    congr 1
    funext k
    have h1 := le_abs_self (a k)
    have h2 := neg_abs_le (a k)
    have h3 := le_abs_self (b i k)
    have h4 := neg_abs_le (b i k)
    simp only [Pi.add_apply, Pi.neg_apply, α, β]
    omega
  let f : MRing (bundleIdx ι M) F := ∑ l, U l * chartMono M c α * X ⟨none, l⟩
  have hg : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1)))
      (chartMono M c β) = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := eval_chartMono y w φ _ c β
  have hf : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f
      = t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
        (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (chartMono M c β) := by
    rw [hg]
    calc _ = ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
            projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          simp only [f, eval₂_sum, eval₂_mul, eval₂_X, hUe, eval_chartMono]
          refine Finset.sum_congr rfl fun l _ => ?_
          have hl : algebraMap Ω Φ (u l * segreVec y c ^ n) * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) =
              algebraMap Ω Φ (u l * chartPow y c (-a)) *
                algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
            rw [← map_mul, ← map_mul]
            congr 1
            rw [mul_assoc, hid]
            ring
          rw [mul_comm _ (projCoord _ _ _ _ _), mul_assoc, hl]
          ring
      _ = t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          rw [hstar, Finset.sum_mul]
      _ = t i * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := by
          have hp : algebraMap Ω Φ (chartPow y c (b i)) ≠ 0 :=
            (map_ne_zero _).2 (chartPow_ne_zero hY _)
          rw [map_inv₀, map_mul]
          field_simp
  refine ⟨fun o => Option.elim o 1 (fun k => n + α k), β, f, ?_, ?_, hf⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
    have h := ((hUh l).mul (chartMono_homog (F := F) M c α)).mul
      (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)
    convert h using 1
    funext o
    cases o <;> simp [liftNat, blockWeight]
  · funext o
    cases o with
    | none => simp [liftNat, zetaDeg, liftDeg]
    | some k =>
      have h1 := le_abs_self (a k)
      have h2 := neg_abs_le (a k)
      have h3 := le_abs_self (b i k)
      have h4 := neg_abs_le (b i k)
      simp only [liftNat, zetaDeg, liftDeg, Option.elim, Pi.add_apply, Pi.sub_apply, α, β]
      omega

end SectionForm

end FlagBundleChartSection

end

end GroundTheory.Heights₂.Heights.NumbersDVR
