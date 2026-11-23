module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsIntMulIsIntegralOfTrace
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle008
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle009
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem mem_sUnits_sup_of_local_orders {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (N : Subgroup Fˣ) (t : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ n ∈ N,
      v.valuation F (n : F) = v.valuation F (t : F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F (n : F) = 1) :
    t ∈ sUnits F S ⊔ N := by
  classical
  choose! n hnN hnv hnw using h
  set T := (finite_valuation_ne_one F t).toFinset \ S with hT
  have hP : ∏ v ∈ T, n v ∈ N :=
    N.prod_mem (fun v hv => hnN v (Finset.mem_sdiff.1 hv).2)
  have hU : t * (∏ v ∈ T, n v)⁻¹ ∈ sUnits F S := by
    rw [mem_sUnits]
    intro w hw
    have key : w.valuation F ((∏ v ∈ T, n v : Fˣ) : F) = w.valuation F (t : F) := by
      rw [Units.coe_prod, map_prod]
      by_cases hwT : w ∈ T
      · rw [Finset.prod_eq_single w]
        · exact hnv w hw
        · intro v hv hne
          exact hnw v (Finset.mem_sdiff.1 hv).2 w hw hne.symm
        · intro h'; exact absurd hwT h'
      · have h1 : w.valuation F (t : F) = 1 := by
          by_contra hc
          exact hwT (Finset.mem_sdiff.2 ⟨by simpa using hc, hw⟩)
        rw [h1]
        refine Finset.prod_eq_one (fun v hv => ?_)
        exact hnw v (Finset.mem_sdiff.1 hv).2 w hw (fun e => hwT (e ▸ hv))
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, key]
    exact mul_inv_cancel₀ (by simp)
  have : t = t * (∏ v ∈ T, n v)⁻¹ * ∏ v ∈ T, n v := by group
  rw [this]
  exact Subgroup.mul_mem_sup hU hP

theorem exists_norm_uniformizer_of_split {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (hq : IsQuad δ θ σ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : admitted F S) (hSE : admitted E SE) (hover : ∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ S)
    (hδ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F δ = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (hsq : IsSquare (algebraMap F (v.adicCompletion F) δ)) :
    ∃ a b : F, v.valuation F (a ^ 2 - δ * b ^ 2) = WithZero.exp (-1) ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → u ≠ v → u.valuation F (a ^ 2 - δ * b ^ 2) = 1 := by
  obtain ⟨w, w', hne, hw, hw'⟩ := two_places_of_isSquare F E δ θ σ hq v hsq
  obtain ⟨hc1, hc2⟩ := conj_places_transitive F E δ θ σ hq
  have hwS : w ∉ SE := by rw [hover, hw]; exact hv
  have hw'S : w' ∉ SE := by rw [hover, hw']; exact hv
  obtain ⟨-, π, hπ, hπ'⟩ := hSE w hwS
  obtain ⟨a, b, hab⟩ := (isQuad_basic F E δ θ σ hq).2.2.2.1 π
  have hun : ∀ x : HeightOneSpectrum (𝓞 E), x.under (𝓞 F) ∉ S →
      (x.under (𝓞 F)).valuation F (a ^ 2 - δ * b ^ 2) =
        x.valuation E π * x.valuation E (σ π) := by
    intro x hx
    rw [← map_mul, hab,
      valuation_unramified_of_unit F E δ θ σ hq x (hS _ hx).1 (hδ _ hx)]
  refine ⟨a, b, ?_, ?_⟩
  · have := hun w (hw ▸ hv)
    rw [hw] at this
    rw [this, hπ]
    rcases hc2 w w' (hw'.trans hw.symm) with h | h
    · exact absurd h.symm hne
    · rw [← h, hπ' w' hw'S hne.symm, mul_one]
  · intro u hu huv
    obtain ⟨x, hx⟩ := (places_over F E).2.1 u
    obtain ⟨x', hx', hxx⟩ := hc1 x
    have := hun x (hx ▸ hu)
    rw [hx] at this
    rw [this, ← hxx, hπ' x (by rw [hover, hx]; exact hu) (by rintro rfl; exact huv (hx.symm.trans hw)),
      hπ' x' (by rw [hover, hx', hx]; exact hu)
        (by rintro rfl; exact huv ((hx'.trans hx).symm.trans hw)), mul_one]

theorem exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ), ¬ IsSquare (δ : F) →
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), admitted F S ∧ δ ∈ sUnits F S ∧ ∀ t : Fˣ,
        (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
          t ∈ normSub (algebraMap F (v.adicCompletion F)) (δ : F)) →
        t ∈ sUnits F S ⊔ normSub (RingHom.id F) (δ : F) := by
  classical
  intro F _ _ δ hδ
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := exists_isQuad F δ hδ
  obtain ⟨T, -, hT⟩ := exists_admissible_superset_finite_places E ∅
  obtain ⟨S₁, hS₁, hS₁'⟩ := exists_superset_mem_sUnits F {δ} (T.image (fun w => w.under (𝓞 F)))
  obtain ⟨S, hS, hadm⟩ := exists_admissible_superset_finite_places F S₁
  have hδS : δ ∈ sUnits F S := hS₁' S hS δ (by simp)
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  have hadmE : admitted E SE := hT.mono (fun w hw =>
    (hSE w).2 (hS (hS₁ (Finset.mem_image_of_mem _ hw))))
  refine ⟨S, hadm, hδS, fun t ht => ?_⟩
  refine mem_sUnits_sup_of_local_orders S _ t (fun v hv => ?_)
  have ht0 : v.valuation F (t : F) ≠ 0 := by simp
  by_cases hsq : IsSquare (algebraMap F (v.adicCompletion F) δ)
  · obtain ⟨a, b, h1, h2⟩ := exists_norm_uniformizer_of_split hq S SE hadm hadmE hSE
      ((mem_sUnits F S δ).1 hδS) v hv hsq
    have h0 : a ^ 2 - δ * b ^ 2 ≠ 0 := by
      intro h
      rw [h, map_zero] at h1
      exact WithZero.exp_ne_zero h1.symm
    refine ⟨(Units.mk0 _ h0) ^ (-(WithZero.log (v.valuation F (t : F)))),
      Subgroup.zpow_mem _ ((mem_normSub _ _ _).2 ⟨a, b, rfl⟩) _, ?_, ?_⟩
    · rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, h1, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log ht0]
    · intro u hu huv
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, h2 u hu huv, one_zpow]
  · obtain ⟨h2, π, hπ, hπ'⟩ := hadm v hv
    have hval : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    have hev := evenNorms_of_odd_place F v
      (by have := hval 2; rwa [map_ofNat, h2] at this) _
      ((hval _).trans ((mem_sUnits F S δ).1 hδS v hv)) hsq
    obtain ⟨a, b, hab⟩ := ht v hv
    obtain ⟨m, hm⟩ := hev a b (by
      by_contra hc
      push Not at hc
      rw [hc.1, hc.2] at hab
      simp at hab)
    rw [← hab, hval] at hm
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    refine ⟨((Units.mk0 _ hπ0) ^ (-m)) ^ 2, ⟨π ^ (-m), 0, by simp⟩, ?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow,
        map_zpow₀, hπ, hm, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul]
      simp
    · intro u hu huv
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow,
        map_zpow₀, hπ' u hu huv, one_zpow, one_pow]

end GlobalTheory.QNorm
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

open Module Submodule

theorem Sized.proj_le {E : Type} [Field E] [NumberField E] [IsCMField E] {V : Type} [AddCommGroup V] [Module E V]
    {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B : ℝ} (H : Sized h Λ N ν B)
    {T : ℝ} (hT : 2 ≤ T) {v x : V} (hv : ν v ≤ T) (hx : ν x ≤ T) :
    ν (h v v • x - h x v • v) ≤ T ^ 4 := by
  have hneg : house (-(h x v)) = house (h x v) := by simp [house]
  have h0 : 0 ≤ T := by linarith
  have h1 : house (h v v) ≤ T * T := (H.form_le v v).trans (mul_le_mul hv hv (H.nonneg _) h0)
  have h2 : house (h x v) ≤ T * T := (H.form_le x v).trans (mul_le_mul hx hv (H.nonneg _) h0)
  have h3 : ν (h v v • x) ≤ T * T * T :=
    (H.smul_le _ _).trans (mul_le_mul h1 hx (H.nonneg _) (by positivity))
  have h4 : ν ((-(h x v)) • v) ≤ T * T * T :=
    (H.smul_le _ _).trans (by rw [hneg]; exact mul_le_mul h2 hv (H.nonneg _) (by positivity))
  rw [sub_eq_add_neg, ← neg_smul]
  have h5 : 2 * (T * T * T) ≤ T * (T * T * T) := mul_le_mul_of_nonneg_right hT (by positivity)
  refine (H.add_le _ _).trans ?_
  calc _ ≤ 2 * (T * T * T) := by linarith
    _ ≤ _ := h5
    _ = _ := by ring

theorem orthoSmall_of_anisoSmall (E : Type) [Field E] [NumberField E] [IsCMField E] (HA : AnisoSmall E) :
    OrthoSmall E := by
  intro n
  induction n with
  | zero =>
    intro N _
    exact ⟨∅, 0, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro N hN
    obtain ⟨S₁, k₁, hS₁, h0₁, H₁⟩ := HA (n + 1) n.succ_ne_zero N hN
    obtain ⟨M, hM, hMS⟩ := GlobalTheory.HermClass.exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)
    obtain ⟨S₂, k₂, hS₂, h0₂, H₂⟩ := ih _ (mul_ne_zero hM hN)
    refine ⟨S₁ ∪ S₂, k₁ + (k₁ + 1) * 4 * k₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩
    intro V _ _ _ h Λ ν B hV H
    obtain ⟨v, hv, hvS, hvν⟩ := H₁ V h Λ ν B hV H
    have hs := H.symm
    have hO := H.stable
    have hint := H.int
    have hB1 : 1 ≤ B := by linarith [H.two_le]
    have hBT : B ≤ B ^ (k₁ + 1) := le_self_pow₀ hB1 (Nat.succ_ne_zero _)
    have hT2 : 2 ≤ B ^ (k₁ + 1) := H.two_le.trans hBT
    have hvT : ν v ≤ B ^ (k₁ + 1) := hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_succ _))
    have hproj : ∀ x, ν x ≤ B → ν (h v v • x - h x v • v) ≤ (B ^ (k₁ + 1)) ^ 4 := fun x hx =>
      H.proj_le hT2 hvT (hx.trans hBT)
    set a := h v v with ha
    have ha0 : a ≠ 0 := fun h0 => h0₁ (h0 ▸ hvS)
    have hai : IsIntegral ℤ a := hint v hv v hv
    have has : star a = a := (hs v v).symm
    let W : Submodule E V := LinearMap.ker (h.flip v)
    have hW : ∀ x, x ∈ W ↔ h x v = 0 := fun x => Iff.rfl
    have hWr : finrank E W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (h.flip v)
      have h2 : LinearMap.range (h.flip v) = ⊤ := by
        rw [eq_top_iff]
        intro c _
        exact ⟨(c / a) • v, by simp [← ha, ha0]⟩
      rw [h2, finrank_top, finrank_self, hV] at h1
      change 1 + finrank E W = _ at h1
      omega
    let p : V →ₗ[E] W := LinearMap.codRestrict W
      (a • LinearMap.id - (h.flip v).smulRight v) fun x => by
        rw [hW]; simp [← ha, mul_comm]
    have hp : ∀ x, (p x : V) = a • x - h x v • v := fun x => rfl
    let Λ' : Submodule ℤ W := Λ.comap (W.subtype.restrictScalars ℤ)
    have hΛ' : ∀ x : W, x ∈ Λ' ↔ (x : V) ∈ Λ := fun x => Iff.rfl
    have hpΛ : ∀ x ∈ Λ, p x ∈ Λ' := fun x hx => by
      rw [hΛ', hp]; exact sub_mem (hO _ hai _ hx) (hO _ (hint x hx v hv) _ hv)
    have hyp : ∀ (y : W) (x : V), h y (p x) = a * h y x := fun y x => by
      have : h y v = 0 := y.2
      simp [hp, starRingEnd_apply, has, this]
    have H' : Sized (h.domRestrict₁₂ W W) Λ' (M * N) (fun w : W => ν w) ((B ^ (k₁ + 1)) ^ 4) :=
      { symm := fun x y => hs x y
        nondeg := fun y hy => Subtype.ext (H.nondeg y fun x => by
          have h1 : h y (p x) = 0 := hy (p x)
          rw [hyp] at h1
          exact (mul_eq_zero.1 h1).resolve_left ha0)
        fg := by
          apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective
          exact H.fg.of_le (map_comap_le _ _)
        stable := fun c hc x hx => hO c hc x hx
        int := fun x hx y hy => hint x hx y hy
        dual := fun y hy => by
          have h1 : (N : E) • a • (y : V) ∈ Λ := H.dual _ fun x hx => by
            rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]
            exact hy _ (hpΛ x hx)
          have h2 := hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1
          rw [smul_smul, smul_smul] at h2
          rw [hΛ', Submodule.coe_smul]
          convert h2 using 2
          push_cast; field_simp
        two_le := hT2.trans (le_self_pow₀ (by linarith) (by norm_num))
        nonneg := fun x => H.nonneg x
        add_le := fun x y => H.add_le x y
        smul_le := fun c x => H.smul_le c x
        form_le := fun x y => H.form_le x y
        span := by
          rw [eq_top_iff]
          intro w _
          have h1 : span E {x | x ∈ Λ ∧ ν x ≤ B} ≤
              (span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4}).comap p :=
            span_le.2 fun x hx => subset_span ⟨hpΛ x hx.1, hproj x hx.2⟩
          have h2 : p w ∈ span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4} := h1 (H.span ▸ mem_top)
          have h3 : w = a⁻¹ • p w := Subtype.ext (by
            have : h w v = 0 := w.2
            simp [hp, this, ha0])
          rw [h3]; exact smul_mem _ _ h2 }
    obtain ⟨u, huΛ, huo, huS⟩ := H₂ W (h.domRestrict₁₂ W W) Λ' _ _ hWr H'
    refine ⟨Fin.cons v fun i => u i, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · cases i using Fin.cases with
      | zero => exact hv
      | succ i => exact huΛ i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          have : h (u j) v = 0 := (u j).2
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs, this, star_zero]
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (u i).2
        | succ j => exact huo i j fun h0 => hij (congrArg _ h0)
    · cases i using Fin.cases with
      | zero => exact ⟨Or.inl hvS, hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_add_right _ _))⟩
      | succ i =>
        refine ⟨Or.inr (huS i).1, (huS i).2.trans ?_⟩
        rw [← pow_mul, ← pow_mul, ← mul_assoc]
        exact pow_le_pow_right₀ hB1 (Nat.le_add_left _ _)

end GlobalTheory.SmoothForms
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (k : ℕ) (a b : Fin n), E a b * gelfA E k = gelfA E k * E a b := by
  first | exact @GlobalTheory.SmoothForms.commute_gelfA | exact GlobalTheory.SmoothForms.commute_gelfA | (intros; apply GlobalTheory.SmoothForms.commute_gelfA <;> assumption)
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.quadraticExt_norm_form_over_algebra : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  first | exact @GlobalTheory.QuadNormBase.norm_form | exact GlobalTheory.QuadNormBase.norm_form | (intros; apply GlobalTheory.QuadNormBase.norm_form <;> assumption)
end
