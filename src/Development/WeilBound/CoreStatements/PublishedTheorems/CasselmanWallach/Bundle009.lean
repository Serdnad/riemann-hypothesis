module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped InnerProductSpace
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary adjSign)

namespace PositivityTheory.CW.EigenOrthogonalForm

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem cas_symm (hu : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hu a b, hu b a]
  simp [adjSign, hab]

theorem inner_eq_zero_of_eig (hu : IsInfUnitary ε E) {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : ⟪v, y⟫_ℂ = 0 := by
  have h := cas_symm hu v y
  rw [hv, hy, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have h' : ((μ : ℂ) - μ') * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) hne
  · exact h0

theorem B_eq_zero (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y))
    {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : B v y = 0 := by
  have h := hB v y
  rw [hv, hy] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Complex.conj_ofReal,
    RingHom.id_apply] at h
  have h2 : ((μ : ℂ) - μ') * B v y = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) hne
  · exact h3

end PositivityTheory.CW.EigenOrthogonalForm

namespace PositivityTheory.CW

open EigenOrthogonalForm in
theorem e2c : CasimirPairingBound := by
  intro n ε V _ _ E _ _ hM Q hQ η
  let S : Submodule ℂ V :=
    { carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪a, y⟫_ℂ‖ ≤ C * Q y}
      add_mem' := by
        rintro a b ⟨C₁, h₁, ha⟩ ⟨C₂, h₂, hb⟩
        refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun y => ?_⟩
        rw [inner_add_left, add_mul]
        exact (norm_add_le _ _).trans (add_le_add (ha y) (hb y))
      zero_mem' := ⟨0, le_rfl, fun y => by simp⟩
      smul_mem' := by
        rintro c a ⟨C, h, ha⟩
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) h, fun y => ?_⟩
        rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
        exact mul_le_mul_of_nonneg_left (ha y) (norm_nonneg _) }
  suffices hS : S = ⊤ by
    have hη : η ∈ S := hS ▸ Submodule.mem_top
    exact hη
  rw [eq_top_iff, ← hM.span, Submodule.span_le]
  rintro w ⟨μ, hw⟩
  let W : Submodule ℂ V := Module.End.eigenspace (casimirK ε E) (μ : ℂ)
  have hWmem : ∀ v, v ∈ W ↔ casimirK ε E v = (μ : ℂ) • v := fun v => Module.End.mem_eigenspace_iff
  haveI : FiniteDimensional ℂ W := by
    haveI := hM.fin μ
    have hle : W ≤ Submodule.span ℂ {v | ∃ μ' ≤ μ, Eig ε E μ' v} :=
      fun v hv => Submodule.subset_span ⟨μ, le_rfl, (hWmem v).1 hv⟩
    exact Submodule.finiteDimensional_of_le hle
  let P : (V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) → Prop := fun B =>
    (∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y)) ∧ ∀ v y, ‖B v y‖ ≤ Q v * Q y
  let G : Set (Module.Dual ℂ W) := {g | ∃ B, P B ∧ ∃ v ∈ W, g = (B v).comp W.subtype}
  have hspan : Submodule.span ℂ G = ⊤ := by
    have hco : (Submodule.span ℂ G).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      by_contra hne
      have hy0 : (y : V) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨B, hB1, hB2, hB3⟩ := hQ y hy0
      have hg : (B y).comp W.subtype ∈ Submodule.span ℂ G :=
        Submodule.subset_span ⟨B, ⟨hB1, hB2⟩, y, y.2, rfl⟩
      exact hB3 ((Submodule.mem_dualCoannihilator _).1 hy _ hg)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ G), hco,
      Submodule.dualAnnihilator_bot]
  have hl : (innerₛₗ ℂ w).comp W.subtype ∈ Submodule.span ℂ G := hspan ▸ Submodule.mem_top
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 hl
  choose B hB v hv hgv using fun i => (g i).2
  have hid : innerₛₗ ℂ w = ∑ i, f i • B i (v i) := by
    refine LinearMap.ext_on hM.span ?_
    rintro y ⟨lam, hy⟩
    by_cases hμ : lam = μ
    · subst hμ
      have hyW : y ∈ W := (hWmem y).2 hy
      have := LinearMap.congr_fun hfg ⟨y, hyW⟩
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hgv, LinearMap.comp_apply,
        Submodule.subtype_apply] at this
      rw [← this, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    · have h0 : ⟪w, y⟫_ℂ = 0 := inner_eq_zero_of_eig hM.uni (Ne.symm hμ) hw hy
      have h1 : ∀ i, B i (v i) y = 0 := fun i =>
        B_eq_zero (B i) (hB i).1 (Ne.symm hμ) ((hWmem _).1 (hv i)) hy
      rw [LinearMap.sum_apply, innerₛₗ_apply_apply, h0]
      simp [h1]
  show ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪w, y⟫_ℂ‖ ≤ C * Q y
  refine ⟨∑ i, ‖f i‖ * Q (v i),
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg Q _), fun y => ?_⟩
  have hwy : ⟪w, y⟫_ℂ = ∑ i, f i * B i (v i) y := by
    have h := LinearMap.congr_fun hid y
    rw [innerₛₗ_apply_apply, LinearMap.sum_apply] at h
    rw [h]
    simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hwy, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hB i).2 _ _) (norm_nonneg _)

end PositivityTheory.CW
end

section

noncomputable section

open Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped Topology

namespace PositivityTheory.CW

namespace SlopeLimitConstant

variable {n : ℕ}

theorem const_of_slope {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
    {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) (f : ℝ → E)
    (hf : ∀ t, Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (f (t + h) - f t)) (𝓝[≠] 0) (𝓝 0)) : f 1 = f 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 (f 1 - f 0) (sub_ne_zero.2 hne)
  set g : ℝ → ℝ := fun t => p i (f t - f 0) with hg
  have hd : ∀ t, HasDerivAt g 0 t := by
    intro t
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h1 : Tendsto (fun h : ℝ => p i (((h : ℂ)⁻¹) • (f (t + h) - f t))) (𝓝[≠] 0) (𝓝 0) := by
      have := ((hp.continuous_seminorm i).tendsto 0).comp (hf t)
      rw [map_zero] at this
      exact this
    refine squeeze_zero_norm (fun h => ?_) h1
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, map_smul_eq_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_sub_map_le_sub (p i) (f (t + h) - f 0) (f t - f 0)
    simpa [hg] using this
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  apply hi
  have : g 1 = 0 := by rw [hc]; simp [hg]
  simpa [hg] using this

theorem tendsto_pi_zero {ε : Fin n → Bool} {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} {π dπ : Mx n → (E →L[ℂ] E)} (hπ : IsSmoothModRep ε p π dπ)
    {ι : Type} {l : Filter ι} {v : ι → E} (hv : Tendsto v l (𝓝 0)) {g : ι → Mx n} {g₀ : Mx n}
    (hg : ∀ x, g x ∈ UJset ε) (hg₀ : Tendsto g l (𝓝 g₀)) : Tendsto (fun x => π (g x) (v x)) l (𝓝 0) := by
  rw [hπ.withSeminorms.tendsto_nhds _ 0]
  intro i δ hδ
  obtain ⟨q, N, hq, hb⟩ := hπ.growth i
  have h1 : Tendsto (fun x => (1 + hs (g x)) ^ N * q (v x)) l (𝓝 ((1 + hs g₀) ^ N * 0)) := by
    refine Tendsto.mul ?_ ?_
    · exact ((tendsto_const_nhds.add ((continuous_hs).tendsto g₀ |>.comp hg₀)).pow N)
    · have := (hq.tendsto 0).comp hv
      rw [map_zero] at this
      exact this
  rw [mul_zero] at h1
  filter_upwards [(tendsto_order.1 h1).2 δ hδ] with x hx
  rw [sub_zero]
  exact lt_of_le_of_lt (hb (g x) (hg x) (v x)) hx

theorem Dw_sub {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H}
    (hx : Sm ε σ x) (hy : Sm ε σ y) : Dw σ l (x - y) = Dw σ l x - Dw σ l y := by
  have hy' : Sm ε σ ((-1 : ℂ) • y) := by
    rw [sm_iff] at hy ⊢
    exact Submodule.smul_mem _ _ hy
  rw [sub_eq_add_neg, ← neg_one_smul ℂ y, Dw_add hσ hl hx hy', Dw_smul hσ hl _ hy, neg_one_smul, ← sub_eq_add_neg]

theorem tendsto_rem {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) (hSD : SobDiff ε σ) {T : H →ₗ[ℂ] E}
    (hT : SobBdOn ε σ (Sm ε σ) p T) {X : Mx n} (hX : X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w))
      (𝓝[≠] 0) (𝓝 0) := by
  have hwX : Sm ε σ (dRep σ X w) := by
    have := hw.word hσ (l := [X]) (by simpa using hX)
    simpa [Dw] using this
  have hsm : ∀ h : ℝ, Sm ε σ (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) := by
    intro h
    have h1 := hw.translate hσ (exp_mem_UJ hX h)
    rw [sm_iff] at h1 hw hwX ⊢
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 hw) (Submodule.smul_mem _ _ hwX)
  rw [hp.tendsto_nhds _ 0]
  intro j δ hδ
  obtain ⟨S, C, hS, hb⟩ := hT j
  have hl : ∀ l ∈ S, Tendsto (fun h : ℝ =>
      ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖) (𝓝[≠] 0) (𝓝 0) := by
    intro l hlS
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := hS l hlS
    have hd := hSD l hl' w hw X hX
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have e0 : Dw σ l (σ (NormedSpace.exp ((0 : ℝ) • X)) w) = Dw σ l w := by
      rw [zero_smul, NormedSpace.exp_zero, sigma_one hσ]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hd
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have htr := hw.translate hσ (exp_mem_UJ hX h)
    have hsw : Sm ε σ ((h : ℂ) • dRep σ X w) := by
      rw [sm_iff] at hwX ⊢
      exact Submodule.smul_mem _ _ hwX
    have hdiff : Sm ε σ (σ (NormedSpace.exp (h • X)) w - w) := by
      rw [sm_iff] at htr hw ⊢
      exact Submodule.sub_mem _ htr hw
    rw [Dw_sub hσ hl' hdiff hsw, Dw_sub hσ hl' htr hw, Dw_smul hσ hl' _ hwX, zero_add, e0,
      ← Complex.coe_smul, Complex.ofReal_inv, smul_sub, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hh', one_smul]
  have hsum : Tendsto (fun h : ℝ => C * (S.map fun l =>
      ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖).sum) (𝓝[≠] 0) (𝓝 0) := by
    have := (tendsto_list_sum (l := S) hl).const_mul C
    simpa using this
  have hle : ∀ h : ℝ, p j (((h : ℂ)⁻¹) • T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) - 0) ≤
      C * (S.map fun l =>
        ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖).sum := by
    intro h
    rw [sub_zero, map_smul_eq_mul]
    calc ‖((h : ℂ)⁻¹)‖ * p j (T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w))
        ≤ ‖((h : ℂ)⁻¹)‖ * (C * sobNorm σ S (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)) :=
          mul_le_mul_of_nonneg_left (hb _ (hsm h)) (norm_nonneg _)
      _ = _ := by
          rw [sobNorm, mul_left_comm, ← List.sum_map_mul_left]
          congr 2
          exact List.map_congr_left fun l _ => (norm_smul _ _).symm
  filter_upwards [(tendsto_order.1 hsum).2 δ hδ] with h hh
  exact lt_of_le_of_lt (hle h) hh

theorem tendsto_key {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} {π dπ : Mx n → (E →L[ℂ] E)} (hπ : IsSmoothModRep ε p π dπ)
    (hSD : SobDiff ε σ) {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) {X : Mx n} (hX : X ∈ lieSet ε)
    (hc : ∀ w, Sm ε σ w → T (dRep σ X w) = dπ X (T w)) {w : H} (hw : Sm ε σ w) :
    Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) •
      (π (NormedSpace.exp ((-h) • X)) (T (σ (NormedSpace.exp (h • X)) w)) - T w)) (𝓝[≠] 0) (𝓝 0) := by
  set a := T w
  set b := dπ X a
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => neg_ne_zero.2 hx⟩
    have := ((continuous_neg (G := ℝ)).tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    simpa using this
  have hg : Tendsto (fun h : ℝ => NormedSpace.exp ((-h) • X)) (𝓝[≠] 0) (𝓝 1) := by
    have := ((continuous_exp_smul X).tendsto 0).comp (tendsto_nhdsWithin_iff.1 hneg).1
    simpa [Function.comp_def] using this
  have hgU : ∀ h : ℝ, NormedSpace.exp ((-h) • X) ∈ UJset ε := fun h => exp_mem_UJ hX (-h)
  have hgW : Tendsto (fun h : ℝ => NormedSpace.exp ((-h) • X)) (𝓝[≠] 0) (𝓝[UJset ε] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hg, Eventually.of_forall hgU⟩

  have t1 := tendsto_pi_zero hπ (tendsto_rem hσ hπ.withSeminorms hSD hT hX hw) hgU hg
  have t2 : Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (π (NormedSpace.exp ((-h) • X)) a - a)) (𝓝[≠] 0) (𝓝 (-b)) := by
    have := ((hπ.hasDRep X hX a).comp hneg).neg
    refine this.congr' (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply, Complex.ofReal_neg, inv_neg, neg_smul, neg_neg]
  have t3 : Tendsto (fun h : ℝ => π (NormedSpace.exp ((-h) • X)) b) (𝓝[≠] 0) (𝓝 b) := by
    have := ((hπ.continuousOn b) 1 (one_mem_UJ ε)).tendsto.comp hgW
    rw [hπ.map_one] at this
    exact this
  have hsum := (t1.add t2).add t3
  rw [zero_add, neg_add_cancel] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hTu : T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) =
      T (σ (NormedSpace.exp (h • X)) w) - a - (h : ℂ) • b := by
    rw [map_sub, map_sub, map_smul, hc w hw]
  rw [hTu, (π (NormedSpace.exp ((-h) • X))).map_smul, map_sub, map_sub, (π (NormedSpace.exp ((-h) • X))).map_smul]
  rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hh', one_smul]
  abel

end SlopeLimitConstant

open SlopeLimitConstant in
theorem d4b : D4 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hSD T hT X hX hc w hw
  set f : ℝ → E := fun t => π (NormedSpace.exp ((-t) • X)) (T (σ (NormedSpace.exp (t • X)) w)) with hf
  have hmulπ : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ y, π a (π b y) = π (a * b) y := by
    intro a ha b hb y
    rw [hπ.map_mul a ha b hb]; rfl
  have hslope : ∀ t, Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (f (t + h) - f t)) (𝓝[≠] 0) (𝓝 0) := by
    intro t
    have hwt := hw.translate hU (exp_mem_UJ hX t)
    have hk := tendsto_key hU hπ hSD hT hX hc hwt
    have := ((π (NormedSpace.exp ((-t) • X))).continuous.tendsto 0).comp hk
    rw [map_zero] at this
    refine this.congr' (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply, hf, map_smul, map_sub]
    congr 2
    · rw [hmulπ _ (exp_mem_UJ hX _) _ (exp_mem_UJ hX _), ← exp_add_smul, ← sigma_mul hU (exp_mem_UJ hX _)
        (exp_mem_UJ hX _), ← exp_add_smul, neg_add, add_comm h t]
  have h10 := const_of_slope hπ.withSeminorms f hslope
  simp only [hf, neg_zero, zero_smul, NormedSpace.exp_zero, sigma_one hU, hπ.map_one] at h10
  have h11 := congrArg (π (NormedSpace.exp ((1 : ℝ) • X))) h10
  rw [hmulπ _ (exp_mem_UJ hX _) _ (exp_mem_UJ hX _), ← exp_add_smul, add_neg_cancel, zero_smul,
    NormedSpace.exp_zero, hπ.map_one, one_smul] at h11
  simpa using h11

end PositivityTheory.CW
end
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

theorem c7 : C7 := by
  classical
  intro hMax hC4 n ε H _ _ _ σ hU hI hD E hKD hM N
  obtain ⟨m, K, I0, hK0, hmax⟩ := hMax n ε (kfin ε σ) E hM N
  obtain ⟨S, C', hS, hC', hbd⟩ := hC4 n ε H σ hU hI hD E hKD m
  refine ⟨S, K * C', I0.image Subtype.val, hS, mul_nonneg hK0 hC', ?_, ?_⟩
  · intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    exact x.2
  · intro F hcont hder hgrow B hB hI0 v hv
    let F' : kfin ε σ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ → ℂ := F ∘ₗ (kfin ε σ).subtype
    have key := hmax F' (fun w => hcont w w.2)
      (fun X hX w g hg => by
        have h1 := hder X hX.1 w w.2 g hg
        show HasDerivAt (fun t : ℝ => F (w : H) (g * NormedSpace.exp (t • X)))
          (F ((ReciprocityTheory.ChartRestriction.DS.actM E X w : kfin ε σ) : H) g) 0
        rw [hKD X hX.1 w]
        exact h1)
      (fun w => hgrow w w.2) B hB
      (fun e he g hg => hI0 e.1 (Finset.mem_image_of_mem _ he) g hg) ⟨v, hv⟩
    calc ‖F v 1‖ = ‖F' ⟨v, hv⟩ 1‖ := rfl
      _ ≤ K * B * ‖((1 + ReciprocityTheory.ChartRestriction.DS.casimirK ε E) ^ m) ⟨v, hv⟩‖ := key
      _ ≤ K * B * (C' * sobNorm σ S v) :=
        mul_le_mul_of_nonneg_left (hbd ⟨v, hv⟩) (mul_nonneg hK0 hB)
      _ = K * C' * B * sobNorm σ S v := by ring

end PositivityTheory.CW
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW

theorem e3d : SobolevNormDomination := by
  intro he2 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT hd q hq hq1 S hS
  let Dop : List (Mx n) → (E →L[ℂ] E) := fun l =>
    l.foldr (fun X f => (dπ X).comp f) (ContinuousLinearMap.id ℂ E)
  have key : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v →
      IsKFin ε σ (Dw σ l v) ∧ T (Dw σ l v) = Dop l (T v) := by
    intro l
    induction l with
    | nil => intro _ v hv; exact ⟨hv, rfl⟩
    | cons X l ih =>
      intro hl v hv
      obtain ⟨h1, h2⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) v hv
      refine ⟨hD.2.1 _ h1 X (hl X List.mem_cons_self), ?_⟩
      show T (dRep σ X (Dw σ l v)) = dπ X (Dop l (T v))
      rw [hd X (hl X List.mem_cons_self) _ h1, h2]
  have hcont : ∀ l, Continuous (q.comp (Dop l : E →ₗ[ℂ] E)) := fun l => by
    rw [Seminorm.coe_comp, ContinuousLinearMap.coe_coe]
    exact hq.comp (Dop l).continuous
  have hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ w, Sm ε σ w →
      ‖Dw σ l w‖ ≤ (q.comp (Dop l : E →ₗ[ℂ] E)) (T w) := by
    intro l hl
    refine (he2 n ε H σ hU hI E p π dπ hπ hD T hT _ (hcont l) l 0 0 hl).2 fun y hy => ?_
    obtain ⟨h1, h2⟩ := key l hl y hy
    calc ‖Dw σ l y‖ ≤ q (T (Dw σ l y)) := hq1 _ h1
      _ = _ := by rw [h2]; rfl
  have main : ∀ S : List (List (Mx n)), Words (lieSet ε) S →
      ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ w, Sm ε σ w → sobNorm σ S w ≤ q' (T w) := by
    intro S
    induction S with
    | nil =>
      intro _
      refine ⟨0, by rw [Seminorm.coe_zero]; exact continuous_zero, fun w _ => ?_⟩
      simp [sobNorm]
    | cons l S ih =>
      intro hS
      obtain ⟨q', hq', h'⟩ := ih (fun m hm => hS m (List.mem_cons_of_mem _ hm))
      have hl : ∀ X ∈ l, X ∈ lieSet ε := hS l List.mem_cons_self
      refine ⟨q.comp (Dop l : E →ₗ[ℂ] E) + q', ?_, fun w hw' => ?_⟩
      · rw [Seminorm.coe_add]
        exact (hcont l).add hq'
      · have e : sobNorm σ (l :: S) w = ‖Dw σ l w‖ + sobNorm σ S w := by
          first
            | rfl
            | simp [sobNorm]
        rw [e, Seminorm.add_apply]
        exact add_le_add (hw l hl w hw') (h' w hw')
  exact main S hS

end PositivityTheory.CW

end
end
