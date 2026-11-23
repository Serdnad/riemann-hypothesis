module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

open Formalism.FourierDecayAlt.P.Qx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section fam

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ}

def EqvL (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (J : Mx k r → (Wq →L[ℂ] Wp)) : Prop :=
  LeftEq k r z i D J ∧ RightEq k r z' i D J ∧
    ∀ g ∈ Glev k r i ∩ D, ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', J (h * g * h') = (π h).comp ((J g).comp (π' h'))

def FamD (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  (∀ c ∈ OmX r, EqvL z z' π π' i D (Φ c)) ∧
  ∀ c₀ ∈ OmX r, ∀ g₀ ∈ Glev k r i ∩ D, ∃ (U : Set ((Fin r → ℂ) × Mx k r)) (F : (Fin r → ℂ) × Mx k r → (Wq →L[ℂ] Wp)),
    IsOpen U ∧ (c₀, g₀) ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ x ∈ U, x.1 ∈ OmX r → x.2 ∈ Glev k r i → x.2 ∈ D → Φ x.1 x.2 = F x

theorem famD_FFl {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    {i : Fin (r + 1)} {D : Set (Mx k r)} (hD : IsOpen D) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamD z z' π π' i D Φ)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) : Φ c ∈ FFl k r z z' π π' i D := by
  refine ⟨?_, (hΦ.1 c hc).1, (hΦ.1 c hc).2.1, (hΦ.1 c hc).2.2⟩
  intro g₀ hg₀
  obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2 c hc g₀ hg₀
  refine ⟨(fun g => (c, g)) ⁻¹' U ∩ D, fun g => F (c, g), (hU.preimage (by fun_prop)).inter hD, ⟨hx, hg₀.2⟩, ?_,
    fun g hg hgl => hΦF (c, g) hg.1 hc hgl hg.2⟩
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg.1)

theorem upd_mem {c : Fin r → ℂ} (hc : c ∈ OmX r) {c'' : ℂ} (h : c'' ≠ 0) (l : Fin r) :
    Function.update c l c'' ∈ OmX r := by
  intro a
  by_cases ha : a = l
  · subst ha; simpa using h
  · simpa [Function.update_apply, ha] using hc a

def JxF (l : Fin r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Fn k r (Wq →L[ℂ] Wp) :=
  fun c g => (psi k r z cStd (uL k r l g) * psi k r z' cStd (iH (uL k r l (iH g)))) •
    Φ (Function.update c l (cF k r l g)) (rho k r l g)

theorem dec_JxF {l : Fin r} {g u g₁ u' : Mx k r} {c' : ℂ} (h : Dec k r l g c' u g₁ u')
    (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) :
    JxF l z z' Φ c g = (psi k r z cStd u * psi k r z' cStd u') • Φ (Function.update c l c') g₁ := by
  unfold JxF
  rw [h.uL_eq, h.uL_iH, h.cF_eq, h.rho_eq, iH_eq (up_inv h.hu').1.1, inv_inv' h.hu'.1.1]

theorem descended_function_apply_w1_mul {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r)
    (Φ : Fn k r (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) {c' : ℂ} (hc' : c' ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    JxF l z z' Φ c (w1 k r l c' * g) = Φ (Function.update c l c') g := by
  rw [dec_JxF (dec_w hc' hg), psi_one hz, psi_one hz', one_mul, one_smul]

theorem w1_mul_mem_descended_set_iff (l : Fin r) (D₁ : Set (Mx k r)) {c : ℂ} (hc : c ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g ∈ D0 k r l D₁ ↔ g ∈ D₁ := by
  have d := dec_w (l := l) hc hg
  constructor
  · intro h
    have h2 : rho k r l (w1 k r l c * g) ∈ D₁ := h.2
    rwa [d.rho_eq] at h2
  · intro h
    refine ⟨d.cell_decomposition_mem, ?_⟩
    show rho k r l (w1 k r l c * g) ∈ D₁
    rw [d.rho_eq]; exact h

theorem smM_snd (s : Set ((Fin r → ℂ) × Mx k r)) : SmM (fun x : (Fin r → ℂ) × Mx k r => x.2) s := fun i j =>
  ((contDiff_apply_apply ℝ i j).comp contDiff_snd).contDiffOn

theorem descended_set_is_domain {z z' : Fin (2 * r + k + 1) → ℂ} (l : Fin r) {D₁ : Set (Mx k r)} (hD₁ : IsDom k r z z' l.succ D₁) :
    IsDom k r z z' l.castSucc (D0 k r l D₁) := by
  refine ⟨isOpen_cell_domain hD₁.1, ?_⟩
  rintro g hg s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
  obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
  obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hm
  obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hm'
  have d1 := (((((d.leftG hn₁.2).leftU hu₂).leftG (uw_glev hh _)).rightG (uw_glev hh' _)).rightG hn₃.2).rightU hu₃
  have e : h * (u₂ * n₁) * g * (h' * (n₃ * u₃)) = h * (u₂ * (n₁ * g)) * h' * n₃ * u₃ := by
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (mem_cell_domain_iff.2 ⟨_, _, _, _, d1, ?_⟩).2
  have h2 := hD₁.2 g₁ ⟨d.hg, hg₁⟩ (h * n₁) ⟨h, hh, n₁, hn₁, rfl⟩ (h' * n₃) ⟨h', hh', n₃, hn₃, rfl⟩
  have e2 : h * (n₁ * g₁) * h' * n₃ = h * n₁ * g₁ * (h' * n₃) := by simp only [Matrix.mul_assoc]
  rw [e2]; exact h2

theorem famStep {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r) {D₁ : Set (Mx k r)}
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamD z z' π π' l.succ D₁ Φ) :
    FamD z z' π π' l.castSucc (D0 k r l D₁) (JxF l z z' Φ) := by
  refine ⟨fun c hc => ⟨?_, ?_, ?_⟩, ?_⟩
  ·
    intro g hg n hn
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hn
    have d1 := (d.leftG hn₁.2).leftU hu₂
    have hL := (hΦ.1 _ (upd_mem hc d.hc l)).1 g₁ ⟨d.hg, hg₁⟩ n₁ hn₁
    rw [Matrix.mul_assoc, dec_JxF d1, dec_JxF d, hL,
      psi_mul hz (up_nset hu₂) (up_nset (up_conj d.hu hn₁.2)), psi_conjN hz hn₁.1 (up_nset d.hu),
      psi_mul hz (up_nset hu₂) hn₁.1]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg n hn
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hn
    have d1 := (d.rightG hn₃.2).rightU hu₃
    have hR := (hΦ.1 _ (upd_mem hc d.hc l)).2.1 g₁ ⟨d.hg, hg₁⟩ n₃ hn₃
    rw [← Matrix.mul_assoc, dec_JxF d1, dec_JxF d, hR,
      psi_mul hz' (up_nset (up_conj' d.hu' hn₃.2)) (up_nset hu₃), psi_conjN' hz' hn₃.1 (up_nset d.hu'),
      psi_mul hz' hn₃.1 (up_nset hu₃)]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg h hh h' hh'
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    have d1 := (d.leftG (uw_glev hh _)).rightG (uw_glev hh' _)
    have hW := (hΦ.1 _ (upd_mem hc d.hc l)).2.2 g₁ ⟨d.hg, hg₁⟩ h hh h' hh'
    rw [dec_JxF d1, dec_JxF d, hW, psi_conjW hz hh (up_nset d.hu), psi_conjW' hz' hh' (up_nset d.hu')]
    ext v
    simp
  ·
    intro c₀ hc₀ g₀ hg₀
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg₀
    obtain ⟨U₁, F₁, hU₁, hmem, hF₁, hag⟩ := hΦ.2 (Function.update c₀ l c'') (upd_mem hc₀ d.hc l) g₁ ⟨d.hg, hg₁⟩
    have hs0 : IsOpen {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := isOpen_adelicUnipotentTimesIntegralOutsideSet.preimage continuous_snd
    have h1 := smM_snd (k := k) (r := r) {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l}
    have hupd : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => Function.update x.1 l (cF k r l x.2))
        {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := by
      refine contDiffOn_pi.2 fun a => ?_
      by_cases ha : a = l
      · subst ha
        exact (sm_cF (l := a) h1).congr fun x _ => by simp
      · exact ((contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst).contDiffOn.congr fun x _ => by
          simp [ha]
    have hrho : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => rho k r l x.2)
        {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} :=
      (smM_contDiffOn smM_rho).comp contDiff_snd.contDiffOn fun x hx => hx
    have hm := hupd.prodMk hrho
    refine ⟨{x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
        (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁,
      fun x => (psi k r z cStd (uL k r l x.2) * psi k r z' cStd (iH (uL k r l (iH x.2)))) •
        F₁ (Function.update x.1 l (cF k r l x.2), rho k r l x.2),
      hm.continuousOn.isOpen_inter_preimage hs0 hU₁, ⟨d.cell_decomposition_mem, ?_⟩, ?_, ?_⟩
    · show (Function.update c₀ l (cF k r l g₀), rho k r l g₀) ∈ U₁
      rw [d.cF_eq, d.rho_eq]; exact hmem
    · have hs : {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
          (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁ ⊆
          {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := Set.inter_subset_left
      have h1' := smM_snd (k := k) (r := r) ({x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
          (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁)
      have h2 : SmM (fun x : (Fin r → ℂ) × Mx k r => uL k r l x.2) _ := smM_uL h1' fun x hx => hx.1.1
      have h3 : SmM (fun x : (Fin r → ℂ) × Mx k r => uL k r l (iH x.2)) _ := smM_uL (smM_iH h1') fun x hx => hx.1.2
      have h5 := hF₁.comp (hm.mono hs) fun x hx => hx.2
      exact ((sm_psi z cStd h2).mul (sm_psi z' cStd (smM_iH h3))).smul h5
    · intro x hxU hx1 hxG hxD
      obtain ⟨u3, g3, u3', d3⟩ := dec_exists hxG hxU.1.1
      have hy := hag (Function.update x.1 l (cF k r l x.2), rho k r l x.2) hxU.2 (upd_mem hx1 hxU.1.1 l)
        (by show rho k r l x.2 ∈ Glev k r l.succ; rw [d3.rho_eq]; exact d3.hg) hxD.2
      show JxF l z z' Φ x.1 x.2 = _
      unfold JxF
      rw [hy]

end fam

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc
end
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.ChartIntegralLocal

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma step_loc {b : Bool} {X : Mat k r} (hX : inLie k r X) (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1)
    (hψm : AEStronglyMeasurable ψ μ) (G : α → Mat k r → E) (hG1 : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ))
    {g : Mat k r} (hg : g ∈ GV k r) {ε : ℝ} (hε : 0 < ε)
    (hGm : ∀ t ∈ Metric.ball (0 : ℝ) ε, AEStronglyMeasurable (fun ξ => G ξ (cv b X t g)) μ)
    (hG'm : AEStronglyMeasurable (fun ξ => op b X (G ξ) g) μ)
    (β : α → ℝ) (hβ : Integrable β μ)
    (hb0 : ∀ ξ, ‖G ξ g‖ ≤ β ξ) (hb1 : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ ξ, ‖op b X (G ξ) (cv b X t g)‖ ≤ β ξ)
    (Φ : Mat k r → E) (hΦ : ∀ t ∈ Metric.ball (0 : ℝ) ε, Φ (cv b X t g) = ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ) :
    op b X Φ g = ∫ ξ, ψ ξ • op b X (G ξ) g ∂μ := by
  have hcurve : ∀ t, cv b X t g ∈ GV k r := fun t => cv_mem hX hg t
  have hd : ∀ ξ, ∀ g₁ ∈ GV k r, HasDerivAt (fun s : ℝ => G ξ (cv b X s g₁)) (op b X (G ξ) g₁) 0 :=
    fun ξ g₁ hg₁ => (ckOn_diff 0 b (hG1 ξ) hX hg₁).hasDerivAt
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  have h00 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball_self hε
  have hm0 : AEStronglyMeasurable (fun ξ => G ξ (cv b X 0 g)) μ := hGm 0 h00
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (bound := β)
    (F := fun t ξ => ψ ξ • G ξ (cv b X t g)) (x₀ := 0) (s := Metric.ball 0 ε) hs
    (Filter.mem_of_superset hs fun t ht => hψm.smul (hGm t ht))
    (hβ.mono' (hψm.smul hm0) (Eventually.of_forall fun ξ => (hsm ξ _).trans (by rw [cv_zero]; exact hb0 ξ)))
    (F' := fun t ξ => ψ ξ • op b X (G ξ) (cv b X t g))
    (by simp only [cv_zero]; exact hψm.smul hG'm)
    (Eventually.of_forall fun ξ t ht => (hsm ξ _).trans (hb1 t ht ξ)) hβ
    (Eventually.of_forall fun ξ t _ => by
      have e : (fun t' : ℝ => G ξ (cv b X t' g)) = fun t' => G ξ (cv b X (t' - t) (cv b X t g)) := by
        funext t'; rw [← cv_add]; congr 2; ring
      have h2 : HasDerivAt (fun s => G ξ (cv b X s (cv b X t g))) (op b X (G ξ) (cv b X t g)) (t - t) := by
        rw [sub_self]; exact hd ξ _ (hcurve t)
      have h3 := (h2.comp_sub_const t t)
      rw [← e] at h3
      exact h3.const_smul (ψ ξ))
  have e1 : (fun t : ℝ => Φ (cv b X t g)) =ᶠ[𝓝 0] fun t => ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ :=
    Filter.mem_of_superset hs fun t ht => hΦ t ht
  show deriv (fun t : ℝ => Φ (cv b X t g)) 0 = _
  rw [e1.deriv_eq, key.2.deriv]
  simp only [cv_zero]

theorem int_chart_loc (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1) (hψm : AEStronglyMeasurable ψ μ) (h : α → Mat k r → E)
    (mm : ℕ) (hh : ∀ ξ, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (h ξ)) {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {δ : ℝ}
    (hδp : 0 < δ) (hcl : Metric.closedBall (0 : J k r → ℝ) δ ⊆ Dom k r)
    (hM : ∀ w : List (J k r), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      AEStronglyMeasurable (fun ξ => dLR (w.map Lt) [] (h ξ) (chart g0 Y)) μ)
    (β : α → ℝ) (hβ : Integrable β μ)
    (hbd : ∀ w : List (J k r), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∀ ξ,
      ‖dLR (w.map Lt) [] (h ξ) (chart g0 Y)‖ ≤ β ξ) :
    ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => ∫ ξ, ψ ξ • h ξ (chart g0 Y) ∂μ) (Metric.ball 0 δ) := by
  have hΩ : Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r := Metric.ball_subset_closedBall.trans hcl
  have hcomp : IsCompact (Metric.closedBall (0 : J k r → ℝ) δ) := isCompact_closedBall _ _
  have hac : ContinuousOn (fun Y => ∑ i, ‖aC g0 i Y‖) (Metric.closedBall (0 : J k r → ℝ) δ) :=
    continuousOn_finsetSum _ fun i _ => ((aC_cd hg0 i).continuousOn.mono hcl).norm
  obtain ⟨Ba, hBa⟩ := hcomp.exists_bound_of_continuousOn hac
  have hBa' : ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∑ i, ‖aC g0 i Y‖ ≤ Ba := by
    intro Y hY
    have h1 := hBa Y (Metric.ball_subset_closedBall hY)
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  have hunit : ∀ w : List (J k r), ∀ X ∈ w.map Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Lt_unit i
  have hckw : ∀ ξ (w : List (J k r)) (m : ℕ), m + w.length ≤ mm →
      CkOn ((m : ℕ) : ℕ∞) (GV k r) (dLR (w.map Lt) [] (h ξ)) := by
    intro ξ w m hm'
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) m (ckOn_mono (by rw [length_lr]; simp; omega) (hh ξ))
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hbw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ∀ ξ,
      ‖ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)‖ ≤ β ξ := fun w hw Y hY ξ =>
    (hsm ξ _).trans (hbd w hw Y hY ξ)
  have hmw : ∀ (w : List (J k r)), w.length ≤ mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      AEStronglyMeasurable (fun ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) μ := fun w hw Y hY =>
    hψm.smul (hM w hw Y hY)
  set L : List (J k r) → (J k r → ℝ) → E :=
    fun w Y => ∫ ξ, ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y) ∂μ with hL
  have hLc : ∀ w : List (J k r), w.length ≤ mm → ContinuousOn (L w) (Metric.ball (0 : J k r → ℝ) δ) := by
    intro w hw
    refine continuousOn_of_dominated (F := fun Y ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y)) (bound := β)
      (fun Y hY => hmw w hw Y hY) (fun Y hY => Eventually.of_forall fun ξ => hbw w hw Y hY ξ) hβ
      (Eventually.of_forall fun ξ => ?_)
    exact ((cont_chart hg0 (hckw ξ w 0 (by omega))).mono hΩ).const_smul (ψ ξ)
  have hLd : ∀ w : List (J k r), w.length < mm → ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ,
      HasFDerivAt (L w) (∑ i, (aC g0 i Y).smulRight (L (i :: w) Y)) Y := by
    intro w hw Y hY
    have hD : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ,
        HasFDerivAt (fun Y'' => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y''))
          (∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))) Y' := by
      intro ξ Y' hY'
      have h1 := (hasFDeriv_chart hg0 (hckw ξ w 1 (by omega)) (hΩ hY')).const_smul (ψ ξ)
      refine h1.congr_fderiv ?_
      ext1 W
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
        ContinuousLinearMap.smulRight_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
      rfl
    have hβ0 : ∀ ξ, 0 ≤ β ξ := fun ξ =>
      (norm_nonneg _).trans (hbd [] (by simp) 0 (Metric.mem_ball_self hδp) ξ)
    have hF'm : AEStronglyMeasurable (fun ξ => ∑ i, (aC g0 i Y).smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (StrongDual.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).continuous.comp_aestronglyMeasurable
        (hmw (i :: w) (by simp; omega) Y hY)
    have hbF' : ∀ ξ, ∀ Y' ∈ Metric.ball (0 : J k r → ℝ) δ, ‖∑ i, (aC g0 i Y').smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ ≤ Ba * β ξ := by
      intro ξ Y' hY'
      calc _ ≤ ∑ i, ‖(aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y'))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i, ‖aC g0 i Y'‖ * β ξ := Finset.sum_le_sum fun i _ => by
            rw [ContinuousLinearMap.norm_smulRight_apply]
            exact mul_le_mul_of_nonneg_left (hbw (i :: w) (by simp; omega) Y' hY' ξ) (norm_nonneg _)
        _ = (∑ i, ‖aC g0 i Y'‖) * β ξ := by rw [Finset.sum_mul]
        _ ≤ Ba * β ξ := mul_le_mul_of_nonneg_right (hBa' Y' hY') (hβ0 ξ)
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
      (F := fun Y' ξ => ψ ξ • dLR (w.map Lt) [] (h ξ) (chart g0 Y'))
      (F' := fun Y' ξ => ∑ i, (aC g0 i Y').smulRight (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y')))
      (bound := fun ξ => Ba * β ξ) (Metric.isOpen_ball.mem_nhds hY)
      (by filter_upwards [Metric.isOpen_ball.mem_nhds hY] with Y' hY' using hmw w hw.le Y' hY')
      (hβ.mono' (hmw w hw.le Y hY) (Eventually.of_forall fun ξ => hbw w hw.le Y hY ξ))
      hF'm (Eventually.of_forall fun ξ Y' hY' => hbF' ξ Y' hY') (hβ.const_mul Ba)
      (Eventually.of_forall fun ξ Y' hY' => hD ξ Y' hY')
    refine key.congr_fderiv ?_
    have hint : ∀ i, Integrable (fun ξ => ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y)) μ := fun i =>
      hβ.mono' (hmw (i :: w) (by simp; omega) Y hY)
        (Eventually.of_forall fun ξ => hbw (i :: w) (by simp; omega) Y hY ξ)
    have hI : ∀ i, Integrable (fun ξ => (aC g0 i Y).smulRight
        (ψ ξ • dLR ((i :: w).map Lt) [] (h ξ) (chart g0 Y))) μ := fun i =>
      (StrongDual.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integrable_comp (hint i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (StrongDual.smulRightL ℝ (J k r → ℝ) E (aC g0 i Y)).integral_comp_comm (hint i)
  have hAL := ALd (𝔤 := J k r → ℝ) (E := E) Metric.isOpen_ball (aC g0) (fun i => (aC_cd hg0 i).mono hΩ) mm L
    hLc hLd
  exact hAL.congr fun Y _ => rfl

theorem ck_at_of_chart {F : Mat k r → E} {mm : ℕ} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {δ : ℝ} (hδ : 0 < δ)
    (hAL : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Metric.ball 0 δ)) :
    ∃ (U : Set (Mat k r)) (F' : Mat k r → E), IsOpen U ∧ g0 ∈ U ∧
      ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) F' U ∧ ∀ g ∈ U, g ∈ GV k r → F g = F' g := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  set U := Sr g0 ∩ Formalism.FourierDecayAlt.P.Ux10.rho g0 ⁻¹' Metric.ball (0 : J k r → ℝ) δ with hUdef
  have hUo : IsOpen U :=
    (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) Metric.isOpen_ball
  have hg0U : g0 ∈ U := by
    have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
    refine ⟨?_, ?_⟩
    · show IsUnit (g0 * g0⁻¹ + 1).det
      rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
    · show Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 ∈ Metric.ball (0 : J k r → ℝ) δ
      have h3 : Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 = 0 := by
        funext i
        simp only [Formalism.FourierDecayAlt.P.Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
        exact co_zero i
      rw [h3]; exact Metric.mem_ball_self hδ
  refine ⟨U, fun x => F (chart g0 (Formalism.FourierDecayAlt.P.Ux10.rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · have h4 : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (Formalism.FourierDecayAlt.P.Ux10.rho g0) U :=
      ((rho_cd g0).mono Set.inter_subset_left).of_le (by exact_mod_cast le_top)
    exact hAL.comp h4 (by intro x hx; exact hx.2)
  · intro x hx hxG
    have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
    obtain ⟨hl, -, hk⟩ := iot_facts hh hx.1
    show F x = F (kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0)
    rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

end Formalism.FourierDecayAlt.P.ChartIntegralLocal
end
end
