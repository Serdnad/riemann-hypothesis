module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SlopeOfBinomCombGen
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CollapseExponent
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

def lsup {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) : MvPolynomial σ K →ₗ[K] MvPolynomial τ K :=
  (basisMonomials σ K).constr K φ

theorem lsup_monomial {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) (α : σ →₀ ℕ) (c : K) :
    lsup φ (monomial α c) = c • φ α := by
  have h : monomial α c = c • (basisMonomials σ K) α := by simp [smul_monomial]
  rw [h, map_smul, lsup, Module.Basis.constr_basis]

theorem lsup_apply {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) (F : MvPolynomial σ K) :
    lsup φ F = ∑ α ∈ F.support, F.coeff α • φ α := by
  conv_lhs => rw [F.as_sum]

  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => lsup_monomial φ α _

theorem dg_eq_lsup {σ : Type} (f : (σ →₀ ℕ) → K) : dg f = lsup fun α => monomial α (f α) := rfl

theorem dg_apply {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by
  rw [dg_eq_lsup, lsup_apply]
  exact Finset.sum_congr rfl fun α _ => by rw [smul_monomial, smul_eq_mul, mul_comm]

def ddivL {σ : Type} (M : σ →₀ ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  lsup fun α => if M ≤ α then monomial (α - M) (α.prod fun x k => (k.choose (M x) : K)) else 0

theorem ddiv_eq {σ : Type} (M : σ →₀ ℕ) (F : MvPolynomial σ K) : ddiv M F = ddivL M F := by
  rw [ddivL, lsup_apply, ddiv]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [smul_monomial, smul_eq_mul]
  · rw [smul_zero]

theorem ddiv_monomial {σ : Type} (M α : σ →₀ ℕ) (c : K) :
    ddiv M (monomial α c) =
      if M ≤ α then monomial (α - M) (c * α.prod fun x k => (k.choose (M x) : K)) else 0 := by
  rw [ddiv_eq, ddivL, lsup_monomial]
  split_ifs
  · rw [smul_monomial, smul_eq_mul]
  · rw [smul_zero]

theorem ddiv_add {σ : Type} (M : σ →₀ ℕ) (F G : MvPolynomial σ K) :
    ddiv M (F + G) = ddiv M F + ddiv M G := by simp only [ddiv_eq, map_add (f := _)]

theorem ddiv_smul {σ : Type} (M : σ →₀ ℕ) (a : K) (F : MvPolynomial σ K) :
    ddiv M (a • F) = a • ddiv M F := by simp only [ddiv_eq, map_smul]

theorem ddiv_sum {σ ι : Type} (M : σ →₀ ℕ) (s : Finset ι) (f : ι → MvPolynomial σ K) :
    ddiv M (∑ i ∈ s, f i) = ∑ i ∈ s, ddiv M (f i) := by simp only [ddiv_eq, map_sum]

theorem coeff_ddiv {σ : Type} (M β : σ →₀ ℕ) (F : MvPolynomial σ K) :
    (ddiv M F).coeff β = F.coeff (β + M) * (β + M).prod fun x k => (k.choose (M x) : K) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [ddiv_monomial, coeff_monomial]
    by_cases h : M ≤ α
    · rw [ite_eq_left h, coeff_monomial]
      by_cases h2 : α - M = β
      · have : α = β + M := by rw [← h2, tsub_add_cancel_of_le h]
        rw [ite_eq_left h2, ite_eq_left this, this]
      · have : ¬ α = β + M := by
          intro h3; apply h2; rw [h3, add_tsub_cancel_right]
        rw [ite_eq_right h2, ite_eq_right this, zero_mul]
    · have : ¬ α = β + M := by
        intro h3; apply h; rw [h3]; exact le_add_self
      rw [ite_eq_right h, ite_eq_right this, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_mul]
  | add p q hp hq =>
    simp only [ddiv_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_mul]

namespace TwistData

variable (D : TwistData K)

def digitPartL (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) :
    MvPolynomial (D.OL × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun α => if D.InClass p ρ α then monomial (D.liftE p α) 1 else 0

theorem digitPart_eq (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ F = D.digitPartL p ρ F := by
  rw [digitPartL, lsup_apply, digitPart]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [smul_monomial, smul_eq_mul, mul_one]
  · rw [smul_zero]

theorem digitPart_monomial (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (α : D.EA) (c : K) :
    D.digitPart p ρ (monomial α c) = if D.InClass p ρ α then monomial (D.liftE p α) c else 0 := by
  rw [digitPart_eq, digitPartL, lsup_monomial]
  split_ifs
  · rw [smul_monomial, smul_eq_mul, mul_one]
  · rw [smul_zero]

theorem digitPart_add (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (F G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (F + G) = D.digitPart p ρ F + D.digitPart p ρ G := by
  simp only [digitPart_eq, map_add (f := _)]

theorem digitPart_smul (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (a : K) (F : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (a • F) = a • D.digitPart p ρ F := by
  simp only [digitPart_eq, map_smul]

theorem digitPart_sum {ι : Type} (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (s : Finset ι)
    (f : ι → MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (∑ i ∈ s, f i) = ∑ i ∈ s, D.digitPart p ρ (f i) := by

  simp only [digitPart_eq, map_sum]

theorem gaAct_eq (G : MvPolynomial (D.OL × Fin D.r) K) : D.gaAct G = dg D.ga G := by
  rw [dg_apply, gaAct]

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def TLset (j : Fin D.J) (m : Fin D.r) : Finset D.ML :=
  (D.LLj j).image D.mb ∪ (univ.filter fun m' : Fin D.r => m < m').image fun m' => D.mlab (j, m')

def YPset (j : Fin D.J) (m : Fin D.r) : Finset D.ML :=
  (D.LLj j).image D.mb ∪ (univ.filter fun m' : Fin D.r => m < m').image fun m' => D.mtp (j, m')

def SegL (j : Fin D.J) (i : D.ML) : Prop :=
  (∃ b, D.seg b = j ∧ i = D.mb b) ∨ (∃ m, i = D.mlab (j, m)) ∨ (∃ m, i = D.mtp (j, m))

def PreE (j : Fin D.J) (ζ : D.EM) : Prop :=
  (∀ b, D.seg b = j → ldeg ζ (D.mb b) = D.dB b) ∧ (∀ m, ldeg ζ (D.mlab (j, m)) = D.dT (j, m)) ∧
  (∀ m a, ζ (D.mtp (j, m), a) = 0)

def PostE (j : Fin D.J) (ζ : D.EM) : Prop :=
  (∀ b, D.seg b = j → ldeg ζ (D.mb b) = D.dB b) ∧
  (∀ m, ldeg ζ (D.mlab (j, m)) + ldeg ζ (D.mtp (j, m)) = D.dT (j, m)) ∧
  (∀ m, ldeg ζ (D.mtp (j, m)) ≤ D.dLL j) ∧
  (∀ m : Fin D.r, m.val = 0 → ∀ a, ζ (D.mtp (j, m), a) = 0)

end TwistData

def SegStep (K : Type) [Field K] [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) : Prop :=
  DVRHyp v p → ∀ D : TwistData K, 0 < D.r → 0 < D.J → ∀ j : Fin D.J,
    ∃ Th : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K,
      (∀ ζ : D.EM, D.PreE j ζ → Integral v (Th (monomial ζ 1))) ∧
      (∀ ζ : D.EM, D.PreE j ζ → D.ph p (Th (monomial ζ 1)) = D.ph p (monomial ζ 1)) ∧
      (∀ ζ : D.EM, D.PreE j ζ → ∀ ζ' ∈ (Th (monomial ζ 1)).support,
        D.PostE j ζ' ∧ ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) ∧
      (∀ Z : MvPolynomial (D.ML × Fin D.r) K, Integral v Z → (∀ ζ ∈ Z.support, D.PreE j ζ) →
        ∀ (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
          vala D.msg (D.TLset j m) θ Z → vala D.msg (D.YPset j m) θ (Th Z)) ∧
      (∀ S : Finset D.ML, (∀ i ∈ S, ¬ D.SegL j i) → ∀ Z : MvPolynomial (D.ML × Fin D.r) K,
        valS D.msg S Z ≤ valS D.msg S (Th Z))

end Formalism.MainNotions.PlaneGram
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def embU (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (x : D.OL × Fin D.r) (ζ : D.EM) : ℕ :=
  Sum.elim (fun b => ζ (D.mb b, x.2)) (fun t => ρ t x.2 + D.P p t * ζ (D.mw t, x.2)) x.1

def embE (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => D.embU p ρ x ζ

theorem substituted_exponent_eq_embedded (p : ℕ) (ζ : D.EM) : D.collapseExponent p ζ = D.embE p (D.labF ζ) ζ := rfl

def gaR (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ρ : D.Tau → Fin D.r → ℕ) (ε : ℤ)
    (ζ : D.EM) : K :=
  D.ga (D.embE p ρ ζ) ^ ε * ∏ t, gam t (ρ t) (D.wF ζ t) ^ ε

theorem gaR_one (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) :
    D.gaR p gam (D.labF ζ) 1 ζ = D.gaP p gam ζ := by
  simp only [gaR, gaP, zpow_one, substituted_exponent_eq_embedded]

theorem gaR_neg_one (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) :
    D.gaR p gam (D.labF ζ) (-1) ζ = (D.gaP p gam ζ)⁻¹ := by
  simp only [gaR, gaP, zpow_neg_one, substituted_exponent_eq_embedded, Finset.prod_inv_distrib, mul_inv]

end TwistData

section

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

abbrev CostM (D : TwistData K) : ℕ → (D.EM → K) → Prop := CostV (K := K) (r := D.r) D.msg Set.univ

theorem costM_ok (D : TwistData K) : CostOK (CostM D) :=
  costV_ok _ _ (fun _ _ _ _ _ h1 h2 => vala_add h1 h2) (fun _ _ _ a _ h => vala_smul a h)

theorem costM_choose (hV2 : V2 K) (D : TwistData K) (hr : 0 < D.r) (x : D.ML × Fin D.r) (k : ℕ) :
    CostM D k (fun α => ((α x).choose k : K)) := by
  haveI : NeZero D.r := ⟨hr.ne'⟩
  intro S _ θ F h
  exact vala_dg_choose hV2 x k h

theorem exists_approx_gaR (hV2 : V2 K) (D : TwistData K) (hV : D.Valid v p)
    (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K)
    (hDig : D.DigOK v p cst gam) (ρ : D.Tau → Fin D.r → ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ g : D.EM → K, (∀ ζ, 0 ≤ v (g ζ)) ∧ CostM D (12 * D.c) g ∧
      ((∀ t a, ρ t a < D.P p t) → ∀ ζ, ((D.c : ℕ) : WithTop ℚ) ≤ v (D.gaR p gam ρ ε ζ - g ζ)) := by
  have hC := costM_ok D
  have hch := costM_choose hV2 D hV.1
  by_cases hρ : ∀ t a, ρ t a < D.P p t
  · obtain ⟨hga0, hga⟩ := hV.2.2.2.2.2.2
    obtain ⟨T, lam, hlam, hcong⟩ := hga ε hε
    obtain ⟨g1, a1, a2, a3⟩ := approx_of_trunc_gen (v := v) hC (D.embU p ρ) (by
        rintro ⟨i, a⟩ k
        rcases i with b | t
        · exact hch (D.mb b, a) k
        · exact cost_choose_affine hC (fun ζ => ζ (D.mw t, a)) (hch (D.mw t, a)) (ρ t a) (D.P p t) k)
      T lam hlam (fun ζ => D.ga (D.embE p ρ ζ) ^ ε) (fun ζ => hcong (D.embE p ρ ζ))
    obtain ⟨T', lam', hlam', hcong'⟩ := hDig.2 ρ hρ ε hε
    obtain ⟨g2, b1, b2, b3⟩ := approx_of_trunc_gen (v := v) hC
      (fun (x : D.Tau × Fin D.r) (ζ : D.EM) => ζ (D.mw x.1, x.2)) (fun x k => hch (D.mw x.1, x.2) k)
      T' lam' hlam' (fun ζ => (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε)
      (fun ζ => hcong' (fun x => ζ (D.mw x.1, x.2)))
    have u2 : ∀ ζ : D.EM, v ((∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε) = 0 := fun ζ =>
      v_unit_zpow v (Finset.prod_induction _ (fun x => v x = 0) (fun a b ha hb => v_unit_mul v ha hb)
        v.map_one fun t _ => ((hDig.1 t (ρ t) (hρ t)).2 _).1) ε
    refine ⟨fun ζ => g1 ζ * g2 ζ, fun ζ => v_mul_nonneg (a1 ζ) (b1 ζ), ?_, fun _ ζ => ?_⟩
    · have := hC.mul _ _ _ _ a3 b3
      have e : 6 * D.c + 6 * D.c = 12 * D.c := by ring
      rwa [e] at this
    · have e : D.gaR p gam ρ ε ζ - g1 ζ * g2 ζ =
          (D.ga (D.embE p ρ ζ) ^ ε - g1 ζ) * (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε +
            g1 ζ * ((∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε - g2 ζ) := by
        have e2 : ∏ t, gam t (ρ t) (D.wF ζ t) ^ ε = (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε :=
          Finset.prod_zpow _ _ _
        simp only [TwistData.gaR]
        rw [e2]; ring
      rw [e]
      exact v_add_ge (v_mul_ge_left (a2 ζ) (u2 ζ).ge) (v_mul_ge_right (a1 ζ) (b2 ζ))
  · refine ⟨fun _ => 1, fun _ => by simp, ?_, fun h => absurd h hρ⟩
    exact hC.mono 0 _ _ (Nat.zero_le _) hC.one

theorem eOut_of_mem_image {L : Type} [DecidableEq L] {r : ℕ} (out : L → Prop) [DecidablePred out]
    (F : MvPolynomial (L × Fin r) K) {μ : L × Fin r →₀ ℕ} (hμ : μ ∈ F.support.image (eOut out)) :
    eOut out μ = μ := by
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hμ
  exact eOut_eOut out α

theorem vala_dg_labels (D : TwistData K) (gg : (D.Tau → Fin D.r → ℕ) → D.EM → K) (n : ℕ)
    (hgg : ∀ ρ, CostM D n (gg ρ)) (S : Finset D.ML) (hS : ∀ t, D.mlab t ∉ S) (θ : ℝ)
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZ : vala D.msg S θ Z) :
    vala D.msg S (θ - n) (dg (fun ζ => gg (D.labF ζ) ζ) Z) := by
  set out : D.ML → Prop := fun i => ∃ t, i = D.mlab t with hout
  letI : DecidablePred out := Classical.decPred _
  have hoS : ∀ i ∈ S, ¬ out i := by
    rintro i hi ⟨t, rfl⟩; exact hS t hi

  conv => rw [sum_coefOut out Z, map_sum]
  refine vala_sum _ _ fun μ hμ => ?_
  have e : dg (fun ζ => gg (D.labF ζ) ζ) (monomial μ 1 * coefOut out μ Z) =
      dg (gg (D.labF μ)) (monomial μ 1 * coefOut out μ Z) := by
    refine dg_congr fun α hα => ?_
    have hlab : D.labF α = D.labF μ := by
      rw [mem_support_iff, coeff_monomial_mul'] at hα
      by_cases hle : μ ≤ α
      · rw [if_pos hle, one_mul] at hα
        have h0 := eOut_eq_zero_of_mem_support_coefOut out (mem_support_iff.mpr hα)
        funext t a
        have h1 : (α - μ) (D.mlab t, a) = 0 := by
          have := DFunLike.congr_fun h0 (D.mlab t, a)
          rw [eOut_apply, if_pos ⟨t, rfl⟩] at this
          simpa using this
        have h2 : μ (D.mlab t, a) ≤ α (D.mlab t, a) := hle _
        rw [Finsupp.tsub_apply] at h1
        simp only [TwistData.labF]
        omega
      · rw [if_neg hle] at hα; exact absurd rfl hα
    rw [hlab]
  rw [e]
  refine hgg _ S (Set.mem_univ _) θ _ ?_
  refine vala_mul_left_nonneg (valS_monomial_nonneg_of_free _ _ ?_) (vala_coefOut out hoS _ hZ)
  intro i hi a
  rw [← eOut_of_mem_image out Z hμ, eOut_apply, if_neg (hoS i hi)]

theorem stepG_of (hV2 : V2 K) : StepG K v p := by
  intro _hD D hV cst gam hDig
  have Hp := fun ρ => exists_approx_gaR hV2 D hV cst gam hDig ρ 1 (Or.inl rfl)
  have Hm := fun ρ => exists_approx_gaR hV2 D hV cst gam hDig ρ (-1) (Or.inr rfl)
  choose gp hp1 hp2 hp3 using Hp
  choose gm hm1 hm2 hm3 using Hm
  refine ⟨fun ζ => gp (D.labF ζ) ζ, fun ζ => gm (D.labF ζ) ζ, fun ζ => hp1 _ ζ, fun ζ => hm1 _ ζ, ?_, ?_⟩
  · intro ζ hζ
    constructor
    · have := hp3 (D.labF ζ) hζ ζ
      rw [D.gaR_one, AddValuation.map_sub_swap] at this
      exact this
    · have := hm3 (D.labF ζ) hζ ζ
      rw [D.gaR_neg_one, AddValuation.map_sub_swap] at this
      exact this
  · intro S hS θ Z hZ
    have e : θ - 12 * (D.c : ℝ) = θ - ((12 * D.c : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    exact ⟨vala_dg_labels D gp _ hp2 S hS θ Z hZ, vala_dg_labels D gm _ hm2 S hS θ Z hZ⟩

end

end Formalism.MainNotions.PlaneGram
end
end
