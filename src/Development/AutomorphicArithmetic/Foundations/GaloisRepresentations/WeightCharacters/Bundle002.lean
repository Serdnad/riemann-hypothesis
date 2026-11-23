module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle213
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.dom_of :
    UpperTheory.Gal.Wt.Dom := by
  classical
  intro a κ f hf
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ a a κ.natW := hf
  clear hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ a a κ.natW] at hf'
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm k
    have h := (Formalism.GradedWeylDivisibility.bidetDominance ℂ a a K sz hsz I m hm).1 k
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm k
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx m h k
    · exact hy m h k
  | smul c x _ hx =>
    intro m hm k
    exact hx m (MvPolynomial.support_smul hm) k
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.evLem_of :
    UpperTheory.Gal.Wt.EvLem := by
  intro M X Z _ _ _ ev hsep T Φ hT L
  let W : Submodule ℂ (Module.Dual ℂ M) := Submodule.span ℂ (Set.range ev)
  have hbot : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Submodule.mem_dualCoannihilator] at hm
    exact (Submodule.mem_bot ℂ).2 (hsep m fun x => hm _ (Submodule.subset_span ⟨x, rfl⟩))
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hbot, Submodule.dualAnnihilator_bot]
  let φ : Module.Dual ℂ M →ₗ[ℂ] (Z → ℂ) :=
    { toFun := fun l z => l (Φ z)
      map_add' := fun a b => by
        ext z
        simp
      map_smul' := fun c a => by
        ext z
        simp }
  have hle : W ≤ T.comap φ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hT x
  have hL : L ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  exact hle hL
end

section

noncomputable section

namespace UpperTheory.Gal.Wt

private theorem pow_mem_le {s m : ℤ} (h : m ≤ s) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpLe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem pow_mem_ge {s m : ℤ} (h : s ≤ m) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpGe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem circle_mul_mem_of_mem_span_of_mem_span {S T : Set (Circle → ℂ)} {P : Submodule ℂ (Circle → ℂ)}
    (h : ∀ f ∈ S, ∀ g ∈ T, (fun z => f z * g z) ∈ P) {f g : Circle → ℂ}
    (hf : f ∈ Submodule.span ℂ S) (hg : g ∈ Submodule.span ℂ T) :
    (fun z => f z * g z) ∈ P := by
  induction hf using Submodule.span_induction with
  | mem f hfS =>
    induction hg using Submodule.span_induction with
    | mem g hgT => exact h f hfS g hgT
    | zero =>
      have e : (fun z => f z * (0 : Circle → ℂ) z) = 0 := by
        funext z
        simp
      rw [e]
      exact P.zero_mem
    | add g₁ g₂ _ _ h₁ h₂ =>
      have e : (fun z => f z * (g₁ + g₂) z) = (fun z => f z * g₁ z) + (fun z => f z * g₂ z) := by
        funext z
        simp [mul_add]
      rw [e]
      exact P.add_mem h₁ h₂
    | smul c g _ h₁ =>
      have e : (fun z => f z * (c • g) z) = c • (fun z => f z * g z) := by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact P.smul_mem c h₁
  | zero =>
    have e : (fun z => (0 : Circle → ℂ) z * g z) = 0 := by
      funext z
      simp
    rw [e]
    exact P.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ =>
    have e : (fun z => (f₁ + f₂) z * g z) = (fun z => f₁ z * g z) + (fun z => f₂ z * g z) := by
      funext z
      simp [add_mul]
    rw [e]
    exact P.add_mem h₁ h₂
  | smul c f _ h₁ =>
    have e : (fun z => (c • f) z * g z) = c • (fun z => f z * g z) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact P.smul_mem c h₁

private theorem circle_comp_inv_mem_of_mem_span {S : Set (Circle → ℂ)} {P : Submodule ℂ (Circle → ℂ)}
    (h : ∀ f ∈ S, (fun z : Circle => f z⁻¹) ∈ P) {f : Circle → ℂ}
    (hf : f ∈ Submodule.span ℂ S) : (fun z : Circle => f z⁻¹) ∈ P := by
  induction hf using Submodule.span_induction with
  | mem f hfS => exact h f hfS
  | zero =>
    have e : (fun z : Circle => (0 : Circle → ℂ) z⁻¹) = 0 := by
      funext z
      simp
    rw [e]
    exact P.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ =>
    have e : (fun z : Circle => (f₁ + f₂) z⁻¹) = (fun z => f₁ z⁻¹) + (fun z => f₂ z⁻¹) := by
      funext z
      simp
    rw [e]
    exact P.add_mem h₁ h₂
  | smul c f _ h₁ =>
    have e : (fun z : Circle => (c • f) z⁻¹) = c • (fun z => f z⁻¹) := by
      funext z
      simp
    rw [e]
    exact P.smul_mem c h₁

private theorem circle_zpow_mul_zpow_eq_zpow_add (m n : ℤ) :
    (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) = fun z : Circle => (z : ℂ) ^ (m + n) := by
  funext z
  rw [zpow_add₀ (Circle.coe_ne_zero z)]

private theorem circle_inv_zpow_eq_zpow_neg (m : ℤ) :
    (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) = fun z : Circle => (z : ℂ) ^ (-m) := by
  funext z
  rw [Circle.coe_inv, inv_zpow, zpow_neg]

theorem expBasic_of : ExpBasic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_le (by omega)
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_ge (by omega)
  · intro s t hst
    constructor
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hm.trans hst, rfl⟩
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hst.trans hm, rfl⟩
  · intro c m
    exact ⟨(ExpLe m).smul_mem c (pow_mem_le le_rfl), (ExpGe m).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro c
    have e : (fun _ : Circle => c) = c • (fun z : Circle => (z : ℂ) ^ (0 : ℤ)) := by
      funext z
      simp
    rw [e]
    exact ⟨(ExpLe 0).smul_mem c (pow_mem_le le_rfl), (ExpGe 0).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro s f
    constructor
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_ge (by omega)
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_le (by omega)

end UpperTheory.Gal.Wt

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

namespace UpperTheory.Gal.Wt.KaplanskyFiniteness

variable {k : Type} [NormedField k] [IsUltrametricDist k]

private lemma norm_unit_le (c x : k) (hc : c ≠ 0) (h : ‖x‖ ≤ ‖c‖) : ‖1 - c⁻¹ * x‖ ≤ 1 := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
  rw [norm_neg, norm_mul, norm_inv, inv_mul_le_iff₀ hc', mul_one]
  exact h

private lemma norm_le_of_near (c x : k) (h : ‖x - c‖ ≤ ‖c‖ / 2) : ‖x‖ ≤ ‖c‖ := by
  have hx : x = (x - c) + c := by ring
  rw [hx]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans ?_) le_rfl)
  have := norm_nonneg c
  linarith

private lemma pow_near {u : k} {ε : ℝ} (hε : 0 ≤ ε) (hu : ‖u‖ ≤ 1) (h : ‖u - 1‖ ≤ ε) (n : ℕ) :
    ‖u ^ n - 1‖ ≤ ε := by
  induction n with
  | zero => simpa using hε
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h)
    rw [norm_mul]
    calc ‖u‖ * ‖u ^ n - 1‖ ≤ 1 * ε := mul_le_mul hu ih (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

private lemma eval_bound (p : Polynomial k) (x : k) (R : ℝ) (hx : ‖x‖ ≤ R) :
    ‖p.eval x‖ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * R ^ i := by
  rw [Polynomial.eval_eq_sum_range]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx i) (norm_nonneg _)

private lemma exists_pow_small (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ n : ℕ, M * (1 / 2 : ℝ) ^ n ≤ ε := by
  have hM1 : 0 < M + 1 := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hM1) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  calc M * (1 / 2 : ℝ) ^ n ≤ (M + 1) * (1 / 2 : ℝ) ^ n := by nlinarith
    _ ≤ (M + 1) * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hn.le hM1.le
    _ = ε := by field_simp

end UpperTheory.Gal.Wt.KaplanskyFiniteness

open UpperTheory.Gal.Wt.KaplanskyFiniteness in
theorem UpperTheory.Gal.Wt.kaplFin_of :
    UpperTheory.Gal.Wt.KaplFin := by
  classical
  intro k _ _ s δ ε hδ hε hε1
  refine Finset.induction_on_max_value (fun c : k => ‖c‖) s ?_ ?_
  · intro _
    refine ⟨1, fun x _ => by simp, fun c hc => absurd hc (Finset.notMem_empty c), fun x _ => ?_⟩
    simpa using hε.le
  · intro c s _ hmax ih hs
    obtain ⟨p', h1, h2, h3⟩ := ih fun c' hc' => hs c' (Finset.mem_insert_of_mem hc')
    have hδc : δ ≤ ‖c‖ := hs c (Finset.mem_insert_self c s)
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hδc
      linarith
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    obtain ⟨n, hn⟩ := exists_pow_small (∑ i ∈ Finset.range (p'.natDegree + 1), ‖p'.coeff i‖ * ‖c‖ ^ i) ε
      (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) hε
    have hev : ∀ x, ((p' * (1 - Polynomial.C c⁻¹ * Polynomial.X) ^ n).eval x) =
        p'.eval x * (1 - c⁻¹ * x) ^ n := by
      intro x
      simp [Polynomial.eval_mul, Polynomial.eval_pow]
    refine ⟨p' * (1 - Polynomial.C c⁻¹ * Polynomial.X) ^ n, ?_, ?_, ?_⟩
    · intro x hx
      rw [hev, norm_mul, norm_pow]
      have hu := norm_unit_le c x hc0 (hx.trans hδc)
      calc ‖p'.eval x‖ * ‖1 - c⁻¹ * x‖ ^ n ≤ 1 * 1 :=
            mul_le_mul (h1 x hx) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) zero_le_one
        _ = 1 := one_mul 1
    · intro c' hc' x hx
      rw [hev, norm_mul, norm_pow]
      rcases Finset.mem_insert.mp hc' with rfl | hc's
      · have hxc := norm_le_of_near c' x hx
        have hu : ‖1 - c'⁻¹ * x‖ ≤ 1 / 2 := by
          have e : 1 - c'⁻¹ * x = c'⁻¹ * (c' - x) := by field_simp
          rw [e, norm_mul, norm_inv, norm_sub_rev, inv_mul_le_iff₀ hcpos]
          linarith
        calc ‖p'.eval x‖ * ‖1 - c'⁻¹ * x‖ ^ n
            ≤ (∑ i ∈ Finset.range (p'.natDegree + 1), ‖p'.coeff i‖ * ‖c'‖ ^ i) * (1 / 2 : ℝ) ^ n :=
              mul_le_mul (eval_bound p' x _ hxc) (pow_le_pow_left₀ (norm_nonneg _) hu n)
                (by positivity) ((norm_nonneg _).trans (eval_bound p' x _ hxc))
          _ ≤ ε := hn
      · have hxc : ‖x‖ ≤ ‖c‖ := (norm_le_of_near c' x hx).trans (hmax c' hc's)
        have hu := norm_unit_le c x hc0 hxc
        calc ‖p'.eval x‖ * ‖1 - c⁻¹ * x‖ ^ n ≤ ε * 1 :=
              mul_le_mul (h2 c' hc's x hx) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) hε.le
          _ = ε := mul_one ε
    · intro x hx
      have hxδ : ‖x‖ ≤ δ := hx.trans (by nlinarith)
      have hu := norm_unit_le c x hc0 (hxδ.trans hδc)
      have hu1 : ‖(1 - c⁻¹ * x) - 1‖ ≤ ε := by
        have e : (1 - c⁻¹ * x) - 1 = -(c⁻¹ * x) := by ring
        rw [e, norm_neg, norm_mul, norm_inv, inv_mul_le_iff₀ hcpos]
        calc ‖x‖ ≤ δ * ε := hx
          _ ≤ ‖c‖ * ε := mul_le_mul_of_nonneg_right hδc hε.le
      have hun := pow_near hε.le hu hu1 n
      have e : p'.eval x * (1 - c⁻¹ * x) ^ n - 1 =
          p'.eval x * ((1 - c⁻¹ * x) ^ n - 1) + (p'.eval x - 1) := by ring
      rw [hev, e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h3 x hx))
      rw [norm_mul]
      calc ‖p'.eval x‖ * ‖(1 - c⁻¹ * x) ^ n - 1‖ ≤ 1 * ε :=
            mul_le_mul (h1 x hxδ) hun (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.kapl_of :
    UpperTheory.Gal.Wt.KaplFin → UpperTheory.Gal.Wt.Kapl := by
  intro hfin k _ _ Y hY δ ε hδ hε hε1
  have hY' : IsCompact (Y ∩ {x : k | δ ≤ ‖x‖}) :=
    hY.inter_right (isClosed_le continuous_const continuous_norm)
  have hnhds : ∀ c ∈ Y ∩ {x : k | δ ≤ ‖x‖}, Metric.closedBall c (‖c‖ / 2) ∈ nhds c := by
    intro c hc
    have hc' : δ ≤ ‖c‖ := hc.2
    exact Metric.closedBall_mem_nhds c (by linarith)
  obtain ⟨s, hs, hcov⟩ := hY'.elim_nhds_subcover (fun c => Metric.closedBall c (‖c‖ / 2)) hnhds
  obtain ⟨p, h1, h2, h3⟩ := hfin k s δ ε hδ hε hε1 (fun c hc => (hs c hc).2)
  have hbig : ∀ x ∈ Y, δ ≤ ‖x‖ → ‖p.eval x‖ ≤ ε := by
    intro x hx hxδ
    have hmem := hcov ⟨hx, hxδ⟩
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨c, hc, hxc⟩ := hmem
    exact h2 c hc x (by simpa [dist_eq_norm] using hxc)
  refine ⟨p, fun x hx => ?_, hbig, h3⟩
  rcases le_total ‖x‖ δ with h | h
  · exact h1 x h
  · exact (hbig x hx h).trans hε1
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.autCrit_of :
    UpperTheory.Gal.Wt.AutCrit := by
  intro E _ _ _ a C hLev φ hL hC hI S hS hSub
  obtain ⟨N, hNo, hN1, hNC⟩ := hLev.isOpen
  set Wn : Set (UA E a) := GlobalTheory.EllU.finPart ⁻¹' N with hWn
  have hWo : IsOpen Wn := hNo.preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E a) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ N
    rw [map_one]; exact hN1
  have hkey : ∀ g, ∀ w ∈ Wn, φ (g * w) = φ (g * ((GlobalTheory.EllU.finPart w)⁻¹ * w)) := by
    intro g w hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hNC ⟨hw, GlobalTheory.EllU.finPart_mem w⟩
    have hx := GlobalTheory.EllU.inv_finPart_mul_mem w
    have hcm := GlobalTheory.DefU.fin_mul_inf (GlobalTheory.EllU.finPart_mem w) hx
    have e : g * w = g * ((GlobalTheory.EllU.finPart w)⁻¹ * w) * GlobalTheory.EllU.finPart w := by
      rw [mul_assoc, ← hcm]; group
    rw [e, hC _ hkC]
  refine ⟨?_, hL, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    have hc : Continuous fun y : UA E a => g⁻¹ * y := continuous_const.mul continuous_id
    have hX : Continuous fun y : UA E a => (⟨(GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y),
        GlobalTheory.EllU.inv_finPart_mul_mem _⟩ : infU E a) :=
      Continuous.subtype_mk (((GlobalTheory.EllU.continuous_finPart.comp hc).inv).mul hc) _
    have h0 : ContinuousAt (fun y : UA E a => φ (g * ((GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y)))) g :=
      ((hI g).comp hX).continuousAt
    refine h0.congr ?_
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    have := hkey g _ hy
    rw [mul_inv_cancel_left] at this
    exact this.symm
  · refine GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds ((RU E a).comp (finU (E := E) (n := a)).subtype) _ ?_
    have ho : IsOpen ((Subtype.val : finU (E := E) (n := a) → UA E a) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    have hk' : (k : UA E a) ∈ C := by
      refine hNC ⟨?_, k.2⟩
      have : GlobalTheory.EllU.finPart (k : UA E a) ∈ N := hk
      rwa [GlobalTheory.EllU.finPart_of_finU k.2] at this
    funext g
    exact hC _ hk' g
  · haveI := hS
    refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hSub k k.2
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.qR_of :
    UpperTheory.Gal.Wt.QR := by
  intro a y
  obtain ⟨k, hk, b, hg, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular (y : Matrix (Fin a) (Fin a) ℂ) y.isUnit
  let u : Matrix.unitaryGroup (Fin a) ℂ := ⟨k, hk⟩
  have hu : ((unitaryIncl a u : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = k := rfl
  refine ⟨u, (unitaryIncl a u)⁻¹ * y, ?_, (mul_inv_cancel_left _ _).symm⟩
  have hbm : (((unitaryIncl a u)⁻¹ * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = b := by
    rw [Units.val_mul, hg, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  intro i j hij
  rw [hbm]
  exact hb hij
end
