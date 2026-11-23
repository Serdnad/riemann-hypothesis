module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PCharpolyRootLift
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle076
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ChooseLePowDivFactorial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace Conductor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) : Ω := ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹

theorem invMon_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ ε : K → ℕ) :
    invMon y c (δ + ε) = invMon y c δ * invMon y c ε := by
  rw [invMon, invMon, invMon, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add, mul_inv]

theorem invMon_sum {β : Type} (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (s : Finset β) (δ : β → K → ℕ) :
    ∏ b ∈ s, invMon y c (δ b) = invMon y c (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [invMon]
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, invMon_add]

theorem prod_zpow_eq_invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ)) = invMon y c δ := by
  simp [invMon, zpow_neg, zpow_natCast]

theorem form_mul_invMon_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {δ : K → ℕ} {g : MRing ι}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g δ) : aeval y g * invMon y c δ ∈ chartRingZ y c := by
  rw [← prod_zpow_eq_invMon, NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ,
    Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : invMon y c d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => inv_ne_zero (pow_ne_zero _ (hc k))
  refine ⟨⟨_, form_mul_invMon_mem y c hg⟩, ⟨_, form_mul_invMon_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

theorem exists_chart_conductor (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (δ : K → ℕ) (F : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F δ ∧ aeval y F ≠ 0 ∧
      ∀ x ∈ integralClosure (chartRingZ y c) Ω, aeval y F * invMon y c δ * x ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have : Algebra.FiniteType ℤ A := .adjoin_of_finite (Set.finite_range _)
  have hfin : Module.Finite A (integralClosure A Ω) := Model.FiniteIntegralClosure.proof A Ω Ω
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A Ω => (z : Ω))
  have key : ∀ z : integralClosure A Ω, ((b : A) : Ω) * (z : Ω) ∈ A := by
    intro z
    have hz : z ∈ Submodule.span A (s : Set (integralClosure A Ω)) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu⟩ := hb _ (Finset.mem_image_of_mem _ hw)
      have : (u : Ω) = ((b : A) : Ω) * (w : Ω) := by rw [Algebra.smul_def] at hu; exact hu
      rw [← this]; exact u.2
    | zero => simp
    | add w v _ _ hw hv => rw [Subalgebra.coe_add, mul_add]; exact add_mem hw hv
    | smul r w _ hw =>
      rw [Subalgebra.coe_smul, Algebra.smul_def, mul_left_comm]
      exact mul_mem r.2 hw
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
  obtain ⟨δ, e, he, hv⟩ := SectionBounded.exists_form_of_mem_chartRingZ y c hc (b : A).2
  have hm : (∏ k, y ⟨k, c k⟩ ^ δ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hbv : aeval y e * invMon y c δ = ((b : A) : Ω) := by
    rw [hv, invMon, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hm, mul_one]
  refine ⟨δ, e, he, by rw [hv]; exact mul_ne_zero hb0 hm, fun x hx => ?_⟩
  rw [hbv]
  exact key ⟨x, hx⟩

theorem homog_prod {β : Type} (s : Finset β) (F : β → MRing ι) (δ : β → K → ℕ)
    (h : ∀ b ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (F b) (δ b)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ b ∈ s, F b) (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SectionBounded.homog_one (ι := ι))
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact SectionBounded.homog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

end Conductor

theorem Conductor.proof (hS : SecEq.Statement) : KH.CondStatement := by
  classical
  intro K _ ι _ Ω _ y a ha hy hbir
  obtain ⟨τ₀, hτ₀⟩ := hS K ι Ω y a ha hy
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  choose i0 hi0 using hy
  set Δ : K → ℕ := ∑ c : C, δ c
  set k' : ℕ := τ₀ + ∑ κ, Δ κ
  have hΔ : ∀ κ, Δ κ ≤ k' * a κ := fun κ =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)).trans
      ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (ha κ)))
  set e : K → ℕ := fun κ => k' * a κ - Δ κ
  set Φ : MRing ι := (∏ c : C, F c) * SectionBounded.chartMon i0 e
  have hΦ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog Φ (fun κ => k' * a κ) :=
    SectionBounded.homog_congr (SectionBounded.homog_mul
      (Conductor.homog_prod Finset.univ F δ fun c _ => hF c) (SectionBounded.homog_chartMon i0 e))
      fun κ => by simp only [Pi.add_apply, e]; exact Nat.add_sub_cancel' (hΔ κ)
  have hM : aeval y (SectionBounded.chartMon i0 e) ≠ 0 := by
    rw [SectionBounded.aeval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hi0 κ)
  have hΦ0 : aeval y Φ ≠ 0 := by
    rw [map_mul, map_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c) hM
  refine ⟨k', Φ, hΦ, hΦ0, fun τ s hs => ?_⟩
  rw [← hτ₀ (τ + k') (by omega)]
  intro c' hc'
  set c : C := ⟨c', hc'⟩
  have hx := hs c' hc'
  have hτ : (fun κ => τ * a κ) + Δ + e = fun κ => (τ + k') * a κ := by
    funext κ
    simp only [Pi.add_apply, e]
    rw [add_assoc, Nat.add_sub_cancel' (hΔ κ)]
    ring
  have hexp : ∀ n : K → ℕ, (∏ κ, y ⟨κ, c' κ⟩ ^ (-((n κ : ℕ) : ℤ))) = Conductor.invMon y c' n :=
    Conductor.prod_zpow_eq_invMon y c'
  beta_reduce at hx ⊢
  have e1 : ∀ κ, -((τ : ℤ) * (a κ : ℤ)) = -(((τ * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  have e2 : ∀ κ, -(((τ + k' : ℕ) : ℤ) * (a κ : ℤ)) = -((((τ + k') * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  simp only [e1] at hx
  simp only [e2]
  rw [hexp (fun κ => τ * a κ)] at hx
  rw [hexp (fun κ => (τ + k') * a κ), ← hτ, Conductor.invMon_add, Conductor.invMon_add,
    ← Conductor.invMon_sum y c' Finset.univ δ]
  have hsplit : aeval y Φ * s * (Conductor.invMon y c' (fun κ => τ * a κ) *
      (∏ b : C, Conductor.invMon y c' (δ b)) * Conductor.invMon y c' e) =
      (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
        (aeval y (SectionBounded.chartMon i0 e) * Conductor.invMon y c' e) *
        (aeval y (F c) * Conductor.invMon y c' (δ c) * (s * Conductor.invMon y c' (fun κ => τ * a κ))) := by
    rw [map_mul, map_prod]
    rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
      ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
      Finset.prod_mul_distrib]
    ring
  rw [hsplit]
  refine mul_mem (mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b))
    (Conductor.form_mul_invMon_mem y c' (SectionBounded.homog_chartMon i0 e))) ?_
  exact hcond c _ hx

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem FibreNormDehomRoots.full : FibreNormDehomRoots.Statement :=
  FibreNormDehomRoots.proof
    (PullFormsGeneric.proof
      (PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof))
    PullSectionIntegral.proof CharpolyRootLift.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

namespace ProjDegGenDeg

theorem succ_rpow_isBigO (D : ℕ) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) - 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
  refine IsBigO.of_bound (2 ^ D) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  rw [Real.rpow_sub_one (by positivity), Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)]
  calc ((n : ℝ) + 1) ^ D / ((n : ℝ) + 1) ≤ (2 * (n : ℝ)) ^ D / n :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _) hpos (by linarith)
    _ = 2 ^ D * ((n : ℝ) ^ D / n) := by rw [mul_pow]; ring

theorem pow_div_isLittleO (D : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ D / (n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have h1 : (fun n : ℕ => (1 : ℝ) / n) =o[atTop] fun _ : ℕ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr tendsto_one_div_atTop_nhds_zero_nat
  exact (h1.mul_isBigO (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop)).congr (fun n => by ring)
    (fun n => by ring)

theorem eq_zero_of_isBigO (D : ℕ) (c : ℝ)
    (h : (fun n : ℕ => c * (n : ℝ) ^ D) =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ)) : c = 0 := by
  by_contra hc
  have h2 := (isLittleO_const_mul_left_iff hc).mp (h.trans_isLittleO (pow_div_isLittleO D))
  refine isLittleO_irrefl ?_ h2
  refine (eventually_ge_atTop 1).frequently.mono fun n hn => ?_
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

end ProjDegGenDeg


open ProjDegGenDeg in
theorem ProjDegGenDeg.proof (hR : RankOfSections.Statement) : ProjDegGenDeg.Statement := by
  intro D Ω _ _ κ _ x e hA hF
  obtain ⟨hq, hdim⟩ := GenericFibre.proof Ω κ x D hA
  obtain ⟨C, hC⟩ := hR κ _ D hq hdim
  set γ : ℤ := genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 with hγ
  have hγ' : GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ
      ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)))
      (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = γ := by
    rw [hγ]; unfold genDeg; congr 1

  have h1 : (fun n : ℕ => (Module.finrank ℤ (sec ℤ x n) : ℝ) - (γ : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
    refine IsBigO.trans ?_ (succ_rpow_isBigO D)
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    have hn := hC n
    rw [hγ', SectionsRank.proof Ω κ x n] at hn
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    exact_mod_cast hn

  have h2 := finrank_sec_asymp x e hF
  have h3 : (fun n : ℕ => (((projDeg x e : ℝ) - (γ : ℝ)) / (D.factorial : ℝ)) * (n : ℝ) ^ D)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) :=
    (h1.sub h2).congr_left fun n => by ring
  have h4 := eq_zero_of_isBigO D _ h3
  have hfac : (D.factorial : ℝ) ≠ 0 := by positivity
  rw [div_eq_zero_iff, sub_eq_zero] at h4
  rcases h4 with h4 | h4
  · exact_mod_cast h4.symm
  · exact absurd h4 hfac

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis famExt_symm)

noncomputable section

set_option linter.unusedSectionVars false

namespace ZCombExpand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {J : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem famExt_symm_of (e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (he : ∀ i, IsSmoothHerm (e i))
    (hJ : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
      J P n (L ∘ σ) = J P n L) :
    IsSymmForm (famExt J P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hJ (e ∘ s) σ.symm fun j => he _]

theorem famExt_expand (e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hs : IsSymmForm (famExt J P n e)) (q p : ℝ) :
    famExt J P n e (fun _ => ![q, p]) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * q ^ (n - i) * p ^ i *
        J P n (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) := by
  classical
  have hw : (fun _ : Fin n => (![q, p] : Fin 2 → ℝ)) =
      fun _ => p • (Pi.single 1 1 : Fin 2 → ℝ) + q • (Pi.single 0 1 : Fin 2 → ℝ) := by
    funext j i
    fin_cases i <;> simp
  rw [hw, symm_expand _ hs, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega]
  have hmix : (mix (n - i) (Pi.single 0 1) (p • Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).piecewise
        (fun j => p • (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) j)
        (mix (n - i) (Pi.single 0 1) (Pi.single 1 1)) := by
    funext j
    by_cases h : (j : ℕ) < n - i
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simp; omega)]
      simp [mix, h]
    · rw [Finset.piecewise_eq_of_mem _ _ _ (by simp; omega)]
      simp [mix, h]
  have hcard : (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).card = i := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, Fin.card_filter_val_lt]
    omega
  have hbasis : (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      fun j => Pi.single ((fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) j) 1 := by
    funext j
    simp only [mix]
    split_ifs <;> rfl
  have hlist : (e ∘ fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) =
      fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1 := by
    funext j
    simp only [Function.comp]
    split_ifs <;> rfl
  rw [hmix, MultilinearMap.map_piecewise_smul, Finset.prod_const, hcard, hbasis, famExt_basis, hlist,
    smul_eq_mul, Nat.choose_symm hin]
  simp only [RingHom.id_apply]
  ring

end ZCombExpand

theorem ZCombExpand.proof : ZCombExpand.Statement := by
  intro K _ ι _ I hI P d M H q p hP hM hH
  set e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ![M, H] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    fin_cases i
    · exact hM
    · exact hH
  set Z := HermLine.zcomb M H (q : ℤ) (p : ℤ) with hZ_def
  have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hM hH _ _
  refine ⟨?_, ?_⟩
  · have hposition : ∀ (L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin d), (∀ j, IsSmoothHerm (L j)) →
        I P d (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * I P d (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * I P d (Function.update L a (e 1)) := by
      intro L a hL
      cases d with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hM hH (q : ℤ) (p : ℤ)
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := I) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, ZCombExpand.famExt_expand e (famExt_symm hI hP e he)]
    rfl
  · intro hd
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    let J : Ideal (MRing ι) → (m : ℕ) → (Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ :=
      fun P' m L => I P' (m + 1) (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L)
    have hcons : ∀ L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, IsSmoothHerm (L j)) →
        ∀ j, IsSmoothHerm (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L j) := by
      intro L hL j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hM
      · simpa using hL j
    have hsymm : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
        J P n (L ∘ σ) = J P n L := by
      intro L σ hL
      have hc : (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (L ∘ σ) : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
          (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L) ∘ (Equiv.Perm.decomposeFin.symm (0, σ)) := by
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
        · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
      show I P (n + 1) _ = I P (n + 1) _
      rw [hc, hI.1 P (n + 1) _ _ hP (hcons L hL)]
    have hposition : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        J P n (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * J P n (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * J P n (Function.update L a (e 1)) := by
      intro L a hL
      show I P (n + 1) _ = _ * I P (n + 1) _ + _ * I P (n + 1) _
      rw [Fin.cons_update, Fin.cons_update, Fin.cons_update]
      have h := ZCombLimit.fam_update_zcomb_int hI hP _ (hcons L hL) a.succ hM hH (q : ℤ) (p : ℤ)
      simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := J) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    have hl : (fun j : Fin (n + 1) => if (j : ℕ) = 0 then M else Z) =
        Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (fun _ : Fin n => Z) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp
    rw [hl, show I P (n + 1) (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (fun _ : Fin n => Z)) =
      J P n (fun _ => Z) from rfl, key,
      ZCombExpand.famExt_expand e (ZCombExpand.famExt_symm_of e he hsymm), Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hl2 : (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M
        (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
        fun j : Fin (n + 1) => if (j : ℕ) < n + 1 - i then M else H := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero]
        exact (if_pos (show ((0 : Fin (n + 1)) : ℕ) < n + 1 - i by simp; omega)).symm
      · simp only [Fin.cons_succ, Fin.val_succ]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (by omega) h2
        · exact absurd (by omega) h1
        · rfl
    show _ * I P (n + 1) _ = _
    rw [hl2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
