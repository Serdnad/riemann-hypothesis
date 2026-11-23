module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

section

open MeasureTheory Set

namespace GlobalTheory.FlatFamily

open GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral

variable {X : Type} [MeasurableSpace X]


omit [MeasurableSpace X] in
theorem flatIntegrand_rebase (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (s₀ s₁ s : ℂ) (x : X) :
    flatIntegrand f a s₀ s x = flatIntegrand f a s₀ s₁ x * ((a x : ℝ) : ℂ) ^ (s - s₁) := by
  have h : ((a x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha x).ne'
  simp only [flatIntegrand]
  rw [mul_assoc, ← Complex.cpow_add _ _ h]
  congr 2
  ring


omit [MeasurableSpace X] in
theorem norm_flatIntegrand_le (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (ha1 : ∀ x, a x ≤ 1)
    (s₀ : ℂ) {s₁ s : ℂ} (hs : s₁.re ≤ s.re) (x : X) :
    ‖flatIntegrand f a s₀ s x‖ ≤ ‖flatIntegrand f a s₀ s₁ x‖ := by
  letI : MeasurableSpace X := ⊥
  rw [norm_flatIntegrand f s₀ s (ha x), norm_flatIntegrand f s₀ s₁ (ha x)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (ha x) (ha1 x) (by linarith)) (norm_nonneg _)

theorem aestronglyMeasurable_flatIntegrand {μ : Measure X} {f : X → ℂ} {a : X → ℝ}
    (hm : Measurable a) (ha : ∀ x, 0 < a x) {s₀ s₁ : ℂ}
    (h : AEStronglyMeasurable (flatIntegrand f a s₀ s₁) μ) (s : ℂ) :
    AEStronglyMeasurable (flatIntegrand f a s₀ s) μ := by
  have e : flatIntegrand f a s₀ s
      = fun x => flatIntegrand f a s₀ s₁ x * ((a x : ℝ) : ℂ) ^ (s - s₁) :=
    funext (flatIntegrand_rebase f ha s₀ s₁ s)
  rw [e]
  refine h.mul ?_
  exact ((Complex.measurable_ofReal.comp hm).pow_const (s - s₁)).aestronglyMeasurable

omit [MeasurableSpace X] in
theorem hasDerivAt_flatIntegrand (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (s₀ s : ℂ) (x : X) :
    HasDerivAt (fun z => flatIntegrand f a s₀ z x)
      (flatIntegrand f a s₀ s x * ((Real.log (a x) : ℝ) : ℂ)) s := by
  have h : ((a x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha x).ne'
  have h1 := (((hasDerivAt_id s).sub_const s₀).const_cpow (c := ((a x : ℝ) : ℂ))
    (Or.inl h)).const_mul (f x)
  simp only [flatIntegrand]
  refine h1.congr_deriv ?_
  rw [Complex.ofReal_log (ha x).le]
  simp only [id, mul_one]
  ring

theorem flatZetaHolomorphic : FlatZetaHolomorphic := by
  intro X _ μ f a s₀ s₁ hm ha ha1 hint
  have hmeas := aestronglyMeasurable_flatIntegrand hm ha hint.aestronglyMeasurable
  have hI : ∀ s : ℂ, s₁.re ≤ s.re → Integrable (flatIntegrand f a s₀ s) μ := fun s hs =>
    hint.norm.mono' (hmeas s) (Filter.Eventually.of_forall (norm_flatIntegrand_le f ha ha1 s₀ hs))
  refine ⟨⟨hI, fun s _ => ⟨_, self_mem_nhdsWithin, _, hint.norm,
    fun s' hs' x => norm_flatIntegrand_le f ha ha1 s₀ hs' x⟩⟩, ?_, ?_⟩
  · intro s hs
    have hs' : s₁.re < s.re := hs
    set ε : ℝ := (s.re - s₁.re) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hU : {z : ℂ | s₁.re + ε < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        change s₁.re + ε < s.re
        rw [hε]; linarith)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun z x => flatIntegrand f a s₀ z x)
      (F' := fun z x => flatIntegrand f a s₀ z x * ((Real.log (a x) : ℝ) : ℂ))
      (x₀ := s) (bound := fun x => ‖flatIntegrand f a s₀ s₁ x‖ * (1 / ε)) hU
      (Filter.Eventually.of_forall hmeas) (hI s hs'.le)
      ((hmeas s).mul
        (Complex.measurable_ofReal.comp (Real.measurable_log.comp hm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x z hz => by
        have hz' : s₁.re + ε < z.re := hz
        rw [flatIntegrand_rebase f ha s₀ s₁ z x, mul_assoc, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha x), Complex.norm_real,
          Real.norm_eq_abs, Complex.sub_re]
        have h1 : a x ^ (z.re - s₁.re) ≤ a x ^ ε :=
          Real.rpow_le_rpow_of_exponent_ge (ha x) (ha1 x) (by linarith)
        have h2 := Real.abs_log_mul_self_rpow_lt (a x) ε (ha x) (ha1 x) hεpos
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (ha x) ε), mul_comm] at h2
        exact (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans h2.le)
      (hint.norm.mul_const _)
      (Filter.Eventually.of_forall fun x z _ => hasDerivAt_flatIntegrand f ha s₀ z x)
    exact key.2.differentiableAt.differentiableWithinAt
  · exact continuousOn_of_dominated (bound := fun x => ‖flatIntegrand f a s₀ s₁ x‖)
      (fun s _ => hmeas s)
      (fun s hs => Filter.Eventually.of_forall (norm_flatIntegrand_le f ha ha1 s₀ hs))
      hint.norm
      (Filter.Eventually.of_forall fun x z _ =>
        (hasDerivAt_flatIntegrand f ha s₀ z x).continuousAt.continuousWithinAt)

end GlobalTheory.FlatFamily
end

section

open Matrix GlobalTheory.ClassFin

namespace GlobalTheory

theorem siegelSet_entry_bound_of_lattice_min (N : ℕ) (C : ℝ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ) (hS : IsSiegel C k a n) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmin : ∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖)
    (i j : Fin N) : |(k * diagonal a * n) i j| * t ^ N ≤ N * C ^ N := by
  have hN : 0 < N := Fin.pos i
  set i0 : Fin N := ⟨0, hN⟩ with hi0

  have hk : ∀ p q, |k p q| ≤ 1 := by
    intro p q
    have h := congrFun (congrFun hS.orth q) q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have : k p q * k p q ≤ ∑ x, k x q * k x q :=
      Finset.single_le_sum (f := fun x => k x q * k x q) (fun x _ => mul_self_nonneg _) (Finset.mem_univ p)
    rw [h] at this
    have h2 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact this
    nlinarith [abs_nonneg (k p q)]
  have hC1 : 1 ≤ C := by
    have := hS.bdd i i
    rw [hS.diag i, abs_one] at this
    exact this

  have hg : ∀ p q, (k * diagonal a * n) p q = ∑ l, k p l * a l * n l q := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]

  have hcol : ∀ p, (k * diagonal a * n) p i0 = k p i0 * a i0 := by
    intro p
    rw [hg, Finset.sum_eq_single i0]
    · rw [hS.diag i0, mul_one]
    · intro l _ hl
      have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      rw [hS.lower l i0 this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have ha0 : t ≤ a i0 := by
    have h := hmin (Pi.single i0 1) (by
      intro h; have := congrFun h i0; simp at this)
    refine h.trans ?_
    refine (pi_norm_le_iff_of_nonneg (le_of_lt (hS.pos i0))).2 ?_
    intro p
    have : ((k * diagonal a * n) *ᵥ fun i => (((Pi.single i0 (1:ℤ) : Fin N → ℤ) i : ℤ) : ℝ)) p
        = (k * diagonal a * n) p i0 := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hcol, Real.norm_eq_abs, abs_mul, abs_of_pos (hS.pos i0)]
    exact mul_le_of_le_one_left (le_of_lt (hS.pos i0)) (hk p i0)
  have hlow : ∀ l, t ≤ C * a l := by
    intro l
    by_cases hl : l = i0
    · subst hl
      nlinarith [hS.pos i0]
    · have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      exact ha0.trans (hS.le i0 l this)
  have hup : ∀ l, a l * t ^ (N - 1) ≤ C ^ (N - 1) := by
    intro l
    have hprod : ∏ x ∈ Finset.univ.erase l, t ≤ ∏ x ∈ Finset.univ.erase l, (C * a x) :=
      Finset.prod_le_prod₀ (fun _ _ => le_of_lt ht0) (fun x _ => hlow x)
    rw [Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin] at hprod
    have h1 : a l * ∏ x ∈ Finset.univ.erase l, a x = 1 := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ l)]; exact hS.prod_eq
    have hal := le_of_lt (hS.pos l)
    calc a l * t ^ (N - 1) ≤ a l * (C ^ (N - 1) * ∏ x ∈ Finset.univ.erase l, a x) :=
          mul_le_mul_of_nonneg_left hprod hal
      _ = C ^ (N - 1) * (a l * ∏ x ∈ Finset.univ.erase l, a x) := by ring
      _ = C ^ (N - 1) := by rw [h1, mul_one]
  have hent : |(k * diagonal a * n) i j| ≤ ∑ l, a l * C := by
    rw [hg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_mul, abs_of_pos (hS.pos l)]
    have h1 := hk i l
    have h2 := hS.bdd l j
    have hal := le_of_lt (hS.pos l)
    calc |k i l| * a l * |n l j| ≤ 1 * a l * C := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hal) h2 (abs_nonneg _) (by positivity)
      _ = a l * C := by ring
  have htN : t ^ N = t ^ (N - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have htpow : 0 ≤ t ^ N := by positivity
  calc |(k * diagonal a * n) i j| * t ^ N ≤ (∑ l, a l * C) * t ^ N :=
        mul_le_mul_of_nonneg_right hent htpow
    _ = ∑ l, (a l * t ^ (N - 1)) * C * t := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; rw [htN]; ring
    _ ≤ ∑ l : Fin N, C ^ (N - 1) * C * 1 := by
        refine Finset.sum_le_sum fun l _ => ?_
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hup l) (by linarith)) ht1 (le_of_lt ht0)
        positivity
    _ = N * C ^ N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← pow_succ,
          Nat.sub_add_cancel hN]

theorem siegel_entry_bound : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    (∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖) →
    ∀ i j, |(k * diagonal a * n) i j| * t ^ N ≤ C' :=
  fun N C => ⟨N * C ^ N, fun k a n hS t ht0 ht1 hmin i j =>
    siegelSet_entry_bound_of_lattice_min N C k a n hS t ht0 ht1 hmin i j⟩

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.AdelicLatticeClosure

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem adelic_hat_mul_of_mul_closed {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (J : Set E) (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J) {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F J) (hw : w ∈ GlobalTheory.AdLat.hat1 F J) :
    z * w ∈ GlobalTheory.AdLat.hat1 F J := by
  unfold GlobalTheory.AdLat.hat1 at hz hw ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x * y, hJ x hx y hy, ?_⟩
      · exact mul_mem (ha v) (hb v)
      · exact Algebra.TensorProduct.tmul_mul_tmul a b x y
    | zero => rw [mul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | neg u _ hu => rw [mul_neg]; exact neg_mem hu
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

theorem adelic_hat_one_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E))
    (hw : w ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) :
    z * w ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
  refine adelic_hat_mul_of_mul_closed _ ?_ hz hw
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
  exact (FractionalIdeal.mem_one_iff _).2 ⟨a * b, map_mul _ a b⟩

end GlobalTheory.AdelicLatticeClosure
end
end

section

open ValuativeRel GlobalTheory.SplitWeil

namespace GlobalTheory.ScaledIdealIndex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relIndex_comap_mulLeft (a : kˣ) (H K : AddSubgroup k) :
    (H.comap (AddMonoidHom.mulLeft (a : k))).relIndex (K.comap (AddMonoidHom.mulLeft (a : k))) =
      H.relIndex K := by
  have hs : Function.Surjective (AddMonoidHom.mulLeft (a : k)) := fun y =>
    ⟨((a⁻¹ : kˣ) : k) * y, by simp [← mul_assoc]⟩
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hs]

theorem relIndex_maxIdeal (L : AddSubgroup k) (hL : ∀ x, x ∈ L ↔ valuation k x < 1) :
    L.relIndex (𝒪[k]).toAddSubgroup = resCard k := by
  let f : 𝒪[k] →+ k := (𝒪[k]).subtype.toAddMonoidHom
  have hr : f.range = (𝒪[k]).toAddSubgroup := by
    ext x; simp [f]
  let g : 𝒪[k] →+ 𝓀[k] := (IsLocalRing.residue 𝒪[k]).toAddMonoidHom
  have hk : L.comap f = g.ker := by
    ext y
    simp only [AddSubgroup.mem_comap, AddMonoidHom.mem_ker, g, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, hL]
    rfl
  have hs : Function.Surjective g := Ideal.Quotient.mk_surjective
  rw [← hr, ← AddSubgroup.index_comap, hk, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hs]
  simp [resCard]

section
variable (L : AddSubgroup k) (hL : ∀ x, x ∈ L ↔ valuation k x < 1)
include hL

theorem mem_comap_mulLeft (a : kˣ) (x : k) :
    x ∈ L.comap (AddMonoidHom.mulLeft (a : k)) ↔ valuation k ((a : k) * x) < 1 := by
  simp [hL]

theorem comap_mulLeft_one : L.comap (AddMonoidHom.mulLeft ((1 : kˣ) : k)) = L := by
  ext x; simp [hL]

theorem comap_mulLeft_mul (a b : kˣ) :
    L.comap (AddMonoidHom.mulLeft ((a * b : kˣ) : k)) =
      (L.comap (AddMonoidHom.mulLeft (a : k))).comap (AddMonoidHom.mulLeft (b : k)) := by
  ext x; simp [hL, mul_assoc]

theorem comap_mulLeft_le_pow (ϖ : kˣ) (hϖ : valuation k (ϖ : k) ≤ 1) (a : kˣ) (j : ℕ) :
    L.comap (AddMonoidHom.mulLeft (a : k)) ≤ L.comap (AddMonoidHom.mulLeft ((ϖ ^ j * a : kˣ) : k)) := by
  intro x hx
  rw [mem_comap_mulLeft L hL] at hx ⊢
  rw [Units.val_mul, Units.val_pow_eq_pow_val, mul_assoc, map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' (pow_le_one₀ zero_le' hϖ)) hx

theorem relIndex_unif (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) :
    (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex L = resCard k := by
  have hpos : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have e : L = (𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k)) := by
    ext x
    rw [hL]
    simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup,
      Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one, hϖ, le_uniformizer_iff]
  calc (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex L
      = (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex
          ((𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))) := by rw [← e]
    _ = resCard k := by rw [relIndex_comap_mulLeft, relIndex_maxIdeal L hL]

theorem relIndex_unif_pow (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (n : ℕ) :
    (L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k))).relIndex L = resCard k ^ n := by
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  induction n with
  | zero => rw [Nat.cast_zero, neg_zero, zpow_zero, comap_mulLeft_one L hL, pow_zero, AddSubgroup.relIndex_self]
  | succ n ih =>
    have ea : ϖ ^ (-((n + 1 : ℕ) : ℤ)) = ϖ⁻¹ * ϖ ^ (-(n : ℤ)) := by
      rw [← zpow_neg_one, ← zpow_add]; congr 1; push_cast; ring
    have eb : ϖ ^ (-(n : ℤ)) = ϖ ^ (1 : ℕ) * ϖ ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [ea, pow_one, ← mul_assoc, mul_inv_cancel, one_mul]
    have hle : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-((n + 1 : ℕ) : ℤ)) : kˣ) : k)) ≤
        L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) := by
      rw [eb]; exact comap_mulLeft_le_pow L hL ϖ h1 _ 1
    have hle2 : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) ≤ L := by
      have := comap_mulLeft_le_pow L hL ϖ h1 (ϖ ^ (-(n : ℤ))) n
      rwa [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, comap_mulLeft_one L hL] at this
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle hle2, ih, pow_succ, mul_comm]
    congr 1
    have e1 : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) =
        L.comap (AddMonoidHom.mulLeft (((1 : kˣ) * ϖ ^ (-(n : ℤ)) : kˣ) : k)) := by rw [one_mul]
    rw [ea, e1, comap_mulLeft_mul L hL, comap_mulLeft_mul L hL, relIndex_comap_mulLeft,
      comap_mulLeft_one L hL, relIndex_unif L hL ϖ hϖ]

end

end GlobalTheory.ScaledIdealIndex

namespace GlobalTheory.ScaledIdealIndex

theorem relIndex_scaled_maxIdeal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) →
      (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) →
      (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := by
  intro k _ _ _ _ ϖ hϖ c L P hL hP
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  have hPe : P = L.comap (AddMonoidHom.mulLeft ((ϖ ^ c : kˣ) : k)) := by
    ext x; rw [hP, mem_comap_mulLeft L hL]
  rw [AddSubgroup.inf_relIndex_left, AddSubgroup.inf_relIndex_right]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · have hLP : L ≤ P := by
      have := comap_mulLeft_le_pow L hL ϖ h1 1 n
      rwa [mul_one, comap_mulLeft_one L hL, ← zpow_natCast, ← hPe] at this
    rw [AddSubgroup.relIndex_eq_one.2 hLP, mul_one, Int.natAbs_natCast]
    have eL : L = L.comap (AddMonoidHom.mulLeft (((ϖ ^ (-(n : ℤ)) * ϖ ^ (n : ℤ) : kˣ)) : k)) := by
      rw [← zpow_add, neg_add_cancel, zpow_zero, comap_mulLeft_one L hL]
    have eP : P = L.comap (AddMonoidHom.mulLeft ((((1 : kˣ) * ϖ ^ (n : ℤ) : kˣ)) : k)) := by
      rw [one_mul, hPe]
    calc L.relIndex P
        = (L.comap (AddMonoidHom.mulLeft (((ϖ ^ (-(n : ℤ)) * ϖ ^ (n : ℤ) : kˣ)) : k))).relIndex
            (L.comap (AddMonoidHom.mulLeft ((((1 : kˣ) * ϖ ^ (n : ℤ) : kˣ)) : k))) := by
          rw [← eL, ← eP]
      _ = resCard k ^ n := by
          rw [comap_mulLeft_mul L hL, comap_mulLeft_mul L hL, relIndex_comap_mulLeft,
            comap_mulLeft_one L hL, relIndex_unif_pow L hL ϖ hϖ n]
  · have hPL : P ≤ L := by
      have := comap_mulLeft_le_pow L hL ϖ h1 (ϖ ^ (-(n : ℤ))) n
      rwa [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, comap_mulLeft_one L hL, ← hPe] at this
    rw [AddSubgroup.relIndex_eq_one.2 hPL, one_mul, Int.natAbs_neg, Int.natAbs_natCast, hPe,
      relIndex_unif_pow L hL ϖ hϖ n]

end GlobalTheory.ScaledIdealIndex
end

section

open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef : ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ), (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  first | exact @GlobalTheory.hermitian_adjoint_exists_unique | exact GlobalTheory.hermitian_adjoint_exists_unique | (intros; apply GlobalTheory.hermitian_adjoint_exists_unique <;> assumption)
end

section

open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.mem_range_adjoint_of_mem_span_evaluation_values : ∀ (X W C : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ev : C →ₗ[ℂ] W →ₗ[ℂ] (X → ℂ)) (K : Submodule ℂ W) (ipD : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (pet : (X → ℂ) → (X → ℂ) → ℂ), (∀ w w', ipD w w' = conj (ipD w' w)) → (∀ w, w ≠ 0 → 0 < (ipD w w).re) → (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → (∀ (y : C) (w : W) (n : ℕ) (ys : Fin n → C) (ws : Fin n → W), pet (ev y w) (∑ i, ev (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i)) → ∀ (x : C) (F : X → ℂ) (l : W → ℂ), F ∈ Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} → (∀ y, ∀ w ∈ K, pet (ev y w) F = ip y x * l w) → F ≠ 0 → x ≠ 0 ∧ ∃ w ∈ K, F = ev x w := by
  first | exact @GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span | exact GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span | (intros; apply GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span <;> assumption)
end

section

open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts : ∀ (A C I J : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (Θ : C →ₗ[ℂ] A) (pA : A → I → Prop) (pC : C → J → Prop) (RA : I → I → Prop) (RC : J → J → Prop) (T : I → J), (∀ x y, ipA x y = conj (ipA y x)) → (∀ x, x ≠ 0 → 0 < (ipA x x).re) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → Equivalence RA → Submodule.span ℂ {u | ∃ B, pA u B} = ⊤ → (∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B) → (∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) → (∀ B B', RC (T B) (T B') → RA B B') → (∀ (ι : Type) (x : ι → C) (B : ι → J), (∀ i, pC (x i) (B i)) → (∀ i i', i ≠ i' → ¬ RC (B i) (B i')) → LinearIndependent ℂ x) → (∀ u B, pA u B → ∃ x, (∀ y, ip y x = ipA (Θ y) u) ∧ pC x (T B)) → Function.Surjective Θ := by
  first | exact @GlobalTheory.ChainOnto.surjective_of_adjoint_separates | exact GlobalTheory.ChainOnto.surjective_of_adjoint_separates | (intros; apply GlobalTheory.ChainOnto.surjective_of_adjoint_separates <;> assumption)
end

section

open MeasureTheory
open scoped ContDiff


theorem _root_.GlobalTheory.T.contDiff_compactAverage_of_closed_partials : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  first | exact @GlobalTheory.AvgSmooth.main | exact GlobalTheory.AvgSmooth.main | (intros; apply GlobalTheory.AvgSmooth.main <;> assumption)
end
