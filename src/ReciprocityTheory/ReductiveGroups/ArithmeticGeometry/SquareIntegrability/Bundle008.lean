module

public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitVB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle006

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section SlopeTestRemainingChoices
variable {dim : (E →+* ℂ) → ℕ}

theorem smul_add_scalar (β β' : 𝓞 E) (v : Vsp dim) : act (β + β') v = act β v + act β' v := by
  ext i
  simp [act, add_mul]

theorem Hf_add_rightSquareIntegrability (x w w' : Vsp dim) : Hf x (w + w') = Hf x w + Hf x w' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left_conj [IsCMField E] (α : 𝓞 E) (v w : Vsp dim) :
    Hf (act α v) w = Hf v (act (IsCMField.ringOfIntegersComplexConj E α) w) := by
  simp only [Hf, act, PiLp.toLp_apply, IsCMField.coe_ringOfIntegersComplexConj,
    IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

end SlopeTestRemainingChoices

theorem sum_sq_norm_ge_of_span [IsCMField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) {ξ : Vsp X.dim} (hξ : ξ ∈ I) (hξ0 : ξ ≠ 0)
    (k : ℕ) (x u : Fin k → Vsp X.dim) (hxu : ∀ j, x j ∈ X.L ∧ IsU I (x j) (u j))
    (hspan : Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (x j)) w} = IR I) :
    2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2 / 2 := by
  classical

  have hint : ∀ j (β : 𝓞 E), ∃ n : ℤ, (Hf (x j) (act β ξ)).im = n := fun j β =>
    X.integral _ _ (hxu j).1 (hle (hst β ξ hξ))
  let φ : Fin k → 𝓞 E →+ ℤ := fun j => AddMonoidHom.mk' (fun β => (hint j β).choose) (by
    intro β β'
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← (hint j (β + β')).choose_spec, ← (hint j β).choose_spec, ← (hint j β').choose_spec,
      smul_add_scalar, Hf_add_rightSquareIntegrability, Complex.add_im])
  have hφ : ∀ j β, ((φ j β : ℤ) : ℝ) = (Hf (x j) (act β ξ)).im := fun j β =>
    ((hint j β).choose_spec).symm

  choose y hy using fun j => exists_dual (φ j)
  have hyR : ∀ j (β : 𝓞 E), ((Algebra.trace ℚ E ((β : E) * y j) : ℚ) : ℝ) = (Hf (x j) (act β ξ)).im := by
    intro j β
    rw [hy j β, ← hφ j β]
    push_cast
    rfl
  have hcs : ∀ j, 2 * ∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2 ≤ ‖ξ‖ ^ 2 * ‖u j‖ ^ 2 := fun j =>
    cs_bound I hst hξ (x j) (u j) (hxu j).2 (y j) (hyR j)

  set l : E := ∑ j, y j * IsCMField.complexConj E (y j) with hldef
  set a : (E →+* ℂ) → ℝ := fun σ => ∑ j, ‖σ (y j)‖ ^ 2 with hadef
  have ha0 : ∀ σ, 0 ≤ a σ := fun σ => Finset.sum_nonneg fun _ _ => by positivity
  have hσl : ∀ σ : E →+* ℂ, σ l = (a σ : ℂ) := by
    intro σ

    simp only [hldef, hadef, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj']

  have hl : l ≠ 0 := by
    intro hl0
    obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : a σ₀ = 0 := by
      have := hσl σ₀
      rw [hl0, map_zero] at this
      exact_mod_cast this.symm
    have hy0 : ∀ j, y j = 0 := by
      intro j
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j
        (Finset.mem_univ j)
      have h3 : σ₀ (y j) = 0 := by simpa using h2
      exact (map_eq_zero_iff σ₀ σ₀.injective).1 h3
    have horth : ∀ w ∈ IR I, inner ℝ w ξ = 0 := by
      intro w hw
      rw [← hspan] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨j, α, hU⟩ := hw
        rw [hU.2 ξ (Submodule.subset_span hξ), herm_smul_left_conj, ← hyR, hy0 j, mul_zero, map_zero]
        simp
      | zero => simp
      | add w w' _ _ h h' => rw [inner_add_left, h, h', add_zero]
      | smul r w _ h => rw [real_inner_smul_left, h, mul_zero]
    have h4 := horth ξ (Submodule.subset_span hξ)
    rw [real_inner_self_eq_norm_sq] at h4
    have h5 : ‖ξ‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 h4
    exact hξ0 (norm_eq_zero.1 h5)

  have hmemD : ∀ j, y j ∈ Dual1 E := fun j => mem_dual_of (y j) fun β => ⟨φ j β, hy j β⟩
  have htr : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have hmemD' : ∀ j, IsCMField.complexConj E (y j) ∈ Dual1 E := fun j =>
    mem_dual_of _ fun β => by
      refine ⟨φ j (IsCMField.ringOfIntegersComplexConj E β), ?_⟩
      rw [← hy j, IsCMField.coe_ringOfIntegersComplexConj, ← htr, map_mul,
        IsCMField.complexConj_apply_apply]
  have hmem : l ∈ Dual1 E * Dual1 E := by
    rw [hldef, ← FractionalIdeal.mem_coe]
    exact Submodule.sum_mem _ fun j _ =>
      (FractionalIdeal.mem_coe).2 (FractionalIdeal.mul_mem_mul (hmemD j) (hmemD' j))
  have hnorm := one_le_norm_mul l hl hmem

  have hprodC : ((Algebra.norm ℚ l : ℚ) : ℂ) = ((∏ σ, a σ : ℝ) : ℂ) := by
    rw [norm_prod_emb]
    push_cast
    exact Finset.prod_congr rfl fun σ _ => hσl σ
  have hprodR : ((Algebra.norm ℚ l : ℚ) : ℝ) = ∏ σ, a σ := by exact_mod_cast hprodC
  have hP0 : 0 ≤ ∏ σ, a σ := Finset.prod_nonneg fun σ _ => ha0 σ
  set D : ℝ := ((NumberField.discr E).natAbs : ℝ) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    exact_mod_cast Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  have hprod : (D ^ 2)⁻¹ ≤ ∏ σ, a σ := by
    have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ l : ℚ) : ℝ)| * D ^ 2 := by
      have h1' := (Rat.cast_le (K := ℝ)).2 hnorm
      push_cast at h1'
      rw [hDdef]
      exact h1'
    rw [hprodR, abs_of_nonneg hP0] at h1
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    linarith
  have hcard : Fintype.card (E →+* ℂ) = 2 * PT.f E := by
    rw [NumberField.Embeddings.card, PT.f, IsTotallyComplex.finrank]
    omega
  have hcpos : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos
  have hsum := sum_ge_of_prod_ge a ha0 D hD hprod hcpos
  have hrd : D ^ ((Fintype.card (E →+* ℂ) : ℝ)⁻¹) = PT.rd E := by
    rw [PT.rd, NumberField.Embeddings.card, one_div, hDdef]
    congr 1
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hrd, hcard] at hsum
  push_cast at hsum

  have hξpos : 0 < ‖ξ‖ ^ 2 := by
    have := norm_pos_iff.2 hξ0
    positivity
  have hj : ∀ j, (∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2) / ‖ξ‖ ^ 2 ≤ ‖u j‖ ^ 2 / 2 := by
    intro j
    rw [div_le_iff₀ hξpos]
    linarith [hcs j]
  have hsw : ∑ σ, a σ = ∑ j, ∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2 := by
    rw [hadef]
    exact Finset.sum_comm
  calc 2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) = (2 * PT.f E / PT.rd E ^ 2) / ‖ξ‖ ^ 2 := by
        rw [div_div]
    _ ≤ (∑ σ, a σ) / ‖ξ‖ ^ 2 := by
        apply div_le_div_of_nonneg_right hsum hξpos.le
    _ = ∑ j, (∑ σ : E →+* ℂ, ‖σ (y j)‖ ^ 2) / ‖ξ‖ ^ 2 := by
        rw [hsw, Finset.sum_div]
    _ ≤ ∑ j, ‖u j‖ ^ 2 / 2 := Finset.sum_le_sum fun j _ => hj j

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

structure Good (X : PT E) (c : ℝ) (I : Submodule ℤ (Vsp X.dim)) : Prop where
  le : I ≤ X.L
  sat : ∀ x ∈ X.L, x ∈ IR I → x ∈ I
  stable : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I
  iso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0
  sep : ∀ x ∈ X.L, ∀ u, IsU I x u → u ≠ 0 → c < ‖u‖

private lemma act_zero_square_integrability {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : act α (0 : Vsp dim) = 0 := by
  first
  | (ext i; simp [act])
  | simp [act]
  | (unfold act; ext i; simp)

theorem Good.bot (X : PT E) (c : ℝ) : Good X c ⊥ := by
  refine { le := bot_le, sat := ?_, stable := ?_, iso := ?_, sep := ?_ }
  ·
    intro x _ hx
    have : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := by simp [IR]
    rw [this] at hx
    simpa using hx
  ·
    intro α x hx
    rw [Submodule.mem_bot] at hx ⊢
    subst hx
    rw [act_eq_actE, actE_zero_right]
  ·
    intro x hx y _
    rw [Submodule.mem_bot] at hx
    subst hx
    exact Hf_im_zero_left y
  ·
    intro x _ u hu hne
    exfalso
    have : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := by simp [IR]
    have h1 := hu.1
    rw [this, Submodule.mem_bot] at h1
    exact hne h1

private lemma act_add_square_integrability {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  first
  | (ext i; simp [act, mul_add])
  | (unfold act; ext i; simp [mul_add])

private lemma act_real_smul {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (r : ℝ) (v : Vsp dim) :
    act α (r • v) = r • act α v := by
  first
  | (ext i; simp [act, Complex.real_smul]; ring)
  | (ext i; simp [act, mul_smul_comm])
  | (unfold act; ext i; simp [Complex.real_smul]; ring)

theorem Good.IR_stable {X : PT E} {c : ℝ} {I : Submodule ℤ (Vsp X.dim)} (hI : Good X c I)
    (α : 𝓞 E) : ∀ v ∈ IR I, act α v ∈ IR I := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hI.stable α x hx)
  | zero => rw [act_zero_square_integrability]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [act_add_square_integrability]; exact add_mem hx hy
  | smul r x _ hx => rw [act_real_smul]; exact Submodule.smul_mem _ r hx

private lemma Hf_add_left' {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

private lemma Hf_add_right' {ι : Type} [Fintype ι] (v w w' : EuclideanSpace ℂ ι) :
    Hf v (w + w') = Hf v w + Hf v w' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

private lemma im_Hf_real_smul_left {ι : Type} [Fintype ι] (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf (r • v) w).im = r * (Hf v w).im := by
  first
  | (simp only [Hf, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]; simp [Complex.mul_im])
  | (simp [Hf, Complex.real_smul, mul_assoc, ← Finset.mul_sum, Complex.mul_im])
  | (simp [Hf, Finset.mul_sum, Complex.mul_im, Complex.real_smul])

private lemma Hf_real_smul_right_im {ι : Type} [Fintype ι] (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf v (r • w)).im = r * (Hf v w).im := by
  first
  | (simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, mul_left_comm _ (r : ℂ), ← Finset.mul_sum]; simp [Complex.mul_im])
  | (simp [Hf, Complex.real_smul, mul_left_comm _ (r : ℂ), ← Finset.mul_sum, Complex.mul_im])
  | (simp [Hf, Finset.mul_sum, Complex.mul_im, Complex.real_smul])

theorem Good.IR_iso {X : PT E} {c : ℝ} {I : Submodule ℤ (Vsp X.dim)} (hI : Good X c I) :
    ∀ v ∈ IR I, ∀ w ∈ IR I, (Hf v w).im = 0 := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact hI.iso x hx y hy
    | zero => simp [Hf]
    | add y y' _ _ h1 h2 => rw [Hf_add_right', Complex.add_im, h1, h2, add_zero]
    | smul r y _ h => rw [Hf_real_smul_right_im, h, mul_zero]
  | zero => simp [Hf]
  | add x x' _ _ h1 h2 => rw [Hf_add_left', Complex.add_im, h1, h2, add_zero]
  | smul r x _ h => rw [im_Hf_real_smul_left, h, mul_zero]

theorem im_eq_zero_of_lt (X : PT E) {x y : Vsp X.dim} (hx : x ∈ X.L) (hy : y ∈ X.L)
    (h : |(Hf x y).im| < 1) : (Hf x y).im = 0 := by
  obtain ⟨k, hk⟩ := X.integral x y hx hy
  rw [hk] at h ⊢
  have hk1 : |k| < 1 := by exact_mod_cast h
  have hk0 : k = 0 := by
    rw [abs_lt] at hk1
    omega
  simp [hk0]

theorem one_le_abs_im (X : PT E) {x y : Vsp X.dim} (hx : x ∈ X.L) (hy : y ∈ X.L)
    (h : (Hf x y).im ≠ 0) : 1 ≤ |(Hf x y).im| := by
  obtain ⟨k, hk⟩ := X.integral x y hx hy
  rw [hk] at h ⊢
  have hk0 : k ≠ 0 := by exact_mod_cast h
  exact_mod_cast Int.one_le_abs hk0

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def PerFactor {X : PT E} {DF : ℕ} (P : Par X DF) (I : Submodule ℤ (Vsp X.dim))
    (s : (Fin 1 → Vsp X.dim) → ℂ) : Prop :=
  ∀ w : Vsp X.dim, ∃ y ∈ X.L, Real.sqrt (X.ptN2 1 s fun _ => w) / Real.sqrt (X.l2 1 s) ≤
    Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y‖ ^ 2)

theorem Par_ka0_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ka0 := by
  have h : (0 : ℝ) ≤ PT.rd E := by linarith [P.hrd]
  have hR : (0 : ℝ) ≤ RR (E := E) := by
    unfold RR
    exact pow_nonneg h 7
  unfold Par.ka0
  exact mul_nonneg (mul_nonneg (by norm_num) hR) (sq_nonneg _)

theorem tof_uMap_sq_smul {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (r1 : ℕ) (a y : Vsp dim) :
    ‖uMap I (((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y)‖ ^ 2 =
      (r1 : ℝ) ^ 4 * ‖uMap I a - uMap I y‖ ^ 2 := by
  have h : ((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y = ((r1 : ℝ) ^ 2) • (a - y) := by
    first
    | (rw [← smul_sub, ← Complex.coe_smul, Complex.ofReal_pow, Complex.ofReal_natCast])
    | (rw [← smul_sub]; norm_cast)
    | (rw [← smul_sub, ← Complex.coe_smul]; push_cast; rfl)
  rw [h, map_smul, map_sub, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  ring

theorem t_assemble [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hpf : PerFactor P I s)
    (r1 : ℕ) (hr1 : 2 ≤ r1) (a : Fin X.r → Vsp X.dim) (ha : ∀ j, ((r1 : ℂ) ^ 2) • a j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) (hph : 0 < P.ph) :
    ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
  choose y hyL hb using fun j => hpf (a j)
  set C : ℝ := Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) with hC
  set D : Fin X.r → ℝ := fun j => ‖uMap I (a j) - uMap I (y j)‖ ^ 2 with hD
  have hkp : 0 ≤ P.ka0 * P.ph := mul_nonneg (Par_ka0_nonneg P) hph.le
  have h1 : ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) :=
    Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hb j)
  have h2 : ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) =
      C ^ X.r * Real.exp (-(Real.pi / 2) * ∑ j, D j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, Finset.mul_sum]
  have h3 : C ^ X.r = Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) := by
    rw [hC, mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast ((P.ka0 * P.ph) ^ _),
      ← Real.rpow_mul hkp, Par.p3]
    congr 2; ring

  set xb : Fin X.r → Vsp X.dim := fun j => ((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • y j with hxb
  have hxL : ∀ j, xb j ∈ X.L ∧ IsU I (xb j) (uMap I (xb j)) := by
    intro j
    refine ⟨X.L.sub_mem (ha j) ?_, isU_uMap I _⟩
    have : ((r1 : ℂ) ^ 2) • y j = (r1 ^ 2 : ℕ) • y j := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; push_cast; rfl
    rw [this]; exact X.L.nsmul_mem (hyL j) _
  have hspan := tof_span_condition (X := X) I r1 hr1 a y hyL hgen
  have hu2 := hI.u2 X.r xb (fun j => uMap I (xb j)) hxL hspan
  have hsum : ∑ j, ‖uMap I (xb j)‖ ^ 2 / 2 = (r1 : ℝ) ^ 4 / 2 * ∑ j, D j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxb]; dsimp only
    rw [tof_uMap_sq_smul]; ring
  rw [hsum] at hu2
  have hr4 : (0 : ℝ) < (r1 : ℝ) ^ 4 := by
    have : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
    positivity
  have h4 : Real.exp (-(Real.pi / 2) * ∑ j, D j) ≤ Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
    apply Real.exp_le_exp.2
    have : Real.pi * P.ph / (r1 : ℝ) ^ 4 ≤ Real.pi / 2 * ∑ j, D j := by
      rw [div_le_iff₀ hr4]
      have := mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le
      nlinarith
    linarith
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ C ^ X.r * Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by rw [h3]

end

end ReciprocityTheory.ChartRestriction.G.I2
end
