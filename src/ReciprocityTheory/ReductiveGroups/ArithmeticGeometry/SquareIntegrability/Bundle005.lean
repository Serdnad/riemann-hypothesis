module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IntegrableNormPowMulExpNegMulNormSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

abbrev IR {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Submodule ℝ (Vsp dim) :=
  Submodule.span ℝ (I : Set (Vsp dim))

def IsU {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (x u : Vsp dim) : Prop :=
  u ∈ IR I ∧ ∀ a ∈ IR I, inner ℝ u a = (Hf x a).im

def InPart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : Prop := ∀ j : Idx dim, j.1 ≠ σ → v j = 0

def d1 {dim : (E →+* ℂ) → ℕ} (F : (Fin 1 → Vsp dim) → ℂ) (c : ℕ) (x : Fin c → Vsp dim) : ℂ :=
  iteratedFDeriv ℂ c F 0 (fun k _ => x k)

section

variable {DF : ℕ} {X : PT E}

def Par.th (P : Par X DF) : ℝ := ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0

def Par.eps1 (P : Par X DF) : ℝ :=
  7 * 2 ^ X.gA * (4.3 : ℝ) ^ dstar (E := E) P.m * Real.exp (-t0 (E := E) P.q P.R0)

def Par.K6 (P : Par X DF) : ℝ :=
  6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2)

structure IsSplit (P : Par X DF) (I : Submodule ℤ (Vsp X.dim)) : Prop where
  le : I ≤ X.L
  sat : ∀ x ∈ X.L, ∀ k : ℤ, k ≠ 0 → k • x ∈ I → x ∈ I
  stable : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I
  iso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0
  eps : ∀ x ∈ I, X.eps x = 1
  rank : ∃ ρ ≤ P.m, Module.finrank ℝ (IR I) = 2 * PT.f E * ρ
  ne_bot : I ≠ ⊥ ↔ X.la1 < P.th

  thick : ∀ x ∈ X.L, (∀ a ∈ I, (Hf x a).im = 0) → x ∉ I → P.th ≤ Metric.infDist x (IR I)

  sep : ∀ x ∈ X.L, ∀ u, IsU I x u → u ≠ 0 → b0 (E := E) P.q P.R0 ≤ ‖u‖ ^ 2

  u1 : ∃ x : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, ∃ u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim,
    (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧
      ∀ j, ‖u j‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)

  u2 : ∀ (k : ℕ) (x u : Fin k → Vsp X.dim), (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) →
    Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (x j)) w} = IR I →
      P.ph ≤ ∑ j, ‖u j‖ ^ 2 / 2

end

def SplitStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF),
    ∃ I, IsSplit P I

def CharStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ σ : E →+* ℂ, ∀ ρ : ℕ,
    Module.finrank ℂ ((Submodule.span ℂ (I : Set (Vsp X.dim))) ⊓
      {carrier := {v | InPart σ v}, add_mem' := fun {a b} ha hb j hj => by
          simp [ha j hj, hb j hj], zero_mem' := fun j _ => rfl,
        smul_mem' := fun c v hv j hj => by simp [hv j hj]} : Submodule ℂ (Vsp X.dim)) = ρ →
    ∃ (w : Fin ρ → Vsp X.dim) (x u : Fin ρ → Vsp X.dim) (R : Fin ρ → ℝ) (ε : Fin ρ → Fin ρ → ℂ),
      (∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim))) ∧
      (∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) ∧
      (∀ s, x s ∈ X.L ∧ IsU I (x s) (u s)) ∧
      (∀ s s', s < s' → ε s s' = 0) ∧
      (∀ s, Real.sqrt (∑ s', ‖ε s s'‖ ^ 2) ≤ 1 / (30 * ρ ^ 2) ∧
        ∑ s', ‖ε s s'‖ ≤ Real.sqrt ρ / (30 * ρ ^ 2)) ∧
      (∀ s v, InPart σ v → Hf v (u s) / R s = Hf v (w s) + ∑ s', ε s s' * Hf v (w s')) ∧
      (∀ s, ‖u s‖ ≤ 1.5 * R s ∧ 1 ≤ 2 * Real.pi * R s) ∧
      (∀ s, ∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ (u s) uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2) ∧
      (∀ s, ‖u s‖ ^ 2 ≤ Cchi (E := E) P.m * P.ph)

def ColTorusStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ (c : ℕ), c ≤ DF → ∀ (σ : E →+* ℂ)
    (x0 u : Vsp X.dim), x0 ∈ X.L → IsU I x0 u → ∀ n : ℝ, 1 ≤ n → 2 * Real.pi * ‖u‖ ≤ 1.5 * n →
    (∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ u uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2) →
    ∃ s' ∈ X.Sec P.q 1, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - ζ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) u‖ ≤ P.eps1 * n ^ c) ∧
      P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2 / P.q)) * X.l2 P.q s' ≤ n ^ (2 * c)

def ColAbelStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ (c : ℕ), c ≤ DF → ∀ (σ : E →+* ℂ)
    (ξ : Vsp X.dim), InPart σ ξ → ‖ξ‖ = 1 → (∀ a ∈ I, Hf ξ a = 0) →
    ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2

def ColEmptyStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I →
    ∃ s' ∈ X.Sec P.q 1, 1 / 2 ≤ ‖s' 0‖ ∧ P.K6⁻¹ * X.l2 P.q s' ≤ 1

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

def GT.Coc {ι : Type} [Fintype ι] (Y : GT ι) (q : ℕ) : Prop :=
  ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
    Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)


open scoped Classical in
open Classical in
def PropAStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q c : ℕ) (R0 : ℝ), 1 ≤ q → Y.Coc q → 0 < R0 →
    (∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) →
    270 ≤ R0 ^ 2 → 90 * ((Fintype.card ι : ℝ) + c) ≤ R0 ^ 2 →
    ∀ p : MvPolynomial ι ℂ, p.totalDegree ≤ c →
      ∃ β ∈ Y.Sec q,
        (∀ α : ι →₀ ℕ, α.degree ≤ c →
          polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
            polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1)
              (fun v : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => v i) p) 0) ∧
        Y.l2 q β ≤ 6 * ∫ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) p‖ ^ 2 *
          Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable def fa1M {g : ℕ} (α : Fin g →₀ ℕ) : ℝ :=
  (Real.pi ^ g)⁻¹ * ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)

theorem monomialMass_pos {g : ℕ} (α : Fin g →₀ ℕ) : 0 < fa1M α :=
  mul_pos (by positivity) (integral_norm_monomial_sq_gaussian_pos α)

theorem integral_norm_monomial_sq_gaussian_eq {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.pi ^ g * fa1M α := by
  unfold fa1M
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ Real.pi_ne_zero), one_mul]

noncomputable def fa1K {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) : ℝ :=
  ∑ α ∈ p.support, ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α

noncomputable def fa1N {g : ℕ} (p : MvPolynomial (Fin g) ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖AddMonoidAlgebra.coeff p α‖ ^ 2 * fa1M α

theorem monomialKernel_nonneg {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    0 ≤ fa1K p z := by
  unfold fa1K
  exact Finset.sum_nonneg fun α _ => div_nonneg (by positivity) (monomialMass_pos α).le

theorem coeffNormSq_nonneg {g : ℕ} (p : MvPolynomial (Fin g) ℂ) : 0 ≤ fa1N p := by
  unfold fa1N
  exact Finset.sum_nonneg fun α _ => mul_nonneg (by positivity) (monomialMass_pos α).le

theorem eval_eq_sum_coeff_mul_monomial {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    MvPolynomial.eval (fun i => z i) p = ∑ α ∈ p.support, AddMonoidAlgebra.coeff p α * monomialOfMultiindex α z := by
  first
  | (simp [MvPolynomial.eval_eq', monomialOfMultiindex]; done)
  | (simp [MvPolynomial.eval_eq, monomialOfMultiindex, Finsupp.prod]; done)
  | (rw [MvPolynomial.eval_eq']; unfold monomialOfMultiindex; done)

theorem norm_eval_sq_le {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖MvPolynomial.eval (fun i => z i) p‖ ^ 2 ≤ fa1N p * fa1K p z := by
  rw [eval_eq_sum_coeff_mul_monomial]
  have hM : ∀ α : Fin g →₀ ℕ, 0 < fa1M α := monomialMass_pos
  have h1 : ‖∑ α ∈ p.support, AddMonoidAlgebra.coeff p α * monomialOfMultiindex α z‖ ≤
      ∑ α ∈ p.support, (‖AddMonoidAlgebra.coeff p α‖ * Real.sqrt (fa1M α)) *
        (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun α _ => ?_))
    have hs : Real.sqrt (fa1M α) ≠ 0 := (Real.sqrt_pos.mpr (hM α)).ne'
    rw [norm_mul]
    first
    | (field_simp; done)
    | (field_simp; ring)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq p.support
    (fun α => ‖AddMonoidAlgebra.coeff p α‖ * Real.sqrt (fa1M α)) (fun α => ‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α))
  have h3 : ∀ α, (‖AddMonoidAlgebra.coeff p α‖ * Real.sqrt (fa1M α)) ^ 2 = ‖AddMonoidAlgebra.coeff p α‖ ^ 2 * fa1M α :=
    fun α => by rw [mul_pow, Real.sq_sqrt (hM α).le]
  have h4 : ∀ α, (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α)) ^ 2 = ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α :=
    fun α => by rw [div_pow, Real.sq_sqrt (hM α).le]
  simp only [h3, h4] at h2
  unfold fa1N fa1K
  calc _ ≤ (∑ α ∈ p.support, (‖AddMonoidAlgebra.coeff p α‖ * Real.sqrt (fa1M α)) *
        (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α))) ^ 2 := by gcongr
    _ ≤ _ := h2

theorem integrable_monomialKernel_mul_gaussian {g : ℕ} (p : MvPolynomial (Fin g) ℂ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K p z * Real.exp (-b * ‖z‖ ^ 2)) := by
  simp only [fa1K, Finset.sum_mul]
  refine integrable_finsetSum _ (fun α _ => ?_)
  have := (integrable_norm_monomial_sq_gaussian α hb).const_mul (fa1M α)⁻¹
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only; ring

theorem integral_monomialKernel_mul_gaussian {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-‖z‖ ^ 2) = Real.pi ^ g * p.support.card := by
  have hint : ∀ α : Fin g →₀ ℕ,
      MeasureTheory.Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    intro α
    by_contra h
    apply (monomialMass_pos α).ne'
    unfold fa1M
    rw [MeasureTheory.integral_undef h, mul_zero]
  unfold fa1K
  have hfun : (fun z : EuclideanSpace ℂ (Fin g) =>
      (∑ α ∈ p.support, ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α) * Real.exp (-‖z‖ ^ 2)) =
      fun z => ∑ α ∈ p.support, (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    funext z
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  rw [hfun, MeasureTheory.integral_finsetSum _ (fun α _ => (hint α).const_mul _)]
  have h2 : ∀ α ∈ p.support,
      ∫ z, (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) = Real.pi ^ g := by
    intro α _
    rw [MeasureTheory.integral_const_mul, integral_norm_monomial_sq_gaussian_eq, mul_comm (Real.pi ^ g), ← mul_assoc,
      inv_mul_cancel₀ (monomialMass_pos α).ne', one_mul]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  ring

theorem integral_monomialKernel_mul_gaussian_half {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      Real.pi ^ g * ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) := by
  simp only [fa1K, Finset.sum_mul]
  rw [integral_finsetSum _ (fun α _ => ?_)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    have : ∀ z : EuclideanSpace ℂ (Fin g),
        ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
        (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := fun z => by ring
    simp only [this]
    rw [integral_const_mul, integral_norm_monomial_sq_gaussian_half, integral_norm_monomial_sq_gaussian_eq]
    have := (monomialMass_pos α).ne'
    field_simp
  · have := (integrable_norm_monomial_sq_gaussian α (b := 1 / 2) (by norm_num)).const_mul (fa1M α)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring

theorem integral_mul_conj_gaussian_eq_coeffNormSq {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (F : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : ∀ z, F z = MvPolynomial.eval (fun i => z i) p) :
    (((Real.pi ^ g)⁻¹ : ℝ) : ℂ) * ∫ z, F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
      ((fa1N p : ℝ) : ℂ) := by
  have hexp : ∀ z, F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
      ∑ α ∈ p.support, ∑ β ∈ p.support,
        (AddMonoidAlgebra.coeff p α * (starRingEnd ℂ) (AddMonoidAlgebra.coeff p β)) *
          (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    intro z

    rw [hF, eval_eq_sum_coeff_mul_monomial, map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [map_mul]; ring
  simp only [hexp]
  have hint : ∀ α β : Fin g →₀ ℕ, Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      (AddMonoidAlgebra.coeff p α * (starRingEnd ℂ) (AddMonoidAlgebra.coeff p β)) *
        (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :=
    fun α β => (integrable_monomial_mul_conj_gaussian α β).const_mul _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hint α β))]
  have hin : ∀ α ∈ p.support, ∫ z : EuclideanSpace ℂ (Fin g), ∑ β ∈ p.support,
      (AddMonoidAlgebra.coeff p α * (starRingEnd ℂ) (AddMonoidAlgebra.coeff p β)) *
        (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) =
      (((‖AddMonoidAlgebra.coeff p α‖ ^ 2 * (Real.pi ^ g * fa1M α)) : ℝ) : ℂ) := by
    intro α hα
    rw [integral_finsetSum _ (fun β _ => hint α β)]
    rw [Finset.sum_eq_single_of_mem α hα (fun β _ hβ => by
      rw [integral_const_mul, integral_monomial_mul_conj_gaussian_eq_zero (Ne.symm hβ), mul_zero])]
    rw [integral_const_mul]
    have h1 : ∀ z : EuclideanSpace ℂ (Fin g),
        monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex α z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
          ((‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      intro z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    simp only [h1]
    rw [integral_complex_ofReal, integral_norm_monomial_sq_gaussian_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [Finset.sum_congr rfl hin, fa1N]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have : (Real.pi : ℂ) ^ g ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  field_simp

end ReciprocityTheory.ChartRestriction.G.I2
end
