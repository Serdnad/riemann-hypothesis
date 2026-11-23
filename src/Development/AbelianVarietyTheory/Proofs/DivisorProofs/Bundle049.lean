module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.Normed.Ring.Units

@[expose] public section

section

open scoped Matrix

namespace GlobalTheory

theorem siegel_fock_exists : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by
  intro V _ _ _ β J hsym hJJ hJ hpos
  set Φ : (V × V) →ₗ[ℝ] (V × V) :=
    LinearMap.inr ℝ V V ∘ₗ LinearMap.fst ℝ V V + J ∘ₗ LinearMap.inr ℝ V V ∘ₗ LinearMap.snd ℝ V V with hΦdef
  have hΦ : ∀ u : V × V, Φ u = (0, u.1) + J (0, u.2) := by
    intro u; simp [hΦdef]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hΦ] at hu
    have h1 : (J (0, u.2)).1 = 0 := by
      have := congrArg Prod.fst hu; simpa using this
    have hb : u.2 = 0 := by
      by_contra hne
      have := hpos (0, u.2) (by simpa using hne)
      simp [h1] at this
    have hJ0 : J (0, 0) = 0 := J.map_zero
    have ha : u.1 = 0 := by
      have := congrArg Prod.snd hu; simpa [hb, hJ0] using this
    exact Prod.ext ha hb
  set E := LinearEquiv.ofInjectiveEndo Φ hinj with hEdef
  have hE : ∀ w, Φ (E.symm w) = w := fun w => by
    show E (E.symm w) = w
    exact E.apply_symm_apply w
  have hJ0 : J (0, 0) = 0 := J.map_zero
  set A : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hAdef
  set B : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hBdef
  have hAB : ∀ p, E.symm (p, 0) = (A p, B p) := fun p => by simp [hAdef, hBdef]
  have hP0 : ∀ q, E.symm (0, q) = (q, 0) := fun q => by
    apply E.injective
    rw [E.apply_symm_apply]
    show (0, q) = Φ (q, 0)
    rw [hΦ]; simp [hJ0]
  have hsplit : ∀ w : V × V, E.symm w = (A w.1 + w.2, B w.1) := fun w => by
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    rw [hw, map_add (f := _), hAB, hP0]; simp
  have hJB : ∀ p, J (0, B p) = (p, -A p) := fun p => by
    have := hE (p, 0)
    rw [hAB, hΦ] at this
    have h2 : J (0, B p) = (p, 0) - (0, A p) := by rw [← this]; abel
    rw [h2]; simp
  have hPJ : ∀ w : V × V, E.symm (J w) = (-(E.symm w).2, (E.symm w).1) := fun w => by
    apply E.injective
    rw [E.apply_symm_apply]
    show J w = Φ _
    conv_lhs => rw [← hE w]
    rw [hΦ, hΦ, map_add (f := _), hJJ]
    ext <;> simp <;> abel
  have hAsym : ∀ x y, β x (A y) = β y (A x) := fun x y => by
    have := hJ (0, B x) (0, B y)
    rw [hJB, hJB] at this
    simp at this
    linarith
  have hBsym : ∀ x y, β x (B y) = β y (B x) := fun x y => by
    have := hJ (J (0, B x)) (0, B y)
    rw [hJJ, hJB, hJB] at this
    simp at this
    linarith
  have hBpos : ∀ x, x ≠ 0 → 0 < -β x (B x) := fun x hx => by
    have hne : ((0 : V), B x) ≠ 0 := by
      intro h0
      have h1 : J (0, B x) = 0 := by rw [h0]; exact J.map_zero
      rw [hJB] at h1
      exact hx (congrArg Prod.fst h1)
    have := hpos (0, B x) hne
    rw [hJB] at this
    simpa using this
  let Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ))
    (fun m₁ m₂ n => by simp; ring)
    (fun c m n => by simp; ring)
    (fun m n₁ n₂ => by simp; ring)
    (fun c m n => by simp; ring)
  let Q : V →L[ℝ] V →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ Q')
  have hQ : ∀ x y, Q x y = ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ) :=
    fun x y => rfl
  have hre : ∀ x, (Q x x).re = Real.pi * -β x (B x) := fun x => by
    rw [hQ]; simp
  have hscale : ∀ (t : ℝ) (y : V), Real.pi * -β (t • y) (B (t • y)) = t ^ 2 * (Real.pi * -β y (B y)) :=
    fun t y => by simp; ring
  have hcont : Continuous fun x => (Q x x).re := by fun_prop
  have hsym' : ∀ x y, Q x y = Q y x := fun x y => by rw [hQ, hQ, hAsym x y, hBsym x y]
  have hfock : ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) =
      Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := fun w x => by
    have e1 := hsplit (J w)
    rw [hPJ, hsplit w] at e1
    have h1 : A (J w).1 + (J w).2 = -(B w.1) := (congrArg Prod.fst e1).symm
    have h2 : B (J w).1 = A w.1 + w.2 := (congrArg Prod.snd e1).symm
    have hb1 : β x (A (J w).1) = -β x (B w.1) - β x (J w).2 := by
      have := congrArg (β x) h1; simp at this; linarith
    have hb2 : β x (B (J w).1) = β x (A w.1) + β x w.2 := by rw [h2]; simp
    rw [hQ, hQ, hb1, hb2]
    push_cast
    linear_combination (-((Real.pi : ℂ) * (β x (A w.1) : ℂ) + (Real.pi : ℂ) * (β x w.2 : ℂ))) * Complex.I_sq
  by_cases hs : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hs hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    refine ⟨Q, (Q u u).re, ?_, ?_, hsym', hfock⟩
    · rw [hre]; exact mul_pos Real.pi_pos (hBpos u hu0)
    · intro x
      by_cases hx : x = 0
      · subst hx; simp
      · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hu' : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
        have hm : (Q u u).re ≤ (Q (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := hmin hu'
        have key : Real.pi * -β x (B x) = ‖x‖ ^ 2 * (Real.pi * -β (‖x‖⁻¹ • x) (B (‖x‖⁻¹ • x))) := by
          rw [hscale]; field_simp
        rw [hre, hre] at hm
        rw [hre u, hre x, key]
        have := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖x‖)
        linarith
  · refine ⟨Q, 1, one_pos, ?_, hsym', hfock⟩
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      apply hs
      refine ⟨‖x‖⁻¹ • x, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory.TracelessSkewSpan

variable {r : ℕ}

noncomputable def skewSub (A : Matrix (Fin r) (Fin r) ℂ) :
    Submodule ℝ (Matrix (Fin r) (Fin r) ℂ) where
  carrier := {Y | Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    have h : (X + Y).map (starRingEnd ℂ) = X.map (starRingEnd ℂ) + Y.map (starRingEnd ℂ) := by
      ext i j; simp
    rw [transpose_add, h, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᵀ * A + A * X.map (starRingEnd ℂ)) + (Yᵀ * A + A * Y.map (starRingEnd ℂ)) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c Y hY
    simp only [Set.mem_setOf_eq] at *
    have h1 : (c • Y).map (starRingEnd ℂ) = c • Y.map (starRingEnd ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [transpose_smul, h1, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]

lemma mem_skewSub {A Y : Matrix (Fin r) (Fin r) ℂ} :
    Y ∈ skewSub A ↔ Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0 := Iff.rfl

lemma eq_zero_of_mem_of_I_smul_mem {A Y : Matrix (Fin r) (Fin r) ℂ} (hA : A.det ≠ 0)
    (h1 : Y ∈ skewSub A) (h2 : Complex.I • Y ∈ skewSub A) : Y = 0 := by
  rw [mem_skewSub] at h1 h2
  have hc : (Complex.I • Y).map (starRingEnd ℂ) = (-Complex.I) • Y.map (starRingEnd ℂ) := by
    ext i j; simp
  rw [transpose_smul, hc, Matrix.smul_mul, Matrix.mul_smul] at h2
  have h3 : Yᵀ * A - A * Y.map (starRingEnd ℂ) = 0 := by
    have : Complex.I • (Yᵀ * A - A * Y.map (starRingEnd ℂ)) = 0 := by
      rw [smul_sub, ← h2, neg_smul]; abel
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  have h4 : Yᵀ * A = 0 := by
    have : (2 : ℂ) • (Yᵀ * A) = 0 := by
      rw [two_smul]
      calc Yᵀ * A + Yᵀ * A = (Yᵀ * A + A * Y.map (starRingEnd ℂ)) + (Yᵀ * A - A * Y.map (starRingEnd ℂ)) := by abel
        _ = 0 := by rw [h1, h3, add_zero]
    rcases smul_eq_zero.mp this with h | h
    · norm_num at h
    · exact h
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have h5 : Yᵀ = 0 := by
    calc Yᵀ = Yᵀ * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
      _ = 0 := by rw [h4, Matrix.zero_mul]
  simpa using congrArg Matrix.transpose h5

lemma finrank_skewSub_mul_two_le {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.det ≠ 0) :
    2 * Module.finrank ℝ (skewSub A) ≤ 2 * (r * r) := by
  set u := skewSub A
  let f : (u × u) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ :=
    u.subtype ∘ₗ LinearMap.fst ℝ u u + (Complex.I • LinearMap.id) ∘ₗ u.subtype ∘ₗ LinearMap.snd ℝ u u
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hab' : (a : Matrix (Fin r) (Fin r) ℂ) + Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = 0 := by
      simpa [f] using hab
    have hIb : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) ∈ u := by
      have : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = -(a : Matrix (Fin r) (Fin r) ℂ) :=
        eq_neg_of_add_eq_zero_right hab'
      rw [this]; exact u.neg_mem a.2
    have hb : (b : Matrix (Fin r) (Fin r) ℂ) = 0 := eq_zero_of_mem_of_I_smul_mem hA b.2 hIb
    have ha : (a : Matrix (Fin r) (Fin r) ℂ) = 0 := by simpa [hb] using hab'
    ext1
    · exact Subtype.ext ha
    · exact Subtype.ext hb
  have := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex] at this
  simp only [Fintype.card_fin] at this
  linarith

theorem mem_span_of_linearIndependent {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.det ≠ 0)
    (v : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ) (hv : LinearIndependent ℝ v)
    (hvu : ∀ i, (v i)ᵀ * A + A * (v i).map (starRingEnd ℂ) = 0 ∧ (v i).trace = 0)
    (Y : Matrix (Fin r) (Fin r) ℂ) (hY : Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0)
    (hYt : Y.trace = 0) : Y ∈ Submodule.span ℝ (Set.range v) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have : Y = 0 := Subsingleton.elim _ _
    rw [this]; exact Submodule.zero_mem _
  set u := skewSub A
  set su := u ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin r) ℂ ℂ).restrictScalars ℝ)
  have hYsu : Y ∈ su := ⟨hY, by simpa using hYt⟩
  have hle : Submodule.span ℝ (Set.range v) ≤ su := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hvu i).1, by simpa using (hvu i).2⟩
  have hIu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∈ u := by
    rw [mem_skewSub]
    have hc : (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)).map (starRingEnd ℂ)
        = (-Complex.I) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, neg_smul, add_neg_cancel]
  have hIsu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∉ su := by
    rintro ⟨-, h⟩
    have h' : Matrix.trace (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)) = 0 := by simpa using h
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at h'
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact Complex.I_ne_zero h''
    · exact absurd (by exact_mod_cast h'' : r = 0) hr.ne'
  have hlt : su < u := lt_of_le_of_ne inf_le_left (fun h => hIsu (h ▸ hIu))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : 2 * Module.finrank ℝ u ≤ 2 * (r * r) := finrank_skewSub_mul_two_le hA
  have hspan := finrank_span_eq_card hv
  rw [Fintype.card_fin] at hspan
  have heq : Submodule.span ℝ (Set.range v) = su := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hspan, sq]
    change Module.finrank ℝ su ≤ r * r - 1
    generalize r * r = n at h2 ⊢
    omega
  rw [heq]; exact hYsu

end GlobalTheory.TracelessSkewSpan
end

section

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GlobalTheory.JSW

variable {n : ℕ}

def htGL (g : GL (Fin n) ℂ) : ℝ :=
  1 + ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ + ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖

def levSet (n r : ℕ) : Set (GL (Fin n) ℂ) :=
  {g | ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
    (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}

def rowCut (ρ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ := fun j => if j ≤ ρ then x ρ j else 0

def secMat (ρ j : Fin n) (v : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i l => if i = ρ then (if l ≤ ρ then v l else 0) else if l = Equiv.swap j ρ i then 1 else 0


open Classical in
def toGL (x : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n) ℂ := if h : IsUnit x then h.unit else 1

theorem val_toGL {x : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit x) : (toGL x : Matrix (Fin n) (Fin n) ℂ) = x := by
  simp [toGL, h]

theorem one_le_htGL (g : GL (Fin n) ℂ) : 1 ≤ htGL g := by
  unfold htGL
  have h1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  linarith

theorem htGL_pos (g : GL (Fin n) ℂ) : 0 < htGL g := lt_of_lt_of_le one_pos (one_le_htGL g)

theorem htGL_inv (g : GL (Fin n) ℂ) : htGL g⁻¹ = htGL g := by
  unfold htGL; rw [inv_inv]; ring

theorem sum_norm_mul_le (a b : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖(a * b) i j‖ ≤ (∑ i, ∑ j, ‖a i j‖) * ∑ i, ∑ j, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(a * b) i j‖ ≤ ∑ j, ∑ l, ‖a i l‖ * ‖b l j‖ :=
        Finset.sum_le_sum fun j _ => by
          rw [Matrix.mul_apply]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
    _ = ∑ l, ‖a i l‖ * ∑ j, ‖b l j‖ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ l, ‖a i l‖ * ∑ l', ∑ j, ‖b l' j‖ :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun l' => ∑ j, ‖b l' j‖) (fun _ _ => by positivity) (Finset.mem_univ l))
          (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem htGL_mul_le (g h : GL (Fin n) ℂ) : htGL (g * h) ≤ htGL g * htGL h := by
  unfold htGL
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have h1 := sum_norm_mul_le (g : Matrix (Fin n) (Fin n) ℂ) h
  have h2 := sum_norm_mul_le ((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (g⁻¹ : GL (Fin n) ℂ)
  have a1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a3 : 0 ≤ ∑ i, ∑ j, ‖(h : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a4 : 0 ≤ ∑ i, ∑ j, ‖((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  nlinarith [mul_nonneg a1 a4, mul_nonneg a2 a3]

theorem norm_entry_le_htGL (g : GL (Fin n) ℂ) (i j : Fin n) : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ htGL g := by
  unfold htGL
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h1 : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ :=
    (Finset.single_le_sum (f := fun j => ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ i))
  linarith

theorem continuous_htGL : Continuous (htGL : GL (Fin n) ℂ → ℝ) := by
  have h1 : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) ℂ => ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    Units.continuous_coe_inv
  unfold htGL
  fun_prop

theorem isOpenEmbedding_valGL :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) ℂ => fun i j => (g : Matrix (Fin n) (Fin n) ℂ) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) ℂ)

theorem measurable_comp_GL {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) ℂ → β} (hF : Continuous F) {γ : X → GL (Fin n) ℂ}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) ℂ) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) ℂ) := borel _
  haveI : BorelSpace (GL (Fin n) ℂ) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGL.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem measurable_dual {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {η : X → Z →L[ℝ] ℝ} (h : ∀ z, Measurable fun x => η x z) : Measurable η := by
  let b := Module.finBasis ℝ Z
  have : η = fun x => ∑ i, η x (b i) • LinearMap.toContinuousLinearMap (b.coord i) := by
    funext x
    ext z

    conv_lhs => rw [← b.sum_repr z, map_sum]
    simp only [map_smul]
    simp [mul_comm]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => (h _).smul_const _


end GlobalTheory.JSW
end
end

section

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem sq_le_sum_enorm_sq_lintegral_bound
    (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ) (hg : ∀ a, Continuous (g a))
    (hfg : ∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) :
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  by_cases hi : MeasureTheory.Integrable (fun x => f x ^ 2) μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi
      (MeasureTheory.ae_of_all _ (fun x => sq_nonneg (f x)))]
    have hm : ∀ a, Measurable (fun x => ‖g a x‖ₑ ^ 2) := fun a =>
      ((hg a).measurable.enorm).pow_const 2
    calc ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 ∂μ := by
          refine MeasureTheory.lintegral_mono (fun x => ?_)
          calc ENNReal.ofReal (f x ^ 2) ≤ ENNReal.ofReal (C * ∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_le_ofReal (hfg x)
            _ = ENNReal.ofReal C * ENNReal.ofReal (∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_mul' (Finset.sum_nonneg (fun a _ => sq_nonneg _))
            _ = ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 := by
                rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
                congr 1
                refine Finset.sum_congr rfl (fun a _ => ?_)
                rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      _ = ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
          rw [MeasureTheory.lintegral_const_mul _ (Finset.measurable_sum _ (fun a _ => hm a))]
          congr 1
          exact MeasureTheory.lintegral_finsetSum Finset.univ (fun a _ => hm a)
  · rw [MeasureTheory.integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

end GlobalTheory
end
