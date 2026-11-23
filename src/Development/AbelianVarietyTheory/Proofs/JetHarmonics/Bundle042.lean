module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle027
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle028
public import Formalism.HermitianCurvature.StatementU
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle039
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle034
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt

@[expose] public section

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem hhJ_nonneg_of_cloud_eigen : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∀ s : Fin n, s.val + 1 < kk → splitCas E x = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • x → 0 ≤ (hhJ ε x x).re := by
  intro M _ _ n ε E μ kk j bv x hM hS hj hL s hs hx
  obtain ⟨hb, hω, hζ⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj
  have hO := GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hM hS hj hL
  set ζ : ℝ := -μ s + (1 - (n : ℝ)) / 2 with hζdef
  have hζs : ζ ≤ bv / 32 := ((hζ s).1 hs).2
  have hnode : ∀ c : Fin n, kk ≤ c.val + 1 →
      (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 ≤ ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 := by
    intro c hc
    have h1 := (GlobalTheory.wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hM.2.1 (hL c).2).2.1 c (ζ : ℂ)
      (15 * bv / 16) (by positivity) (by
        intro ω hw
        have h2 := ((hω ω hw c).2 hc).1
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
        have := neg_abs_le (ζ + ω c)
        linarith)
    have h3 := congrFun hx c
    simp only [splitCas, Pi.smul_apply] at h3
    rw [← Finset.add_sum_erase univ (fun a => E c a (x a)) (mem_univ c)] at h3
    have h4 : (ζ : ℂ) • x c + E c c (x c) = -∑ a ∈ univ.erase c, E c a (x a) := by
      rw [← h3]; abel
    rw [h4, norm_neg] at h1
    exact h1
  have hterm : ∀ c : Fin n, (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 - 2 * ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 ≤
      (15 * bv / 16) ^ 2 * ((if ε c then 1 else -1) * ⟪x c, x c⟫_ℂ : ℂ).re := by
    intro c
    have hin : (⟪x c, x c⟫_ℂ : ℂ).re = ‖x c‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x c)
    by_cases he : ε c = true
    · rw [if_pos he, one_mul, hin]
      have := sq_nonneg ‖∑ a ∈ univ.erase c, E c a (x a)‖
      linarith
    · have hc : kk ≤ c.val + 1 := by
        by_contra h
        exact he (hS.2.2.2.1 c (not_le.mp h)).1
      rw [if_neg he, neg_one_mul, Complex.neg_re, hin]
      have := hnode c hc
      linarith
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin n))) => hterm c)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum] at hsum
  have hS0 : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hpos : 0 < (15 * bv / 16) ^ 2 := by positivity
  have hkey : 0 ≤ (15 * bv / 16) ^ 2 * (hhJ ε x x).re := by
    unfold hhJ
    have : 0 ≤ bv ^ 2 * ∑ c, ‖x c‖ ^ 2 := mul_nonneg (sq_nonneg _) hS0
    nlinarith
  exact (mul_nonneg_iff_of_pos_left hpos).mp hkey

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem splitCasRes_norm_sq_le_weighted {M : Type} [NormedAddCommGroup M] (u v : M) :
    ‖u‖ ^ 2 ≤ 15 / 13 * ‖u + v‖ ^ 2 + 15 / 2 * ‖v‖ ^ 2 := by
  have htri : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc ‖u‖ = ‖(u + v) - v‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le _ _
  have hsq : ‖u‖ ^ 2 ≤ (‖u + v‖ + ‖v‖) ^ 2 := by gcongr
  nlinarith [sq_nonneg (2 * ‖u + v‖ - 13 * ‖v‖)]

theorem splitCasRes_norm_add_sq_le {M : Type} [NormedAddCommGroup M] (u v : M) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    gcongr
    exact norm_add_le u v
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem splitCasRes_circle_dist (b t : ℝ) (ζ : ℂ) (hζ : ‖ζ + ((b / 16 : ℝ) : ℂ)‖ = 9 * b / 16)
    (ht : (-b / 8 - b / 32 ≤ -t ∧ -t ≤ b / 32) ∨ b - b / 32 ≤ -t) :
    15 * b / 32 ≤ ‖ζ + (t : ℂ)‖ := by
  have hb : 0 ≤ b := by
    have := norm_nonneg (ζ + ((b / 16 : ℝ) : ℂ))
    linarith
  have hsplit : ζ + (t : ℂ) = (ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ) := by
    push_cast
    ring
  have hshift : ‖((t - b / 16 : ℝ) : ℂ)‖ = |t - b / 16| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hsplit]
  rcases ht with ⟨h1, h2⟩ | h3
  ·
    have hclose : |t - b / 16| ≤ 3 * b / 32 := by
      rw [abs_le]
      constructor <;> linarith
    have key := norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) ((t - b / 16 : ℝ) : ℂ)
    rw [add_sub_cancel_right, hζ, hshift] at key
    linarith
  ·
    have hfar : 33 * b / 32 ≤ |t - b / 16| := by
      have := neg_le_abs (t - b / 16)
      linarith
    have key := norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) (ζ + ((b / 16 : ℝ) : ℂ))
    rw [add_sub_cancel_left, hζ, hshift] at key
    linarith

theorem splitCas_resolvent_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → (∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → (13 * bv / 32) ^ 2 * ∑ c, ‖x c‖ ^ 2 ≤ ∑ c, ‖ζ • x c - splitCas E x c‖ ^ 2) ∧ ∑ c, ‖splitCas E x c‖ ^ 2 ≤ (3 * bv) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hshape hj hlev
  obtain ⟨hbv, hω, -⟩ := shape_position n kk j ε μ bv hshape hj
  have hun : IsUnitary ε E := hmod.2.1
  have hoff : ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 :=
    GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hmod hshape hj hlev
  have hsplit : ∀ b, splitCas E x b = -(E b b (x b) + ∑ c ∈ univ.erase b, E b c (x c)) := by
    intro b
    simp only [splitCas]
    congr 1
    exact (Finset.add_sum_erase univ (fun c => E b c (x c)) (Finset.mem_univ b)).symm
  have hdiag := fun c => wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hun (hlev c).2
  have hS : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  constructor
  · intro ζ hζ
    have hlow : ∀ b, (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2 ≤ ‖ζ • x b + E b b (x b)‖ ^ 2 := by
      intro b
      refine (hdiag b).2.1 b ζ (15 * bv / 32) (by positivity) ?_
      intro ω hωn
      apply splitCasRes_circle_dist bv (ω b) ζ hζ
      obtain ⟨h1, h2⟩ := hω ω hωn b
      by_cases hb : b.val + 1 < kk
      · exact Or.inl (h1 hb)
      · exact Or.inr (h2 (by omega)).1
    have hper : ∀ b, 13 / 15 * (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2
        - 13 / 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ ‖ζ • x b - splitCas E x b‖ ^ 2 := by
      intro b
      have hw := splitCasRes_norm_sq_le_weighted (ζ • x b + E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))
      have he : ζ • x b - splitCas E x b
          = (ζ • x b + E b b (x b)) + ∑ c ∈ univ.erase b, E b c (x c) := by
        rw [hsplit]
        abel
      rw [he]
      nlinarith [hlow b]
    have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    nlinarith [hoff, hsum, mul_nonneg (sq_nonneg bv) hS]
  · have hD : ∀ b, ‖E b b (x b)‖ ^ 2 ≤ (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 := by
      intro b
      refine (hdiag b).2.2 b (65 * bv / 32) ?_
      intro ω hωn
      obtain ⟨h1, h2⟩ := hω ω hωn b
      rw [abs_le]
      by_cases hb : b.val + 1 < kk
      · obtain ⟨a1, a2⟩ := h1 hb
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := h2 (by omega)
        constructor <;> linarith
    have hper : ∀ b, ‖splitCas E x b‖ ^ 2
        ≤ 2 * (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 + 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 := by
      intro b
      rw [hsplit, norm_neg]
      have ha := splitCasRes_norm_add_sq_le (E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))
      nlinarith [hD b]
    have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    nlinarith [hoff, hsum, mul_nonneg (sq_nonneg bv) hS]

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_io_pr_single : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  intro M _ _ n ε E N _ _ F io pr μ j w hE hF hT hw s c d
  obtain ⟨hc, hwt⟩ := hw
  have hn : (1 : ℝ) ≤ n := by
    have : 0 < n := Fin.pos s
    exact_mod_cast this
  have hsq : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE hF hT h0 hc s c
    have h2 := GlobalTheory.T.compactCasimirBound_embedded_component M n ε E N F io pr _ s _ hE hF hT (by linarith) h1 d
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := h2
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by linarith)
    push_cast
    nlinarith
  · have h1 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) j hT).1 w hwt s c
    have h2 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) (j + 1) hT).2 s _ h1 d
    have e : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 1 + 1 := by push_cast; ring
    rw [e]
    exact h2

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M), IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_gl_size | exact GlobalTheory.lev_gl_size | (intros; apply GlobalTheory.lev_gl_size <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear : ∀ (k r : ℕ) (i j : Fin (2 * r + k + 1)), (∃ co : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ, ∀ g ∈ B.GV k r, star (g i j) = ∑ a, ∑ b, co a b * g⁻¹ a b) ∧ ∃ q : B.Mat k r → ℂ, U.IsPolyDeg 1 q ∧ ∀ g ∈ B.GV k r, g⁻¹ i j = q g := by
  first | exact @GlobalTheory.unitary_conj_entry_and_inv_entry | exact GlobalTheory.unitary_conj_entry_and_inv_entry | (intros; apply GlobalTheory.unitary_conj_entry_and_inv_entry <;> assumption)
end

section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem exists_addHom_tensor_int_of_biadditive {M N P : Type} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (f : M → N → P) (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n)
    (h2 : ∀ m n n', f m (n + n') = f m n + f m n') :
    ∃ g : M ⊗[ℤ] N →+ P, ∀ m n, g (m ⊗ₜ[ℤ] n) = f m n := by
  let F : M →+ N →+ P := AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (f m) (h2 m))
    (fun m m' => by ext n; exact h1 m m' n)
  refine ⟨TensorProduct.liftAddHom F (fun r m n => ?_), fun m n => ?_⟩
  · rw [map_zsmul, map_zsmul]; rfl
  · rw [TensorProduct.liftAddHom_tmul]; rfl

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem datum_character_eq_zpow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    {F : Type} [Field F] {M : ℕ} (hM : 0 < M) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M)
    (φ : Dw.La →+ Additive Fˣ) (hφ : ∀ a, φ (M • a) = 0) :
    ∃ d : Dw.La, ∀ a, Additive.toMul (φ a) = ζ ^ Dw.EF a d := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : Module.Projective ℤ Dw.La := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 Dw.proj
    haveI : Module.Free ℤ (Dw.La →₀ 𝓞 E) := inferInstance
    exact Module.Projective.of_split (s.restrictScalars ℤ)
      ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hs x)
  let f : ℤ →ₗ[ℤ] Additive Fˣ := LinearMap.toSpanSingleton ℤ (Additive Fˣ) (Additive.ofMul ζ)
  have hmem : ∀ a, φ.toIntLinearMap a ∈ LinearMap.range f := by
    intro a
    have h1 : Additive.toMul (φ a) ∈ rootsOfUnity M F := by
      rw [mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul, hφ]; rfl
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_mem_rootsOfUnity h1
    refine ⟨i, ?_⟩
    change (i : ℤ) • Additive.ofMul ζ = φ a
    rw [natCast_zsmul, ← ofMul_pow, hi]; rfl
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property f.rangeRestrict
    (φ.toIntLinearMap.codRestrict _ hmem) f.surjective_rangeRestrict
  obtain ⟨d, hd⟩ := Dw.unimod.2 ψ
  refine ⟨-d, fun a => ?_⟩
  have skew : Dw.EF a (-d) = ψ a := by
    have := Dw.alt (d + a)
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at this
    rw [map_neg, ← hd]
    linarith
  have h2 : f (ψ a) = φ a := congrArg Subtype.val (LinearMap.congr_fun hψ a)
  rw [skew, ← h2]
  rfl

theorem character_eq_weil_pairing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] (A : PolAV (Sp (FractionRing R))), letI := H.starRing; ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a) (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N k : ℕ), 1 ≤ N → 1 ≤ k → Nat.Coprime N k → ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 → ∀ κ : (TFK (R := R) F ⟶ A.A) → Fˣ, (∀ z z', z ≫ oA.act β = 1 → z' ≫ oA.act β = 1 → κ (z * z') = κ z * κ z') → ∃ b : TFK (R := R) F ⟶ A.A, b ≫ oA.act (star β) = 1 ∧ ∀ z, z ≫ oA.act β = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z b (unitOn (κ z)) := by
  intro E _ _ _ H R _ _ F _ _ A
  let _ := H.starRing
  intro oA Dw I N k hN hk hco β u u' hβ huu κ hκ
  have hM : 0 < k * N := Nat.mul_pos hk hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev (k * N) (c • b) = I.ev (k * N) b ≫ oA.act c := fun c b => I.lin _ c b
  obtain ⟨t, k', htk⟩ := (Nat.isCoprime_iff_coprime.2 hco).map (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at htk
  obtain ⟨ε, w, v, hw, hv⟩ : ∃ ε w v : 𝓞 E, β * ε = ((k * N : ℕ) : 𝓞 E) * w ∧ 1 = ε + v * β := by
    refine ⟨k * k' * u' * star β, k' * u', star β * t + k * k' * u, ?_, ?_⟩
    · push_cast
      rw [← hβ]; ring
    · linear_combination (-(k * k' : 𝓞 E)) * huu - htk - t * hβ
  have hzero : ∀ (c : 𝓞 E) (a : Dw.La), I.ev (k * N) ((((k * N : ℕ) : 𝓞 E) * c) • a) = 1 := by
    intro c a
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact (I.ker _ hM _).2 ⟨_, rfl⟩
  have hkill : ∀ a, I.ev (k * N) (ε • a) ≫ oA.act β = 1 := by
    intro a
    rw [← hlin, smul_smul, hw, hzero]
  have hfix : ∀ a, I.ev (k * N) a ≫ oA.act β = 1 → I.ev (k * N) (ε • a) = I.ev (k * N) a := by
    intro a ha
    obtain ⟨f, hf⟩ := (I.ker _ hM (β • a)).1 (by rw [hlin]; exact ha)
    have h1 : a = ε • a + (k * N) • (v • f) := by
      rw [smul_comm (k * N) v f, ← hf, smul_smul, ← add_smul, ← hv, one_smul]
    conv_rhs => rw [h1, I.add, (I.ker _ hM _).2 ⟨_, rfl⟩, _root_.mul_one]
  let φ : Dw.La →+ Additive Fˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (κ (I.ev (k * N) (ε • a))))
    (fun a b => by rw [smul_add, I.add, hκ _ _ (hkill a) (hkill b), ofMul_mul])
  have hφ : ∀ a, φ ((k * N) • a) = 0 := by
    intro a
    rw [← map_zero φ]
    change Additive.ofMul (κ (I.ev (k * N) (ε • (k * N) • a))) = Additive.ofMul (κ (I.ev (k * N) (ε • 0)))
    rw [smul_comm ε (k * N) a, (I.ker _ hM _).2 ⟨_, rfl⟩, smul_zero,
      (I.ker _ hM 0).2 ⟨0, (smul_zero _).symm⟩]
  obtain ⟨d, hd⟩ := datum_character_eq_zpow Dw hM (I.ζ_prim _ hM) φ hφ
  refine ⟨I.ev (k * N) (H.bar ε • d), ?_, fun z hz => ?_⟩
  · rw [← hlin, smul_smul]
    change I.ev (k * N) ((H.bar β * H.bar ε) • d) = 1
    rw [← map_mul, hw, map_mul, map_natCast, hzero]
  · have hzN : z ^ N = 1 := pow_eq_one_of_kill oA.toRingAct (by rw [_root_.mul_comm]; exact hβ) z hz
    obtain ⟨a, rfl⟩ := (I.onto _ hM z).1 (by rw [pow_mul', hzN, one_pow])
    have h1 : κ (I.ev (k * N) a) = I.ζ (k * N) ^ Dw.EF a (H.bar ε • d) := by
      rw [← Dw.adj, ← hd]
      change _ = κ (I.ev (k * N) (ε • ε • a))
      rw [hfix _ (hkill a), hfix a hz]
    rw [h1]
    exact I.isom _ hM _ _

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lift_point_translation_fieldPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  first | exact @GlobalTheory.exists_lift_translT | exact GlobalTheory.exists_lift_translT | (intros; apply GlobalTheory.exists_lift_translT <;> assumption)
end
