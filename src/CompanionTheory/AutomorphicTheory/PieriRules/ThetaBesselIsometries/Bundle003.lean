module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bessel_nonzero_on_translates : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDG ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  intro hH k r ε mu R Wp _ _ _ _ z π l hds hB hnz
  obtain ⟨⟨-, -, hKF, -⟩, hCyc, -⟩ := hH
  have hex : ∃ w0, PI.UpqRep.IsLowUnitH k r ε mu R.σ w0 := by
    obtain ⟨P, hP, -, -, -, -, -, ⟨S, hS⟩, -⟩ := hds.2
    obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, P, hP, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · exact Submodule.smul_mem _ _ (Submodule.mem_sSup.mpr fun N hN => hN S hS hvS)
  obtain ⟨w0, hlow⟩ := hex
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  by_contra hcon
  push_neg at hcon
  obtain ⟨w, hw, hlw⟩ := hnz
  refine hlw (Formalism.FourierDecayAlt.P.bessel_ne_zero_of_cyclic_orbit hCyc hKF k r ε mu R.H R.σ w0 Wp z Formalism.QuantumDeterminants.cStd π hds.1 hds.2 hlow
    l hB (fun x hx => hcon x ?_) w hw)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hg, w0, hwK, rfl⟩

end GlobalTheory
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensForm

theorem common_bound {ι α β : Type} [DecidableEq ι] (P : α → Prop) (S : Set β) (n : α → β → ℝ)
    (hn : ∀ a v, 0 ≤ n a v) (f : ι → β → ℝ)
    (h : ∀ c, ∃ (C : ℝ) (L : List α), (∀ a ∈ L, P a) ∧ ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum)
    (s : Finset ι) :
    ∃ (C : ℝ) (L : List α), 0 ≤ C ∧ (∀ a ∈ L, P a) ∧
      ∀ c ∈ s, ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum := by
  have hs : ∀ (L : List α) v, 0 ≤ (L.map fun a => n a v).sum := by
    intro L v
    apply List.sum_nonneg
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact hn a v
  induction s using Finset.induction_on with
  | empty => exact ⟨0, [], le_rfl, by simp, by simp⟩
  | insert c s _ ih =>
    obtain ⟨C, L, hC, hL, hb⟩ := ih
    obtain ⟨C', L', hL', hb'⟩ := h c
    refine ⟨C + |C'|, L ++ L', by positivity, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hL a ha
      · exact hL' a ha
    · intro d hd v hv
      rw [List.map_append, List.sum_append]
      have h1 := hs L v
      have h2 := hs L' v
      have h3 := abs_nonneg C'
      have h4 := le_abs_self C'
      rcases Finset.mem_insert.1 hd with rfl | hd
      · have := hb' v hv
        nlinarith [mul_nonneg hC h1, mul_nonneg hC h2, mul_nonneg h3 h1,
          mul_le_mul_of_nonneg_right h4 h2]
      · have := hb d hd v hv
        nlinarith [mul_nonneg hC h2, mul_nonneg h3 h1, mul_nonneg h3 h2]

variable {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hh_act (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (R : Rep k r) (g : Mx k r)
    (hρ : (ρ g)ᴴ * Γ * ρ g = Γ) (hσ : ∀ v, ‖R.σ g v‖ = ‖v‖) (x y : ι → R.H) :
    hh Γ R (act ρ R g x) (act ρ R g y) = hh Γ R x y := by
  have hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 hσ
  conv_rhs => rw [← hρ]
  simp only [hh, act, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hiso, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ b, ∑ a, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) :=
        Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ a, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [RCLike.star_def]
        ring


omit [DecidableEq ι] in
theorem norm_hh_le (Γ : Matrix ι ι ℂ) (R : Rep k r) (x y : ι → R.H) (A B : ℝ)
    (hx : ∀ c, ‖x c‖ ≤ A) (hy : ∀ c, ‖y c‖ ≤ B) :
    ‖hh Γ R x y‖ ≤ (∑ i, ∑ j, ‖Γ i j‖) * (A * B) := by
  rw [hh, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _)
  rw [mul_comm A B]
  exact mul_le_mul (hy i) (hx j) (norm_nonneg _) ((norm_nonneg _).trans (hy i))

theorem family_bound (R R' : Rep k r) (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c)) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ c, ∀ v ∈ R.sm, ‖T c v‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖).sum := by
  obtain ⟨C, L, -, hL, hb⟩ := common_bound (fun W : List (Mx k r) => ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) R.sm
    (fun W v => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖) (fun _ _ => norm_nonneg _)
    (fun c v => ‖T c v‖) (fun c => (hT c).cont [] (by simp)) Finset.univ
  exact ⟨C, L, hL, fun c => hb c (Finset.mem_univ c)⟩

theorem pulledBack_isInvForm : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR _ hF hT I J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y _
    simp only [hh, fun c => (hT.io_sm I c).add x hx x' hx', inner_add_right, mul_add, Finset.sum_add_distrib]
  · intro a x hx y _
    simp only [hh, fun c => (hT.io_sm I c).smul a x hx, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · intro x _ y hy y' hy'
    simp only [hh, fun c => (hT.io_sm J c).add y hy y' hy', inner_add_left, mul_add, Finset.sum_add_distrib]
  · intro a x _ y hy
    simp only [hh, fun c => (hT.io_sm J c).smul a y hy, inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [RCLike.star_def]; ring
  · intro g hg x hx y hy
    show hh Γ R (fun c => io I c ((RI I).σ g x)) (fun c => io J c ((RI J).σ g y)) = _
    rw [hT.io_eq I g hg x hx, hT.io_eq J g hg y hy]
    exact hh_act ρ Γ R g (hF.2.2.2.2.1 g hg) ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2 g hg) _ _
  · obtain ⟨C, Ws, hW, hb⟩ := family_bound (RI I) R (io I) (hT.io_sm I)
    obtain ⟨C', Ws', hW', hb'⟩ := family_bound (RI J) R (io J) (hT.io_sm J)
    refine ⟨(∑ i, ∑ j, ‖Γ i j‖) * C * C', Ws, Ws', ?_, ?_⟩
    · intro W hWm
      rcases List.mem_append.1 hWm with h | h
      · exact hW W h
      · exact hW' W h
    · intro x hx y hy
      refine (norm_hh_le Γ R _ _ _ _ (fun c => hb c x hx) (fun c => hb' c y hy)).trans (le_of_eq ?_)
      ring

end GlobalTheory.TensForm
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupMeas

theorem isDS_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDG ε μ) (v : R.H) : ContinuousOn (fun g => R.σ g v) (GG k r) := by
  obtain ⟨P, hP, -, -, ⟨-, -, hc⟩, -⟩ := h.2
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have := (hc v).comp h3.continuousOn hmaps
  simpa only [Function.comp_def, e] using this

theorem isCoef_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {l : R.H → Wp} {l' : R.H → Wq} {F : Mx k r → (Wq →L[ℂ] Wp)} {s : ℂ}
    (h : R.IsDG ε μ) (hF : IsCoef R l l' F s) : ContinuousOn F (GG k r) := by
  obtain ⟨m, x, y, X, -, hF, -⟩ := hF
  refine ContinuousOn.congr ?_ hF
  exact continuousOn_finsetSum _ fun i _ =>
    (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (isDS_continuousOn h (y i))).smul continuousOn_const

end GlobalTheory.SupMeas
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensAdj

section
variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_left (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (y : ι → R.H) :
    hh Γ R (fun c => ∑ I, f I c) y = ∑ I, hh Γ R (f I) y := by
  simp only [hh, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (x : ι → R.H) :
    hh Γ R x (fun c => ∑ I, f I c) = ∑ I, hh Γ R x (f I) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem sum_sm (R : Rep k r) (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) : ∑ c, x c ∈ R.sm :=
  R.smSub.sum_mem (t := univ) (f := x) fun c _ => hx c

omit [DecidableEq ι] in
theorem hh_tm (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) (v : R.H) :
    hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ := by
  simp only [hh, tm, ev, inner_sum, inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

theorem norm_sq_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Γ : Matrix ι ι ℂ}
    (h : Γᴴ * Γ = 1) (x : ι → H) : ∑ i, ‖∑ j, Γ i j • x j‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have key : ∑ i, ⟪∑ j, Γ i j • x j, ∑ j, Γ i j • x j⟫_ℂ = ∑ i, ⟪x i, x i⟫_ℂ := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ j, ∑ i, Γ i l * ((starRingEnd ℂ) (Γ i j) * ⟪x j, x l⟫_ℂ)
        = (if j = l then 1 else 0) * ⟪x j, x l⟫_ℂ := by
      intro j
      have := congrFun (congrFun h j) l
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [← this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [conjTranspose_apply, RCLike.star_def]
      ring
    simp only [h2]
    simp
  simp only [inner_self_eq_norm_sq_to_K] at key
  exact_mod_cast key

theorem norm_hh_le {Γ : Matrix ι ι ℂ} (h : Γᴴ * Γ = 1) (R : Rep k r) (x : ι → R.H) :
    ‖hh Γ R x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  have e : hh Γ R x x = ∑ i, ⟪x i, ∑ j, Γ i j • x j⟫_ℂ := by
    simp only [hh, inner_sum, inner_smul_right]
  have h1 := norm_sq_mul h x
  have h2 : ‖hh Γ R x x‖ ≤ ∑ i, (‖x i‖ ^ 2 + ‖∑ j, Γ i j • x j‖ ^ 2) / 2 := by
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    nlinarith [sq_nonneg (‖x i‖ - ‖∑ j, Γ i j • x j‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib, h1] at h2
  linarith

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
  {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} {ep : κ → ℝ}

theorem proj_sm (hT : TensH ρ Γ R RI io pr ep) (I : κ) {x : ι → R.H} (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, pr I c (x c) ∈ (RI I).sm :=
  sum_sm (RI I) _ fun c => (hT.raw.pr_sm I c).mem _ (hx c)

theorem adj (hT : TensH ρ Γ R RI io pr ep) (I : κ) (y : (RI I).H) (hy : y ∈ (RI I).sm) (x : ι → R.H)
    (hx : ∀ c, x c ∈ R.sm) :
    hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ := by
  have e : (fun c => ∑ J, io J c (∑ d, pr J d (x d))) = x := funext (hT.raw.sum_io_pr x hx)
  conv_lhs => rw [← e]
  rw [hh_sum_right Γ R (fun J c => io J c (∑ d, pr J d (x d))), Finset.sum_eq_single I]
  · exact hT.iso I y hy _ (proj_sm hT I hx)
  · intro J _ hJ
    exact hT.orth I J hJ.symm y hy _ (proj_sm hT J hx)
  · simp

theorem parseval (hT : TensH ρ Γ R RI io pr ep) (x x' : ι → R.H) (hx : ∀ c, x c ∈ R.sm)
    (hx' : ∀ c, x' c ∈ R.sm) :
    hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ := by
  have e : (fun c => ∑ J, io J c (∑ d, pr J d (x d))) = x := funext (hT.raw.sum_io_pr x hx)
  conv_lhs => rw [← e]
  rw [hh_sum_left Γ R (fun J c => io J c (∑ d, pr J d (x d)))]
  exact Finset.sum_congr rfl fun I _ => adj hT I _ (proj_sm hT I hx) x' hx'

end

theorem tens_adj : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ I, ∀ y ∈ (RI I).sm, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ) ∧ (∀ x x' : ι → R.H, (∀ c, x c ∈ R.sm) → (∀ c, x' c ∈ R.sm) → hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ) ∧ (∀ (a : ι → ℂ) (x : ι → R.H) (v : R.H), hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ) ∧ (∀ I, ∀ y ∈ (RI I).sm, ‖y‖ ^ 2 ≤ ∑ c, ‖io I c y‖ ^ 2) ∧ ∀ (a a' : ι → ℂ), ∀ v ∈ R.sm, ∀ v' ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a') a * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R a v c), (RI I).σ g (∑ c, pr I c (tm R a' v' c))⟫_ℂ := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI hR _ hF hT
  refine ⟨fun I y hy x hx => adj hT I y hy x hx, fun x x' hx hx' => parseval hT x x' hx hx',
    fun a x v => hh_tm Γ R a x v, ?_, ?_⟩
  · intro I y hy
    have h1 := norm_hh_le (Γ := Γ) (by rw [hF.1, hF.2.1]) R (fun c => io I c y)
    rw [hT.iso I y hy y hy, norm_mul, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖(ep I : ℂ)‖ = 1 := by rcases hT.ep_sq I with h | h <;> simp [h]
    rw [h2] at h1
    simpa using h1
  · intro a a' v hv v' hv' g hg
    have ht : ∀ (b : ι → ℂ) (w : R.H), w ∈ R.sm → ∀ c, tm R b w c ∈ R.sm := fun b w hw c =>
      R.smSub.smul_mem (b c) hw
    have hact : ∀ c, act ρ R g (tm R a' v') c ∈ R.sm := fun c =>
      sum_sm R _ fun j => R.smSub.smul_mem _
        (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 _ (ht a' v' hv' j) g hg)
    have hp := parseval hT _ _ hact (ht a v hv)
    simp only [hT.raw.pr_eq _ g hg _ (ht a' v' hv')] at hp
    rw [← hp]
    simp only [hh, act, tm, Formalism.QuantumDeterminants.herm, inner_sum, inner_smul_left, inner_smul_right, map_smul, smul_smul,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.star_apply, RCLike.star_def]
    ring

end GlobalTheory.TensAdj
end Gp91
end
