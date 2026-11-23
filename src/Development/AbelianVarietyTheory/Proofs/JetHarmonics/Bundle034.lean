module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle031
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle015
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle032
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle009
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
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem ev_algebra : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ : Type) [Fintype σ] (x : σ → K), (∀ i, ‖x i‖ < 1) → (∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧ ev (S * T) x = ev S x * ev T x) ∧ (∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a) ∧ (∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i) ∧ (∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1)) ∧ (∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x)) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S → ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x)) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x)) := by
  intro K _ _ _ σ _ x hx
  have Cinj : ∀ a b : K, (MvPowerSeries.C a : MvPowerSeries Unit K) = MvPowerSeries.C b → a = b := by
    intro a b h
    simpa using congrArg MvPowerSeries.constantCoeff h
  have E : ∀ (ρ : Type) [Fintype ρ] (S : MvPowerSeries ρ K) (y : ρ → K),
      csub (fun i => (MvPowerSeries.C (y i) : MvPowerSeries Unit K)) S = MvPowerSeries.C (ev S y) := by
    intro ρ _ S y
    exact (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.1 ρ Unit S y
  obtain ⟨c, hc⟩ : ∃ c : σ → MvPowerSeries Unit K, c = fun i => MvPowerSeries.C (x i) := ⟨_, rfl⟩
  have E' : ∀ S : MvPowerSeries σ K, csub c S = MvPowerSeries.C (ev S x) := by
    intro S
    subst hc
    exact E σ S x
  have B := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ
  have hcs : ∀ i, Small (c i) := by
    intro i
    subst hc
    exact ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit).2.2.2.1 (x i)).2.2 (hx i)
  have R := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ Unit c hcs

  have p1 : ∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x) := by
    intro S hS
    have h := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c S hcs hS).1 0
    rw [E' S] at h
    have hm : ∀ ν : σ →₀ ℕ, MvPowerSeries.coeff 0 (∏ i, c i ^ ν i) = ∏ i, x i ^ ν i := by
      intro ν
      subst hc
      simp [map_prod, map_pow]
    simp only [hm] at h
    unfold HS
    simpa using h
  have p2 : ∀ S T : MvPowerSeries σ K, Bdd S → Bdd T →
      ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧
        ev (S * T) x = ev S x * ev T x := by
    intro S T hS hT
    obtain ⟨h1, h2, h3⟩ := R.1 S T hS hT
    simp only [E'] at h1 h2 h3
    exact ⟨by simpa using congrArg MvPowerSeries.constantCoeff h1,
      by simpa using congrArg MvPowerSeries.constantCoeff h2,
      by simpa using congrArg MvPowerSeries.constantCoeff h3⟩
  have p3 : ∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a := by
    intro a
    have h := R.2.1 a
    rw [E'] at h
    exact Cinj _ _ h
  have p4 : ∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i := by
    intro i
    have h := R.2.2.1 i
    rw [E'] at h
    exact Cinj _ _ (h.trans (by rw [hc]))
  have p5 : ∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1) := by
    intro S hS
    have hSB : Bdd S := (B.2.2.1 S 0).2.2 hS
    have hI := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c S hcs hSB).2.2.1 hS
    rw [E'] at hI
    refine ⟨by simpa using hI 0, fun hSm => ?_⟩

    set c0 := MvPowerSeries.constantCoeff S with hc0d
    have hc0 : ‖c0‖ ≤ 1 := by simpa [hc0d] using hS 0
    have hCI : Intg (MvPowerSeries.C c0 : MvPowerSeries σ K) := (B.2.2.2.1 c0).2.1 hc0
    have hCB : Bdd (MvPowerSeries.C c0 : MvPowerSeries σ K) := (B.2.2.2.1 c0).1
    have hT : Intg (S - MvPowerSeries.C c0) := (B.1 S _ hS hCI).2.1
    have hT0 : MvPowerSeries.constantCoeff (S - MvPowerSeries.C c0) = 0 := by simp [hc0d]
    have hTB : Bdd (S - MvPowerSeries.C c0) := (B.2.2.1 _ 0).2.2 hT
    have hsm := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c _ hcs hTB).2.2.2 hT hT0
    rw [E'] at hsm
    have hlt : ‖ev (S - MvPowerSeries.C c0) x‖ < 1 := by simpa using hsm.2
    have hadd : ev S x = ev (S - MvPowerSeries.C c0) x + c0 := by
      have h := (p2 (S - MvPowerSeries.C c0) _ hTB hCB).1
      rw [sub_add_cancel, p3] at h
      exact h
    have hlt0 : ‖c0‖ < 1 := hSm.2
    calc ‖ev S x‖ = ‖ev (S - MvPowerSeries.C c0) x + c0‖ := by rw [← hadd]
      _ ≤ max ‖ev (S - MvPowerSeries.C c0) x‖ ‖c0‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt hlt hlt0
  have p6 : ∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K),
      (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x) := by
    intro ρ _ s S hs hS
    have h := (GlobalTheory.T.mvPowerSeriesConvergentSubst_assoc K ρ σ Unit s c S hs hcs hS).2
    have hf : (fun j => csub c (s j)) = fun j => (MvPowerSeries.C (ev (s j) x) : MvPowerSeries Unit K) :=
      funext fun j => E' (s j)
    rw [hf, E'] at h
    exact Cinj _ _ (h.trans (E ρ S (fun j => ev (s j) x)))
  have small0 : ∀ a : MvPowerSeries σ K, Intg a → MvPowerSeries.constantCoeff a = 0 → Small a := by
    intro a ha ha0
    show Intg a ∧ ‖MvPowerSeries.constantCoeff a‖ < 1
    exact ⟨ha, by rw [ha0]; simp⟩
  have p7 : ∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K),
      (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S →
        ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x) := by
    intro ρ _ a S ha ha0 hS
    rw [← (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.2.2.1 ρ σ a S ha0]
    exact p6 ρ a S (fun j => small0 _ (ha j) (ha0 j)) hS
  have p8 : ∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a →
      MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x) := by
    intro a f ha ha0 hf
    rw [← (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.2.2.2 σ a f ha0, (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).1 σ a f,
      (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.1 f (ev a x)]
    exact p6 Unit (fun _ => a) f (fun _ => small0 a ha ha0) hf
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩

end GlobalTheory.ConvSer
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem wtdiag_pyth {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ι : Type} (T : Finset ι) (x : ι → M)
    (h : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ⟪x i, x j⟫_ℂ = 0) (c : ι → ℂ) :
    ‖∑ i ∈ T, c i • x i‖ ^ 2 = ∑ i ∈ T, ‖c i‖ ^ 2 * ‖x i‖ ^ 2 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ← ih (fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]
    have h0 : ⟪c a • x a, ∑ i ∈ s, c i • x i⟫_ℂ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [inner_smul_left, inner_smul_right, h a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun e => ha (e ▸ hi))]
      simp
    rw [@norm_add_sq ℂ, h0, norm_smul]
    simp [mul_pow]

theorem wtNear_diag_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → (∀ m : ℝ, (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → m ≤ ∑ a, ω a ^ 2) → m * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2) ∧ (∀ (a : Fin n) (ζ : ℂ) (d : ℝ), 0 ≤ d → (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → d ≤ ‖ζ + (ω a : ℂ)‖) → d ^ 2 * ‖w‖ ^ 2 ≤ ‖ζ • w + E a a w‖ ^ 2) ∧ ∀ (a : Fin n) (D : ℝ), (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → |ω a| ≤ D) → ‖E a a w‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, hx, hsum, horth⟩ := GlobalTheory.T.exists_orthogonal_weight_decomp_of_mem_wtNear M n ε E Λ t w hU hw
  have P := wtdiag_pyth T x horth
  have hw2 : ‖w‖ ^ 2 = ∑ ω ∈ T, ‖x ω‖ ^ 2 := by
    have := P (fun _ => 1)
    simpa [← hsum] using this
  have hE : ∀ a, E a a w = ∑ ω ∈ T, (ω a : ℂ) • x ω := by
    intro a

    rw [hsum, map_sum]
    exact Finset.sum_congr rfl fun ω hω => (hx ω hω).2 a
  have hE2 : ∀ a, ‖E a a w‖ ^ 2 = ∑ ω ∈ T, ω a ^ 2 * ‖x ω‖ ^ 2 := by
    intro a
    rw [hE a, P]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    simp_rw [hE2]
    rw [Finset.sum_comm, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hm ω (hx ω hω).1) (sq_nonneg _)
  · intro a ζ d hd h
    have e : ζ • w + E a a w = ∑ ω ∈ T, (ζ + (ω a : ℂ)) • x ω := by
      rw [hE a]
      conv_lhs => rw [hsum, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ω _ => (add_smul _ _ _).symm
    rw [e, P, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd (h ω (hx ω hω).1) 2) (sq_nonneg _)
  · intro a D h
    rw [hE2, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h ω (hx ω hω).1) 2
end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TensOp

def tensAct {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    (E : Module.End ℂ V) (A : Matrix ι ι ℂ) : Module.End ℂ (PiLp 2 (fun _ : ι => V)) where
  toFun x := WithLp.toLp 2 (fun i => E (x i) + ∑ j, A i j • x j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
    abel
  map_smul' r x := by
    ext i
    simp [Finset.smul_sum, smul_smul, mul_comm]

theorem tensAct_apply {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    (E : Module.End ℂ V) (A : Matrix ι ι ℂ) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct E A x i = E (x i) + ∑ j, A i j • x j := rfl

def sumMap {V N ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] (φ : ι → V →ₗ[ℂ] N) :
    PiLp 2 (fun _ : ι => V) →ₗ[ℂ] N where
  toFun x := ∑ j, φ j (x j)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]

theorem sumMap_apply {V N ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] (φ : ι → V →ₗ[ℂ] N) (x : PiLp 2 (fun _ : ι => V)) :
    sumMap φ x = ∑ j, φ j (x j) := rfl

theorem kunit_tensAct {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι] {n : ℕ}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (A : Fin n → Fin n → Matrix ι ι ℂ)
    (hE : KUnit ε E) (hA : ∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) :
    KUnit ε (fun a b => tensAct (E a b) (A a b)) := by
  intro a b hab x y
  simp only [PiLp.inner_apply, tensAct_apply, inner_add_left, inner_add_right, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.sum_add_distrib, hE a b hab]
  congr 1
  rw [Finset.sum_comm, ← hA a b hab]
  simp [Matrix.conjTranspose_apply]

theorem core (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (N ι : Type) [NormedAddCommGroup N]
    [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N)
    (φ : ι → V →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ) (hE : KUnit ε E) (hF : KUnit ε F)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hA : ∀ a b, ε a = ε b → (A a b).conjTranspose = A b a)
    (hAs : ∀ x : ι → V, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0)
      ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2)
    (hφ : ∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w)
    (hb : ∀ x : V, (∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0) ≤ c ^ 2 * ‖x‖ ^ 2)
    (w : V) (j : ι) : CasKLe ε F (c + s) (φ j w) := by
  set K : Fin n → Fin n → Module.End ℂ (PiLp 2 (fun _ : ι => V)) := fun a b => tensAct (E a b) (A a b) with hK
  have hKu : KUnit ε K := kunit_tensAct ε E A hE hA
  have hint : ∀ a b, ε a = ε b → ∀ x, F a b (sumMap φ x) = sumMap φ (K a b x) := by
    intro a b hab x

    simp only [hK, sumMap_apply, tensAct_apply, map_sum, map_add (f := _), map_smul, hφ a b hab,
    Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
  have hcas : ∀ x, sumMap φ (CasK ε K x) = CasK ε F (sumMap φ x) := by
    intro x

    simp only [CasK, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · simp only [Module.End.mul_apply]
      rw [hint b a hab.symm, hint a b hab]
    · simp
  have hbound : ∀ x, (⟪x, CasK ε K x⟫_ℂ).re ≤ (c + s) ^ 2 * ‖x‖ ^ 2 := by
    intro x
    rw [(GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε K hKu).2 x]
    have h := GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul V (Fin n × Fin n × ι)
      (fun p => if ε p.1 = ε p.2.1 then E p.1 p.2.1 (x p.2.2) else 0)
      (fun p => if ε p.1 = ε p.2.1 then ∑ j, A p.1 p.2.1 p.2.2 j • x j else 0) c s (‖x‖ ^ 2) hc hs
      (by positivity) ?_ ?_
    · refine le_trans (le_of_eq ?_) h
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hab
      · rw [PiLp.norm_sq_eq_of_L2]; rfl
      · simp
    · rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => hb (x i))
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm (s := (univ : Finset ι))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm (s := (univ : Finset ι))]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · rw [PiLp.norm_sq_eq_of_L2]
      refine le_trans (le_of_eq ?_) (hAs (fun i => x i))
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
  refine ⟨LinearMap.range (sumMap φ), inferInstance, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨x, rfl⟩
    exact ⟨K a b x, (hint a b hab x).symm⟩
  · refine ⟨WithLp.toLp 2 (Pi.single j w), ?_⟩
    rw [sumMap_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · simp
  · rintro _ ⟨x, rfl⟩
    exact GlobalTheory.T.re_inner_le_on_image_of_intertwining' _ N (sumMap φ) (CasK ε K) (CasK ε F) _ (GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε K hKu).1
      (GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε F hF).1 hcas hbound x

theorem casKLe_tensor_operator : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N ι : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N) (φ : ι → M →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ), KUnit ε E → KUnit ε F → 0 ≤ c → 0 ≤ s → (∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) → (∀ x : ι → M, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0) ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2) → (∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w) → ∀ w, CasKLe ε E c w → ∀ j, CasKLe ε F (c + s) (φ j w) := by
  intro M _ _ n ε E N ι _ _ _ _ F φ A c s hE hF hc hs hA hAs hφ w hw j
  obtain ⟨S, hfd, hst, hwS, hb⟩ := hw
  let E' : Fin n → Fin n → Module.End ℂ S := fun a b =>
    if h : ε a = ε b then (E a b).restrict (hst a b h) else 0
  have hE' : ∀ a b, ε a = ε b → ∀ x : S, (E' a b x : M) = E a b x := by
    intro a b h x
    simp [E', h]
  have := core S n ε E' N ι F (fun i => (φ i).comp S.subtype) A c s ?_ hF hc hs hA ?_ ?_ ?_ ⟨w, hwS⟩ j
  · exact this
  · intro a b h x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hE' a b h, hE' b a h.symm, hE a b h]
  · intro x
    have h := hAs (fun i => (x i : M))
    simpa only [Submodule.coe_norm, Submodule.coe_sum, Submodule.coe_smul] using h
  · intro a b h i x
    simp [hE' a b h, hφ a b h]
  · intro x
    have h := hb x x.2
    rw [(GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε E hE).2] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · rw [← hE' a b hab]; rfl
    · rfl

end GlobalTheory.TensOp
end
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem casK_mem_of_compact_stable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ε a = ε b → ∀ x ∈ S, E a b x ∈ S) : ∀ x ∈ S, CasK ε E x ∈ S := by
  intro x hx
  unfold CasK
  simp only [LinearMap.sum_apply]
  refine S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
  split_ifs with h
  · exact hS _ _ h _ (hS _ _ h.symm _ hx)
  · simp

theorem quadForm_le_on_sup {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (B : M →ₗ[ℂ] M)
    (hB : B.IsSymmetric) (C : ℝ) (S₁ S₂ : Submodule ℂ M) [FiniteDimensional ℂ S₁] [FiniteDimensional ℂ S₂]
    (h₁ : ∀ x ∈ S₁, B x ∈ S₁) (h₂ : ∀ x ∈ S₂, B x ∈ S₂)
    (b₁ : ∀ x ∈ S₁, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) (b₂ : ∀ x ∈ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) :
    ∀ x ∈ S₁ ⊔ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2 := by
  let e := WithLp.linearEquiv 2 ℂ (S₁ × S₂)
  let Φ : WithLp 2 (S₁ × S₂) →ₗ[ℂ] M := (S₁.subtype.coprod S₂.subtype) ∘ₗ e.toLinearMap
  let A : WithLp 2 (S₁ × S₂) →ₗ[ℂ] WithLp 2 (S₁ × S₂) :=
    e.symm.toLinearMap ∘ₗ ((B.restrict h₁).prodMap (B.restrict h₂)) ∘ₗ e.toLinearMap
  have hA1 : ∀ z, ((A z).fst : M) = B z.fst := fun z => rfl
  have hA2 : ∀ z, ((A z).snd : M) = B z.snd := fun z => rfl
  have hΦ : ∀ z, Φ z = (z.fst : M) + (z.snd : M) := fun z => rfl
  have key := GlobalTheory.T.re_inner_le_on_image_of_intertwining' (WithLp 2 (S₁ × S₂)) M Φ A B C
    (by
      intro z w
      simp only [WithLp.prod_inner_apply, Submodule.coe_inner]
      change ⟪((A z).fst : M), (w.fst : M)⟫_ℂ + ⟪((A z).snd : M), (w.snd : M)⟫_ℂ =
        ⟪(z.fst : M), ((A w).fst : M)⟫_ℂ + ⟪(z.snd : M), ((A w).snd : M)⟫_ℂ
      rw [hA1, hA2, hA1, hA2, hB, hB])
    hB
    (by
      intro z
      rw [hΦ, hΦ, hA1, hA2, map_add (f := _)])
    (by
      intro z
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.prod_inner_apply, Submodule.coe_inner]
      change (⟪(z.fst : M), ((A z).fst : M)⟫_ℂ + ⟪(z.snd : M), ((A z).snd : M)⟫_ℂ).re ≤
        C * (‖(z.fst : M)‖ ^ 2 + ‖(z.snd : M)‖ ^ 2)
      rw [hA1, hA2, Complex.add_re, mul_add]
      exact add_le_add (b₁ _ z.fst.2) (b₂ _ z.snd.2))
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  exact key (WithLp.toLp 2 (⟨y, hy⟩, ⟨z, hz⟩))

theorem casKLe_subspace_mono : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → (∀ c, CasKLe ε E c 0) ∧ (∀ c x y, CasKLe ε E c x → CasKLe ε E c y → CasKLe ε E c (x + y)) ∧ (∀ c (a : ℂ) x, CasKLe ε E c x → CasKLe ε E c (a • x)) ∧ ∀ c c' x, 0 ≤ c → c ≤ c' → CasKLe ε E c x → CasKLe ε E c' x := by
  intro M _ _ n ε E hU
  refine ⟨fun c => ⟨⊥, inferInstance, ?_, Submodule.zero_mem _, ?_⟩, ?_, ?_, ?_⟩
  · intro a b _ x hx
    rw [Submodule.mem_bot] at hx
    simp [hx]
  · intro x hx
    rw [Submodule.mem_bot] at hx
    simp [hx]
  · rintro c x y ⟨S₁, f₁, s₁, hx, b₁⟩ ⟨S₂, f₂, s₂, hy, b₂⟩
    refine ⟨S₁ ⊔ S₂, inferInstance, ?_, Submodule.add_mem_sup hx hy, ?_⟩
    · intro a b hab w hw
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (s₁ a b hab u hu) (s₂ a b hab v hv)
    · exact quadForm_le_on_sup _ (GlobalTheory.T.casK_isSymmetric_and_inner_re_eq M n ε E hU).1 _ S₁ S₂
        (casK_mem_of_compact_stable ε E S₁ s₁) (casK_mem_of_compact_stable ε E S₂ s₂) b₁ b₂
  · rintro c a x ⟨S, f, s, hx, b⟩
    exact ⟨S, f, s, S.smul_mem a hx, b⟩
  · rintro c c' x hc hcc ⟨S, f, s, hx, b⟩
    refine ⟨S, f, s, hx, fun y hy => (b y hy).trans ?_⟩
    gcongr

end GlobalTheory
end
