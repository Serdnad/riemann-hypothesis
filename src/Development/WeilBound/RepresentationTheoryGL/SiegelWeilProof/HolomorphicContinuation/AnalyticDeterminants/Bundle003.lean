module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

theorem fderiv_line {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (G : F → ℂ) (y v : F)
    (hG : DifferentiableAt ℂ G y) : HasDerivAt (fun s : ℂ => G (y + s • v)) (fderiv ℂ G y v) 0 := by
  have h1 : HasDerivAt (fun s : ℂ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).smul_const v).const_add y
  have h2 : HasFDerivAt G (fderiv ℂ G y) ((fun s : ℂ => y + s • v) 0) := by
    simpa using hG.hasFDerivAt
  exact h2.comp_hasDerivAt (0:ℂ) h1

theorem det_phiF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : (1 + phiF X).det = (1 + piF X).det := by
  have h0 : ∀ j : Fin (N+1), (1 + phiF X) 0 j = if j = 0 then 1 else 0 := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp [phiF_zero_row]
    · simp [phiF_zero_row, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero j).symm]
  rw [det_first_row_expansion _ 1 h0, one_mul]
  congr 1
  ext k l
  simp [Matrix.one_apply, phiF_succ_row, piF]

theorem fderiv_determinant_power_corner_int (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 0 1) = (t : ℂ) * H N t (piF X) := by
  set d := (1 + piF X).det with hd
  have hdiff : DifferentiableAt ℂ (H (N + 1) t) (phiF X) :=
    (analyticAt_H (N + 1) t (phiF X) (by rw [det_phiF]; exact hX)).differentiableAt
  have hl := fderiv_line (H (N + 1) t) (phiF X) (Matrix.single 0 0 1) hdiff
  have heq : (fun s : ℂ => H (N + 1) t (phiF X + s • Matrix.single 0 0 1)) =
      fun s => ((1 + s) * d) ^ t := by
    funext s
    simp only [H]
    congr 1
    have h0 : ∀ j : Fin (N + 1),
        ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) + (phiF X + s •
          (Matrix.single 0 0 1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))) 0 j =
        if j = 0 then 1 + s else 0 := by
      intro j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp [phiF_zero_row]
      · simp [phiF_zero_row, Matrix.one_apply, (Fin.succ_ne_zero j).symm, Matrix.single_apply]
    rw [det_first_row_expansion _ (1 + s) h0]
    congr 2
    ext k l
    simp [Matrix.one_apply, phiF_succ_row, piF, Matrix.single_apply, (Fin.succ_ne_zero k).symm]
  rw [heq] at hl
  have hf : HasDerivAt (fun s : ℂ => (1 + s) * d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).const_add 1).mul_const d
  have hz := (hasDerivAt_zpow t ((1 + 0) * d) (Or.inl (by simpa using hX))).comp (0:ℂ) hf
  refine (hl.unique hz).trans ?_
  simp only [H, ← hd, add_zero, one_mul]
  rw [zpow_sub_one₀ hX]
  field_simp

theorem fderiv_determinant_power_column_int (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) (c : Fin N) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = -fderiv ℂ (H N t) (piF X) (colQ X c) := by
  have hdiff : DifferentiableAt ℂ (H (N + 1) t) (phiF X) :=
    (analyticAt_H (N + 1) t (phiF X) (by rw [det_phiF]; exact hX)).differentiableAt
  have hl := fderiv_line (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) hdiff
  have hl' := fderiv_line (H N t) (piF X) (-colQ X c)
    (analyticAt_H N t (piF X) hX).differentiableAt
  have heq : (fun s : ℂ => H (N + 1) t (phiF X + s • Matrix.single 0 c.succ 1)) =
      fun s => H N t (piF X + s • -colQ X c) := by
    funext s
    simp only [H]
    congr 1
    set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
      1 + (phiF X + s • (Matrix.single 0 c.succ 1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) with hA
    rw [← Matrix.det_updateCol_add_smul_self A (i := c.succ) (j := 0) (Fin.succ_ne_zero c) (-s)]
    have h0 : ∀ j : Fin (N + 1),
        (A.updateCol c.succ (fun k => A k c.succ + (-s) • A k 0)) 0 j = if j = 0 then 1 else 0 := by
      intro j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp [hA, Matrix.updateCol_apply, phiF_zero_row, Matrix.single_apply,
          (Fin.succ_ne_zero c).symm]
      · by_cases hj : j = c
        · subst hj
          simp [hA, Matrix.updateCol_apply, phiF_zero_row, Matrix.single_apply, Matrix.one_apply,
            (Fin.succ_ne_zero j).symm]
        · simp [hA, Matrix.updateCol_apply, phiF_zero_row, Matrix.single_apply, Matrix.one_apply,
            (Fin.succ_ne_zero j).symm, hj, Ne.symm hj, Fin.succ_inj]
    rw [det_first_row_expansion _ 1 h0, one_mul]
    congr 1
    ext k l
    by_cases hlc : l = c
    · subst hlc
      simp [hA, Matrix.updateCol_apply, phiF_succ_row, piF, colQ, Matrix.single_apply,
        Matrix.one_apply, (Fin.succ_ne_zero k).symm, sub_eq_add_neg]
      ring
    · simp [hA, Matrix.updateCol_apply, phiF_succ_row, piF, colQ, Matrix.single_apply,
        Matrix.one_apply, (Fin.succ_ne_zero k).symm, hlc, Fin.succ_inj]
  rw [heq] at hl
  refine (hl.unique hl').trans ?_
  simp <;> rfl

end PositivityTheory.Rg.Sw.LVs.CK
end
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem ts_inG_mul {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * JJ n * (g * h) = hᴴ * (gᴴ * JJ n * g) * h := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hg, hh]

theorem ts_herm_conjTranspose (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  rw [conjTranspose_apply]
  apply Complex.ext <;> simp [herm] <;> ring

theorem ts_inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hb]

theorem ts_continuous_herm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
  unfold herm
  fun_prop

theorem ts_continuous_nU : Continuous (nU : Matrix (Fin n) (Fin n) ℂ → M2 n) := by
  unfold nU
  exact Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const


theorem twoSided : TwoSided := by
  intro n H F Γ hF hΓ hcl hperm ψ hψc hψs hvan h a b ha hb
  have : FirstCountableTopology (M2 n) :=
    inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  obtain ⟨γ, hγΓ, hγa⟩ := mem_closure_iff_seq_limit.1 (hcl ha)
  have hmap : Continuous (fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) :=
    (continuous_fst.mul (ts_continuous_nU.comp (ts_continuous_herm.comp continuous_snd))).mul continuous_const
  have hmem : ∀ c x, InG c → InG (c * nU (herm x) * b) := fun c x hc =>
    ts_inG_mul (ts_inG_mul hc (ts_inG_nU (ts_herm_conjTranspose x))) hb
  have hΦc : ∀ c, InG c → Continuous (fun x => F h (c * nU (herm x) * b)) := by
    intro c hc
    have hcx : Continuous (fun x : Fin n → Fin n → ℝ => c * nU (herm x) * b) :=
      (continuous_const.mul (ts_continuous_nU.comp ts_continuous_herm)).mul continuous_const
    exact (hF h).comp_continuous hcx fun x => hmem c x hc
  have hzero : ∀ k, ∫ x, F h (γ k * nU (herm x) * b) * ψ x = 0 := by
    intro k
    obtain ⟨h', hh'⟩ := hperm (γ k) (hγΓ k) h
    have e : ∀ x, F h (γ k * nU (herm x) * b) * ψ x = F h' (nU (herm x) * b) * ψ x := by
      intro x
      rw [Matrix.mul_assoc, hh' _ (ts_inG_mul (ts_inG_nU (ts_herm_conjTranspose x)) hb)]
    simp_rw [e]
    exact hvan h' b hb
  have hS : IsCompact (insert a (Set.range γ)) := hγa.isCompact_insert_range
  have hSG : insert a (Set.range γ) ⊆ {g | InG g} := by
    rintro c (rfl | ⟨k, rfl⟩)
    · exact ha
    · exact hΓ _ (hγΓ k)
  have hC : IsCompact ((fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) ''
      (insert a (Set.range γ) ×ˢ tsupport ψ)) := (hS.prod hψs).image hmap
  have hCG : (fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) ''
      (insert a (Set.range γ) ×ˢ tsupport ψ) ⊆ {g | InG g} := by
    rintro _ ⟨⟨c, x⟩, ⟨hc, -⟩, rfl⟩
    exact hmem c x (hSG hc)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn ((hF h).mono hCG)
  have hbound : ∀ c ∈ insert a (Set.range γ), ∀ x, ‖F h (c * nU (herm x) * b) * ψ x‖ ≤ M * ‖ψ x‖ := by
    intro c hc x
    rw [norm_mul]
    by_cases hx : x ∈ tsupport ψ
    · exact mul_le_mul_of_nonneg_right (hM _ ⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hlim : Tendsto (fun k => ∫ x, F h (γ k * nU (herm x) * b) * ψ x) atTop
      (𝓝 (∫ x, F h (a * nU (herm x) * b) * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M * ‖ψ x‖) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((hΦc _ (hΓ _ (hγΓ k))).mul hψc).aestronglyMeasurable
    · exact (hψc.norm.integrable_of_hasCompactSupport hψs.norm).const_mul M
    · exact Eventually.of_forall fun x => hbound _ (Set.mem_insert_of_mem _ ⟨k, rfl⟩) x
    · refine Eventually.of_forall fun x => ?_
      refine Tendsto.mul_const _ ?_
      have hw : ContinuousWithinAt (F h) {g | InG g} (a * nU (herm x) * b) := hF h _ (hmem a x ha)
      refine hw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => hmem _ x (hΓ _ (hγΓ k))⟩)
      exact ((hγa.mul tendsto_const_nhds).mul tendsto_const_nhds)
  have h0 : Tendsto (fun k => ∫ x, F h (γ k * nU (herm x) * b) * ψ x) atTop (𝓝 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

end PositivityTheory.Rg.Sw.LVs
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def reK (e : M2 n) : M2 n := (1 / 2 : ℂ) • (e - eᴴ)

def imK (e : M2 n) : M2 n := (-Complex.I / 2) • (e + eᴴ)

def dK (F : M2 n → ℂ) (x e : M2 n) : ℂ := fderiv ℝ F x (reK e * x) + Complex.I * fderiv ℝ F x (imK e * x)

def KSet (n : ℕ) : Set (M2 n) := {g | InK g}

def LeftDeriv : Prop :=
  ∀ (n : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι → (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∀ (F : M2 n → ℂ) (U : Set (M2 n)), IsOpen U → KSet n ⊆ U → ContDiffOn ℝ 1 F U →
    ∀ e : M2 n, e * JJ n = JJ n * e →
      Integrable (fun k => dK F (ι k) e) μ ∧ ∫ k, dK F (ι k) e ∂μ = 0

def LawDeriv : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → {g | InG g} ⊆ Ω → DifferentiableOn ℂ Θ Ω →
    (∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x → Θ (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * Θ x) →
    ∀ x, InG x → ∀ Y : M2 n, Y.toBlocks₂₁ = 0 →
      fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x

def eA (a b : Fin n) : M2 n := fromBlocks (Matrix.single a b 1) 0 0 (Matrix.single a b 1)

def eB (a b : Fin n) : M2 n := fromBlocks 0 (Matrix.single a b 1) (-Matrix.single a b 1) 0

def cA (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := (x * Z * xᴴ).toBlocks₂₂ a b

def cB (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := -(x * Z * xᴴ).toBlocks₂₁ a b

def PtId : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (x Z : M2 n), InK x → ContDiffAt ℂ 1 Θ x →
    (∀ Y : M2 n, Y.toBlocks₂₁ = 0 → fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x) →
    fderiv ℂ Θ x (x * Z) =
      ∑ a, ∑ b, (dK (fun y => cA Z a b y * Θ y) x (eA a b) + dK (fun y => cB Z a b y * Θ y) x (eB a b))

def CDiff : Prop := ∀ (n : ℕ) (Z : M2 n) (a b : Fin n), ContDiff ℝ ∞ (cA Z a b) ∧ ContDiff ℝ ∞ (cB Z a b)

end PositivityTheory.Rg.Sw.LVs.II
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Cm (n : ℕ) : M2 n := fromBlocks (Complex.I • 1) (-(Complex.I • 1)) 1 1

def mX (P Q R S : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks P Q R S * (Cm n)⁻¹

def wM (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := (u2 x)⁻¹ * u1 x

def ub1 (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := x⁻¹.toBlocks₁₁ + Complex.I • x⁻¹.toBlocks₂₁

def fV (p q : ℤ) (x : M2 n) : ℂ := (u1 x).det ^ (p - n) * (u2 x).det ^ q * (ub1 x).det ^ (-(n : ℤ))

def blkA (j : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < j

def blkB (j : ℕ) : Finset (Fin n) := (blkA j)ᶜ

def minorOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))).det

def embOn (s : Finset (Fin n)) (T : Matrix s s ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if h : a ∈ s ∧ b ∈ s then T ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def detD {ι : Type} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℂ) *
    iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single ((Fintype.equivFin ι).symm i)
      (σ ((Fintype.equivFin ι).symm i)) 1)

def Cayley : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (t : ℤ),
    detD (fun T : Matrix ι ι ℂ => (1 + A * T).det ^ t) =
      (∏ i ∈ Finset.range (Fintype.card ι), ((t : ℂ) + i)) * A.det

def UAct : Prop :=
  ∀ (n : ℕ) (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ),
    u1 (x * mX P Q R S) = u1 x * P + u2 x * R ∧ u2 (x * mX P Q R S) = u1 x * Q + u2 x * S

def DjSec : Prop :=
  ∀ (n j : ℕ) (p q : ℤ) (x : M2 n), j ≤ n → (u1 x).det ≠ 0 → (u2 x).det ≠ 0 →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
    (∏ i ∈ Finset.range j, (-(q : ℂ) + i)) * (∏ i ∈ Finset.range (n - j), (-(p : ℂ) + i)) *
      f0 p q x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹

def DpDual : Prop :=
  ∀ (n j : ℕ) (p q : ℤ) (x : M2 n), j ≤ n → InG x →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1))) =
    (∏ i ∈ Finset.range j, ((p : ℂ) - n + i)) * (∏ i ∈ Finset.range (n - j), ((q : ℂ) - n + i)) *
      fV p q x * minorOn (blkA j) (wM x)⁻¹ * minorOn (blkB j) (wM x)

def GSet (n : ℕ) : Set (M2 n) := {g | InG g}

def HolInt : Prop :=
  ∀ (n : ℕ) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] (Ω : Set (M2 n)) (F : Kg → M2 n → ℂ), IsOpen Ω →
    (∀ N : ℕ, ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N (F y.1) y.2) (Set.univ ×ˢ Ω)) →
    (∀ k, ContDiffOn ℂ ∞ (F k) Ω) →
    ContDiffOn ℂ ∞ (fun x => ∫ k, F k x ∂μ) Ω ∧ ∀ (N : ℕ) (x : M2 n) (v : Fin N → M2 n), x ∈ Ω →
      iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x v = ∫ k, iteratedFDeriv ℂ N (F k) x v ∂μ

def HolZero : Prop :=
  ∀ (n : ℕ) (Ω : Set (M2 n)) (F : M2 n → ℂ), IsOpen Ω → GSet n ⊆ Ω → ContDiffOn ℂ ∞ F Ω →
    (∀ g ∈ GSet n, F g = 0) → ∀ (N : ℕ) (g : M2 n), InG g → iteratedFDeriv ℂ N F g = 0

def SingToDiff : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) (r : ℝ), 0 < r → ContDiffOn ℂ ∞ G (Metric.ball 0 r) →
    (∀ ψ, IsSingTest ψ → ∫ x, G (herm x) * ψ x = 0) → detD G = 0

def TopComp : Prop :=
  ∀ (n j : ℕ) (F : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → GSet n ⊆ Ω → ContDiffOn ℂ ∞ F Ω →
    (∀ x P S, x * mX (1 + P) 0 0 (1 + S) ∈ Ω → x ∈ Ω → (∀ a b, P a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j) →
      (∀ a b, S a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) → F (x * mX (1 + P) 0 0 (1 + S)) = F x) →
    (∀ a b, InG a → InG b → detD (fun H => F (a * nU H * b)) = 0) →
    ∀ g, InG g → detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      F (g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) = 0

def InfInv : Prop :=
  ∀ (n : ℕ) (F1 F2 : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → GSet n ⊆ Ω → ContDiffOn ℂ ∞ F1 Ω →
    ContDiffOn ℂ ∞ F2 Ω →
    (∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x →
      F1 (p * x) * F2 (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * (F1 x * F2 x)) →
    ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
      [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι → (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∀ Z : M2 n, ∫ k, (fderiv ℂ F1 (ι k) (ι k * Z) * F2 (ι k) + F1 (ι k) * fderiv ℂ F2 (ι k) (ι k * Z)) ∂μ = 0

end PositivityTheory.Rg.Sw.LVs
end
end

section

noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolD

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem line2 {H : E → V} {y w : E} {m : E →L[ℂ] E} (hfd : DifferentiableAt ℂ (fderiv ℂ H) y)
    (hz : ∀ t : ℝ, fderiv ℂ H (y + (t : ℂ) • w) (m (y + (t : ℂ) • w)) = 0) :
    fderiv ℂ (fderiv ℂ H) y w (m y) + fderiv ℂ H y (m w) = 0 := by
  have hψ : HasFDerivAt (fun z => fderiv ℂ H z (m z))
      ((fderiv ℂ H y).comp m + (fderiv ℂ (fderiv ℂ H) y).flip (m y)) y :=
    hfd.hasFDerivAt.clm_apply m.hasFDerivAt
  have h := GlobalTheory.SCV.fderiv_apply_eq_zero_of_frequently hψ.differentiableAt (s := w)
    (GlobalTheory.SCV.frequently_nhdsNE_of_eventually_ofReal
      (p := fun t : ℂ => fderiv ℂ H (y + t • w) (m (y + t • w)) = fderiv ℂ H y (m y))
      (Eventually.of_forall fun t => by
        have h0 := hz 0
        simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
        rw [hz t, h0]))
  rw [hψ.fderiv] at h
  simpa [add_comm] using h

theorem scalar_dir {H : E → V} {y : E} (hd : DifferentiableAt ℂ H y)
    (h : ∀ t : ℝ, H (Complex.exp ((t : ℂ) * Complex.I) • y) = 0) : fderiv ℂ H y y = 0 := by
  have hγ := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp).smul_const y
  have hc := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hd.hasFDerivAt.restrictScalars ℝ) hγ (by simp)
  have hc0 := hc.congr_of_eventuallyEq (f₁ := fun _ : ℝ => (0 : V)) (Eventually.of_forall fun t => (h t).symm)
  have := hc0.unique (hasDerivAt_const (0 : ℝ) (0 : V))
  simp only [ContinuousLinearMap.coe_restrictScalars', id, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, map_smul, Complex.ofReal_one] at this
  exact (smul_eq_zero.mp this).resolve_left Complex.I_ne_zero

end PositivityTheory.Rg.Sw.LVs.HolD
end
end
