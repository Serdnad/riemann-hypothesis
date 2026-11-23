module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.DualComm

variable {n : ℕ}

theorem sum_single_smul {W : Type*} [AddCommGroup W] [Module ℂ W] (Δ : Fin n → Fin n → W) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Δ x y = c • Δ a b := by
  have hx : ∀ x y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Δ x y =
      if y = b then (if x = a then c • Δ a b else 0) else 0 := by
    intro x y
    by_cases h1 : x = a
    · by_cases h2 : y = b
      · subst h1
        subst h2
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, h1, h2, Ne.symm h2]
    · simp [Matrix.single_apply, h1, Ne.symm h1]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem eq_zero_of_skew {W : Type*} [AddCommGroup W] [Module ℂ W] (Δ : Fin n → Fin n → W)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ x, ∑ y, X x y • Δ x y = 0) (a b : Fin n) : Δ a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one,
      neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
    ext i j
    simp [Matrix.single_apply]
    split_ifs <;> ring)
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single_smul, one_smul] at h1 h2
  rw [sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul, smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · exact h2

theorem dualT_comp_rho (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (ξ : E.V →L[ℂ] ℂ) :
    dualT E T (ξ ∘L E.ρ k) = dualT E T ξ ∘L E.ρ k := by
  ext v
  have h := congrArg (fun f : E.V →L[ℂ] E.V => f v) (hT k)
  change T (E.ρ k v) = E.ρ k (T v) at h
  simp [dualT, h]

theorem dualT_sum (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (ξ : E.V →L[ℂ] ℂ) :
    dualT E T (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • G a b (dualT E T ξ) := by
  have hmem : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    intro t
    have hc : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
    have hs : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
      rw [Matrix.conjTranspose_smul, hX, smul_neg]
      simp
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
      ← Matrix.exp_add_of_commute _ _ hc, add_neg_cancel, NormedSpace.exp_zero]
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp ((t : ℂ) • X), hmem t⟩
  have hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
  have h1 := hG.2 X γ hX hγ ξ
  have h2 := hG.2 X γ hX hγ (dualT E T ξ)
  have h3 : HasDerivAt (fun t : ℝ => dualT E T (ξ ∘L E.ρ (γ t)⁻¹))
      (dualT E T (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    ((dualT E T).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have hfun : (fun t : ℝ => dualT E T (ξ ∘L E.ρ (γ t)⁻¹)) =
      fun t : ℝ => dualT E T ξ ∘L E.ρ (γ t)⁻¹ := by
    funext t
    exact dualT_comp_rho E T hT (γ t)⁻¹ ξ
  rw [hfun] at h3
  exact h3.unique h2

theorem dualT_G : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G →
      ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := by
  intro n E T hT G hG a b ξ
  have h := eq_zero_of_skew (fun a b => dualT E T (G a b ξ) - G a b (dualT E T ξ)) ?_ a b
  · exact sub_eq_zero.mp h
  · intro X hX
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, ← dualT_sum E T hT G hG X hX ξ]

    simp only [map_sum, map_smul]

end GlobalTheory.CompanionTheory.RealCountG.DualComm
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Intertw

variable {n : ℕ}

theorem exp_mem (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem sum_single {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • F x y = c • F a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_neg' (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem family_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ a, ∑ b, X a b • F a b = 0) (a b : Fin n) : F a b = 0 := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_neg', single_neg', neg_add,
      add_comm]
  have m1 := h _ h1
  have m2 := h _ h2
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single, one_smul] at m1 m2
  have m3 : F a b + F b a = 0 := by
    have := congrArg (fun v => (-Complex.I) • v) m2
    simpa [smul_add, smul_smul] using this
  have m4 : (2 : ℂ) • F a b = 0 := by
    rw [two_smul]
    calc F a b + F a b = (F a b - F b a) + (F a b + F b a) := by abel
      _ = 0 := by rw [m1, m3, add_zero]
  exact (smul_eq_zero.1 m4).resolve_left two_ne_zero

theorem intertwines : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf →
    ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G →
    ∀ t ∈ invA σ E, ∀ a b ξ, t (G a b ξ) = Kf a b (t ξ) := by
  intro n V _ _ σ Kf hK E G hG t ht a b ξ
  refine sub_eq_zero.1 (family_eq_zero (fun a b => t (G a b ξ) - Kf a b (t ξ)) (fun X hX => ?_) a b)
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun s => ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem X hX s⟩
  have h1 := hG.2 X γ hX (fun _ => rfl) ξ
  obtain ⟨S, _, hS, _, _, hd⟩ := hK.2 (t ξ)
  have h2 := hd X γ (fun _ => rfl) (t ξ) hS
  let tL : (E.V →L[ℂ] ℂ) →L[ℂ] V := LinearMap.toContinuousLinearMap t
  have h3 : HasDerivAt (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) (tL (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    (tL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
  have h4 : (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) = fun s : ℝ => σ (γ s) (t ξ) := by
    funext s
    exact ht (γ s) ξ
  rw [h4] at h3
  have h5 := h3.unique h2
  have h6 : tL (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • t (G a b ξ) := by

    simp only [map_sum, map_smul]
    rfl
  rw [h6] at h5
  simp only [smul_sub, Finset.sum_sub_distrib, h5, sub_self]

end GlobalTheory.CompanionTheory.RealCountG.Intertw
end
end

section

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.KHerm

variable {n : ℕ}

def skA (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a (1 : ℂ))

def skB (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b Complex.I + Matrix.single b a Complex.I)

theorem skA_skew (a b : Fin n) : (skA a b)ᴴ = -skA a b := by
  ext i j
  simp only [skA, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem skB_skew (a b : Fin n) : (skB a b)ᴴ = -skB a b := by
  ext i j
  simp only [skB, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem Kf_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf a b h).1 g = Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have h1 : (Kf a b h).1 g = (e1 DR a b h).1 g - (f1 DR b a h).1 g := by
    simp [Kf, e2, sub_eq_add_neg]
  rw [h1, orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, liftOneFormsToCompatible_apply b a h hg]
  simp only [Eu, Rd, skA, skB, Pi.smul_apply, Pi.add_apply, ite_true, Bool.false_eq_true, ite_false,
    Matrix.mul_smul, mul_sub, mul_add, map_smul, map_sub, map_add, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem Rd_neg (X : Mat n) (f : Mat n → ℂ) (g : Mat n) : Rd (-X) f g = -Rd X f g := by
  simp [Rd]

theorem Kf_apply_swap (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf b a h).1 g = -Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have hA : skA b a = -skA a b := by
    simp only [skA, ← smul_neg, neg_sub]
  have hB : skB b a = skB a b := by
    simp only [skB, add_comm]
  rw [Kf_apply b a h hg, hA, hB, Rd_neg]

theorem Rd_conj_mul (X : Mat n) {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (fun g => conj (x g) * y g) g = conj (Rd X x g) * y g + conj (x g) * Rd X y g := by
  have dx := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hx hg).hasFDerivAt
  have dy := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hy hg).hasFDerivAt
  have dc : HasFDerivAt (fun g => conj (x g)) (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ x g)) g :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp g dx
  have hm : HasFDerivAt (fun g => conj (x g) * y g) _ g := dc.mul dy
  simp only [Rd]
  rw [hm.fderiv]
  change conj (x g) * fderiv ℝ y g (g * X) + y g * conj (fderiv ℝ x g (g * X)) = _
  ring

theorem conj_mul_smooth {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n)) :
    ContDiffOn ℝ ∞ (fun g => conj (x g) * y g) (GLs n) :=
  (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hx).mul hy

section Int

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

omit [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] in
theorem cont_on_unit {f : Mat n → ℂ} (hf : ContinuousOn f (GLs n)) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => f k.1 :=
  hf.comp_continuous continuous_subtype_val fun k => unit_mem k

theorem integrable_of_cont {f : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end Int

end GlobalTheory.CompanionTheory.ModelS.KHerm


open GlobalTheory.CompanionTheory.ModelS.KHerm in
theorem GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  intro n _ _ κ _ hI a b x y
  have hx := x.2.1
  have hy := y.2.1
  have i1 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (Rd X x.1 k.1) * y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hx).continuousOn)).mul (cont_on_unit hy.continuousOn))
  have i2 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * Rd X y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp (cont_on_unit hx.continuousOn)).mul
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hy).continuousOn))
  have key : ∀ X : Mat n, Xᴴ = -X → (∫ k, conj (Rd X x.1 k.1) * y.1 k.1 ∂κ) + ∫ k, conj (x.1 k.1) * Rd X y.1 k.1 ∂κ = 0 := by
    intro X hX
    rw [← integral_add (i1 X) (i2 X), ← hI _ (conj_mul_smooth hx hy) X hX]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => (Rd_conj_mul X hx hy (unit_mem k)).symm)
  have L : ipK κ (Kf a b x) y = (∫ k, conj (Rd (skA a b) x.1 k.1) * y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (Rd (skB a b) x.1 k.1) * y.1 k.1 ∂κ := by
    rw [← integral_const_mul, ← integral_add (i1 _) ((i1 _).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply a b x (unit_mem k), map_sub, map_mul, Complex.conj_I]
    ring
  have R : ipK κ x (Kf b a y) = -((∫ k, conj (x.1 k.1) * Rd (skA a b) y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (x.1 k.1) * Rd (skB a b) y.1 k.1 ∂κ) := by
    rw [← integral_const_mul, ← integral_add (i2 _) ((i2 _).const_mul _), ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply_swap a b y (unit_mem k)]
    ring
  rw [L, R]
  linear_combination key _ (skA_skew a b) + Complex.I * key _ (skB_skew a b)
end
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.L2InnerProduct

theorem isCompact_unitary_set (n : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) := by
  have hK : IsCompact (Set.pi Set.univ
      (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) :
        Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hC : IsClosed ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :=
    isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ)
  refine hK.of_isClosed_subset hC ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact entry_norm_bound_of_unitary hx i j

theorem compactSpace_unitary (n : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitary_set n)

theorem continuous_restrict {n : ℕ} (x : SmF n) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => x.1 k.1 :=
  x.2.1.continuousOn.comp_continuous continuous_subtype_val unit_mem

section

variable {n : ℕ} [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

theorem integrable_integrand (x y : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * y.1 k.1) κ := by
  haveI := compactSpace_unitary n
  exact ((Complex.continuous_conj.comp (continuous_restrict x)).mul
    (continuous_restrict y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_normSq (x : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2) κ := by
  haveI := compactSpace_unitary n
  exact ((continuous_restrict x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem ipK_self (x : SmF n) :
    ipK κ x x = ((∫ k, ‖x.1 k.1‖ ^ 2 ∂κ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  delta ipK
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [Complex.conj_mul']

theorem ipK_conj (x y : SmF n) : conj (ipK κ y x) = ipK κ x y := by
  delta ipK
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_comm]

theorem ipK_add_left (x y z : SmF n) : ipK κ (x + y) z = ipK κ x z + ipK κ y z := by
  delta ipK
  rw [← integral_add (integrable_integrand κ x z) (integrable_integrand κ y z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [add_mul]

theorem ipK_smul_left (c : ℂ) (x y : SmF n) : ipK κ (c • x) y = conj c * ipK κ x y := by
  delta ipK
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_assoc]

theorem eq_zero_of_ipK_self [κ.IsOpenPosMeasure] (x : SmF n) (h : ipK κ x x = 0)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : x.1 k.1 = 0 := by
  rw [ipK_self, Complex.ofReal_eq_zero] at h
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) (integrable_normSq κ x)).1 h
  have hc : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2 :=
    (continuous_restrict x).norm.pow 2
  have := (hc.ae_eq_iff_eq κ continuous_zero).1 hae
  simpa using congrFun this k

end

theorem ipK_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 := by
  intro n _ _ κ _ _
  refine ⟨ipK_conj κ, fun x => ?_, ipK_add_left κ, ipK_smul_left κ, eq_zero_of_ipK_self κ⟩
  rw [ipK_self, Complex.ofReal_re]
  exact integral_nonneg fun k => by positivity

end GlobalTheory.CompanionTheory.ModelS.L2InnerProduct
end
end

section


theorem _root_.GlobalTheory.T.mixed_cycle_rational_exists : GlobalTheory.CompanionTheory.MixZ.ExistsRat := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat | exact GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat | (intros; apply GlobalTheory.CompanionTheory.MixZ.ExRat.existsRat <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

theorem _root_.GlobalTheory.T.levi_embedding_height_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | exact GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.constant_term_levi_parabolic_formula : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ.1 (ratGL E (r + s) γ * g) = φ.1 g) → IsOpen {k | finRep E (r + s) k φ = φ} → ∀ [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)] (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ → ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)), ∫ x in 𝓕, φ.1 (unip x * (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul | exact GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul | (intros; apply GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul <;> assumption)
end
