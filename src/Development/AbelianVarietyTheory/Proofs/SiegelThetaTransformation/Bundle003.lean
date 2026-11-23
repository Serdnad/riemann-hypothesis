module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Mathlib.Order.Filter.Ultrafilter.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SymplecticPeriods

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_symplectic_rows (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ j,
      F (fun i => σ j (Sum.inr i), fun i => σ j (Sum.inl i)) =
        (fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i),
          fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i)) := by
  classical

  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 : ∀ v : (ι → ℚ) × (ι → ℚ), u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 = 0 := fun v => by
      rw [← hF, hu]; simp
    ext i
    · simpa using h0 (0, Pi.single i 1)
    · simpa using h0 (Pi.single i 1, 0)
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.mp hinj

  choose r hr using fun j : ι ⊕ ι => hsurj
    ((fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i)), fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i))
  let σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ := Matrix.of fun j => Sum.elim (fun i => (r j).2 i) (fun i => (r j).1 i)
  have hrow : ∀ j, ((fun i => σ j (Sum.inr i)), (fun i => σ j (Sum.inl i))) = r j := fun j => rfl
  refine ⟨σ, ?_, fun j => by rw [hrow]; exact hr j⟩
  rw [SymplecticGroup.mem_iff]
  ext a b

  have e1 : (σ * Matrix.J ι ℚ * σᵀ) a b = (r a).1 ⬝ᵥ (r b).2 - (r a).2 ⬝ᵥ (r b).1 := by
    simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, σ, dotProduct, Matrix.one_apply,
      Finset.sum_neg_distrib, sub_eq_add_neg, add_comm, Function.swap]
  rw [e1, ← hF, hr, hr]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.J, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem exists_symplectic_action (ι : Type) [Fintype ι] [DecidableEq ι]
    (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm →
      (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) →
      τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  obtain ⟨σ, hσ, hrows⟩ := exists_symplectic_rows F hF
  refine ⟨σ, hσ, fun τ hτ τ' M hτ' hM => ?_⟩
  have hτs : τ.IsSymm := hτ.1
  set X := spDen σ τ with hX
  set Y := qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ with hY

  have colX : ∀ k, (fun l => Xᵀ l k) =
      qv (fun i => σ (Sum.inr k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inr k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hX, spDen, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]
  have columnBlock : ∀ k, (fun l => Yᵀ l k) =
      qv (fun i => σ (Sum.inl k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inl k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hY, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]

  have hA : M * Xᵀ = 1 := by
    ext i k
    have h := hM (fun i => σ (Sum.inr k) (Sum.inr i), fun i => σ (Sum.inr k) (Sum.inl i))
    rw [hrows (Sum.inr k), ← colX k] at h
    rw [show (M * Xᵀ) i k = (M *ᵥ fun l => Xᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.one_apply, Matrix.mulVec, dotProduct]
    split_ifs <;> simp
  have hB : τ' = M * Yᵀ := by
    ext i k
    have h := hM (fun i => σ (Sum.inl k) (Sum.inr i), fun i => σ (Sum.inl k) (Sum.inl i))
    rw [hrows (Sum.inl k), ← columnBlock k] at h
    rw [show (M * Yᵀ) i k = (M *ᵥ fun l => Yᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hMeq : M = (X⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv hA]
  refine ⟨?_, hMeq⟩
  calc τ' = τ'ᵀ := hτ'.eq.symm
    _ = (M * Yᵀ)ᵀ := by rw [← hB]
    _ = Y * Mᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = spAct σ τ := by rw [hMeq, Matrix.transpose_transpose]; rfl

end GlobalTheory.SymplecticPeriods
end

section

open Complex
open scoped ComplexConjugate

namespace GlobalTheory.Ker.CreOp

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable def holD (v : W) (Φ : W → ℂ) (z : W) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))

theorem contDiff_fderiv_apply {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => fderiv ℝ Φ z v := (contDiff_infty_iff_fderiv.1 h).2.clm_apply contDiff_const

theorem contDiff_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) (holD v Φ) := by
  show ContDiff ℝ _ fun z => (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))
  exact contDiff_const.mul
    ((contDiff_fderiv_apply h v).sub (contDiff_const.mul (contDiff_fderiv_apply h (I • v))))

theorem holD_add {Φ Ψ : W → ℂ} (h : Differentiable ℝ Φ) (h' : Differentiable ℝ Ψ) (v : W) :
    holD v (fun z => Φ z + Ψ z) = fun z => holD v Φ z + holD v Ψ z := by
  funext z
  have hs : HasFDerivAt (fun y => Φ y + Ψ y) (fderiv ℝ Φ z + fderiv ℝ Ψ z) z :=
    (h z).hasFDerivAt.add (h' z).hasFDerivAt
  simp only [holD, hs.fderiv, ContinuousLinearMap.add_apply]
  ring

theorem exists_clm_of_antilinear [FiniteDimensional ℂ W] {lam : W → ℂ}
    (h1 : ∀ a b, lam (a + b) = lam a + lam b) (h2 : ∀ (t : ℂ) a, lam (t • a) = conj t * lam a) :
    ∃ T : W →L[ℝ] ℂ, lam = T := by
  have hr : ∀ (r : ℝ) (a : W), lam (r • a) = r • lam a := by
    intro r a
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r a, h2]
    simp [Complex.real_smul]
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  exact ⟨LinearMap.toContinuousLinearMap
    ({ toFun := lam, map_add' := h1, map_smul' := fun r a => by rw [RingHom.id_apply]; exact hr r a }
      : W →ₗ[ℝ] ℂ), rfl⟩

theorem holD_mul (T : W →L[ℝ] ℂ) (h2 : ∀ a, T (I • a) = -I * T a) {Φ : W → ℂ}
    (h : Differentiable ℝ Φ) (v : W) :
    holD v (fun z => T z * Φ z) = fun z => T z * holD v Φ z := by
  funext z
  have hT : HasFDerivAt (fun y => T y * Φ y) (T z • fderiv ℝ Φ z + Φ z • T) z :=
    T.hasFDerivAt.mul (h z).hasFDerivAt
  simp only [holD, hT.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, h2]
  linear_combination (1 / 2 : ℂ) * Φ z * T v * I_sq

theorem holD_of_differentiableAt {Φ : W → ℂ} {z : W} (h : DifferentiableAt ℂ Φ z) (v : W) :
    holD v Φ z = fderiv ℂ Φ z v := by
  have e : fderiv ℝ Φ z = (fderiv ℂ Φ z).restrictScalars ℝ := h.fderiv_restrictScalars ℝ
  simp only [holD, e, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul,
    smul_eq_mul]
  linear_combination (-(1 / 2) : ℂ) * fderiv ℂ Φ z v * I_sq

variable {σ : Type} (u : σ → W)

theorem contDiff_foldr_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (M : List σ) :
    ContDiff ℝ (⊤ : ℕ∞) (M.foldr (fun l => holD (u l)) Φ) := by
  induction M with
  | nil => exact h
  | cons l M ih => exact contDiff_holD ih (u l)

theorem foldr_holD_eq_iteratedFDeriv [FiniteDimensional ℂ W] {θ : W → ℂ}
    (hθ : Differentiable ℂ θ) (M : List σ) :
    M.foldr (fun l => holD (u l)) θ =
      fun z => iteratedFDeriv ℂ M.length θ z fun k => u (M.get k) := by
  have hθ' : ContDiff ℂ ⊤ θ := GlobalTheory.SCV.contDiff_of_differentiable hθ ⊤
  induction M with
  | nil => funext z; simp
  | cons l M ih =>
    have hA : Differentiable ℂ (iteratedFDeriv ℂ M.length θ) :=
      hθ'.differentiable_iteratedFDeriv (WithTop.coe_lt_top _)
    funext z
    simp only [List.foldr_cons]
    rw [ih, holD_of_differentiableAt ((hA z).continuousMultilinear_apply_const _),
      fderiv_continuousMultilinear_apply_const_apply (hA z)]
    rfl

private theorem contDiff_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, ContDiff ℝ (⊤ : ℕ∞) p.2) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => (R.map fun p => p.1 z * p.2 z).sum := by
  induction R with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact contDiff_const
  | cons p R ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (p.1.contDiff.mul (hR p (by simp))).add (ih fun q hq => hR q (by simp [hq]))

private theorem holD_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) (v : W) :
    holD v (fun z => (R.map fun p => p.1 z * p.2 z).sum) =
      fun z => (R.map fun p => p.1 z * holD v p.2 z).sum := by
  induction R with
  | nil => funext z; simp [holD]
  | cons p R ih =>
    have hp := hR p (by simp)
    have hR' : ∀ q ∈ R, (∀ a, q.1 (I • a) = -I * q.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) q.2 :=
      fun q hq => hR q (by simp [hq])
    have hS := contDiff_list_sum_mul R fun q hq => (hR' q hq).2
    have hd : Differentiable ℝ p.2 := (contDiff_infty_iff_fderiv.1 hp.2).1
    simp only [List.map_cons, List.sum_cons]
    rw [holD_add (show Differentiable ℝ fun z => p.1 z * p.2 z from p.1.differentiable.mul hd)
      (contDiff_infty_iff_fderiv.1 hS).1,
      holD_mul p.1 hp.1 hd, ih hR']

theorem foldr_creation_zero : ∀ (σ W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (u : σ → W) (lam : σ → W → ℂ) (θ : W → ℂ),
    (∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a) → Differentiable ℂ θ →
    ∀ Dl : σ → (W → ℂ) → W → ℂ,
      (∀ l Φ z, Dl l Φ z = lam l z * Φ z +
        (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))) →
      ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) ∧
        L.foldr Dl θ 0 = iteratedFDeriv ℂ L.length θ 0 fun k => u (L.get k) := by
  intro σ W _ _ _ u lam θ hlam hθ Dl hDl L
  choose T hT using fun l => exists_clm_of_antilinear (hlam l).1 (hlam l).2
  have hTI : ∀ l a, T l (I • a) = -I * T l a := by
    intro l a
    rw [← hT l, (hlam l).2, Complex.conj_I]
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ :=
    (GlobalTheory.SCV.contDiff_of_differentiable hθ _).restrict_scalars ℝ
  have step : ∀ l Φ, Dl l Φ = fun z => T l z * Φ z + holD (u l) Φ z := by
    intro l Φ
    funext z
    rw [hDl, ← hT l]
    rfl
  have hsm : ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) := by
    intro L
    induction L with
    | nil => exact hθs
    | cons l L ih =>
      simp only [List.foldr_cons]
      rw [step]
      exact ((T l).contDiff.mul ih).add (contDiff_holD ih (u l))
  have key : ∀ L : List σ, ∃ R : List ((W →L[ℝ] ℂ) × (W → ℂ)),
      (∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) ∧
      L.foldr Dl θ = fun z =>
        L.foldr (fun l => holD (u l)) θ z + (R.map fun p => p.1 z * p.2 z).sum := by
    intro L
    induction L with
    | nil => exact ⟨[], by simp, by funext z; simp⟩
    | cons l L ih =>
      obtain ⟨R, hR, hE⟩ := ih
      refine ⟨(T l, L.foldr Dl θ) :: R.map (fun p => (p.1, holD (u l) p.2)), ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩
        · exact ⟨hTI l, hsm L⟩
        · exact ⟨(hR q hq).1, contDiff_holD (hR q hq).2 (u l)⟩
      · have hD := contDiff_foldr_holD u hθs L
        have hS := contDiff_list_sum_mul R fun p hp => (hR p hp).2
        have e : holD (u l) (L.foldr Dl θ) = fun z =>
            holD (u l) (L.foldr (fun l => holD (u l)) θ) z +
              (R.map fun p => p.1 z * holD (u l) p.2 z).sum := by
          rw [hE, holD_add (contDiff_infty_iff_fderiv.1 hD).1 (contDiff_infty_iff_fderiv.1 hS).1,
            holD_list_sum_mul R hR (u l)]
        funext z
        simp only [List.foldr_cons, step, e, List.map_cons, List.map_map, List.sum_cons,
          Function.comp_def]
        ring
  refine ⟨hsm L, ?_⟩
  obtain ⟨R, -, hE⟩ := key L
  have h0 : (R.map fun p => p.1 0 * p.2 0).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      simp
  rw [hE]
  simp only [h0, add_zero]
  rw [foldr_holD_eq_iteratedFDeriv u hθ L]

end GlobalTheory.Ker.CreOp
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory

namespace GlobalTheory.IsoTower

theorem finite_quot_nsmul (M : Type) [AddCommGroup M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    Finite (M ⧸ (nsmulAddMonoidHom n : M →+ M).range) := by
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨y, rfl⟩

theorem exists_eventually_congr {L M : Type} [AddCommGroup L] [AddCommGroup M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (U : Ultrafilter ℕ) (g : ℕ → L →+ M) {n : ℕ} (hn : 0 < n)
    (P : ℕ → Prop) (hP : ∀ᶠ j in U, P j) :
    ∃ i, P i ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e := by
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 (inferInstance : Module.Finite ℤ L))
  have := hSf.to_subtype
  have := finite_quot_nsmul M hn
  let φ : ℕ → S → M ⧸ (nsmulAddMonoidHom n : M →+ M).range := fun j s => QuotientAddGroup.mk (g j s)
  obtain ⟨v, hv⟩ := Ultrafilter.eq_pure_of_finite (U.map φ)
  have hv' : ∀ᶠ j in U, φ j = v := by
    have : {v} ∈ U.map φ := by
      rw [hv]
      exact rfl
    exact this
  obtain ⟨i, hi, hPi⟩ := (hv'.and hP).exists
  refine ⟨i, hPi, hv'.mono fun j hj a => ?_⟩
  have h := AddMonoidHom.eq_of_eqOn_dense hS
    (f := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g i))
    (g := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g j))
    (fun s hs => congrFun (hi.trans hj.symm) ⟨s, hs⟩)
  obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 (DFunLike.congr_fun h a)
  refine ⟨e, ?_⟩
  have he' : n • e = -g i a + g j a := he
  rw [he']
  abel

end GlobalTheory.IsoTower
end
