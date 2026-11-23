module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle293
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Classical

namespace GlobalTheory.DefiniteDecomp

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem pairwise_commute {θ : InfFam D} {V : HSp D} {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ((Finset.univ : Finset D.what₂.Tau) : Set D.what₂.Tau).Pairwise
      (Function.onFun Commute fun τ => atTau θ V τ (g τ)) :=
  fun τ _ τ' _ hne => GlobalTheory.PointAtPlaceComm.atTau_comm D θ h.1 V τ τ' hne _ (h.2 τ) _ (h.2 τ')

def realProd (θ : InfFam D) (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  if h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then
    Finset.univ.noncommProd (fun τ => atTau θ V τ (g τ)) (pairwise_commute h)
  else 1

variable {θ : InfFam D} {V : HSp D}

theorem update_mem {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) (τ : D.what₂.Tau) :
    Function.update g τ₀ g' τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  by_cases h : τ = τ₀
  · subst h; rw [Function.update_self]; exact hg'
  · rw [Function.update_of_ne h]; exact hg τ

theorem realProd_update (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    realProd θ V (Function.update g τ₀ g') = atTau θ V τ₀ g' * realProd θ V (Function.update g τ₀ 1) := by
  classical
  have h1 := update_mem hg τ₀ hg'
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dite_eq_left ⟨hθ, h1⟩, dite_eq_left ⟨hθ, h2⟩, ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀),
    ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀) (fun τ => atTau θ V τ (Function.update g τ₀ 1 τ))]
  simp only [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ, one_mul]
  congr 1
  refine Finset.noncommProd_congr rfl (fun τ hτ => ?_) _
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ), Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem realProd_commute (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    Commute (atTau θ V τ₀ g') (realProd θ V (Function.update g τ₀ 1)) := by
  classical
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dite_eq_left ⟨hθ, h2⟩]
  refine Finset.noncommProd_commute _ _ _ _ fun τ _ => ?_
  by_cases h : τ = τ₀
  · subst h
    rw [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ]
    exact Commute.one_right _
  · exact GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ₀ τ (Ne.symm h) _ hg' _ (h2 τ)

theorem realProd_one (hθ : IsInfFam θ) : realProd θ V (fun _ => 1) = 1 := by
  unfold realProd
  rw [dite_eq_left ⟨hθ, fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _⟩]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun τ _ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ, one_pow]

theorem isAutFunSm_realProd (hθ : IsInfFam θ) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V (rTr V (realProd θ V g) φ) := by
  unfold realProd
  split_ifs with h
  · refine Finset.noncommProd_induction _ _ _ (fun x => ∀ ψ, IsAutFunSm θ V ψ → IsAutFunSm θ V (rTr V x ψ))
      (fun a b ha hb ψ hψ => ?_) (fun ψ hψ => ?_) (fun τ _ ψ hψ => ?_) φ hφ
    · have e : rTr V (a * b) ψ = rTr V a (rTr V b ψ) := funext fun x => by simp only [rTr, mul_assoc]
      rw [e]; exact ha _ (hb _ hψ)
    · have e : rTr V 1 ψ = ψ := funext fun x => by simp only [rTr, mul_one]
      rw [e]; exact hψ
    · exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V ψ hψ τ _ (h.2 τ)
  · have e : rTr V 1 φ = φ := funext fun x => by simp only [rTr, mul_one]
    rw [e]; exact hφ

theorem rep_mul {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (g * h) = (M.rep τ g).comp (M.rep τ h) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have e : M.fr τ * (g * h) * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * h * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  unfold DSModel.rep
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg) _
    (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hh)

theorem rep_one {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem sm_eq_top {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] :
    M.sm τ = ⊤ := by
  rw [GlobalTheory.SmVec.sm_eq]
  refine Submodule.orthogonal_eq_bot_iff.1 ((Submodule.eq_bot_iff _).2 fun y hy => ?_)
  exact GlobalTheory.SmVec.eq_zero_of_inner_smooth (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    fun u hu => (Submodule.mem_orthogonal _ _).1 hy u hu

theorem equiv_one {H G : Type} [AddCommGroup H] [Module ℂ H] [Module.Free ℂ H] [Module.Finite ℂ H] [Mul G]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    {m : ℕ} (k : Fin m → G) (hk : ∀ j, k j ∈ K) (B : Fin m → (H →ₗ[ℂ] H))
    (hB : ∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j)
    (f : G → ℂ) (hf : ∀ g ∈ K, f g = ∑ j, f (k j) * LinearMap.trace ℂ H (ρ g ∘ₗ B j))
    (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K) (e : H →ₗ[ℂ] ℂ) (v : H) {h : G} (hh : h ∈ K) :
    ∑ j, e (B j (ρ h v)) * f (k j) = ∑ j, e (B j v) * f (h * k j) := by
  have e1 : ∀ j, f (h * k j) = ∑ i, f (k i) * LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) := by
    intro j
    rw [hf _ (hmul _ hh _ (hk j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hρ _ hh _ (hk j), LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have e2 : ∀ i, e (B i (ρ h v)) = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) * e (B j v) := by
    intro i
    have := congrArg (fun L : H →ₗ[ℂ] H => e (L v)) (hB i h hh)

    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, smul_eq_mul] at this
    exact this
  simp only [e1, e2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.DefiniteDecomp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

namespace GlobalTheory.RepAdj

theorem rep_adjoint_eq_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  intro D V S M τ _ g hg
  have hfd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ))
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact ((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ |>.mul (M.fr_unit τ)
  have hgi : g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := GlobalTheory.SmVec.inv_mem_UH hG hg
  have hgu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
  refine ⟨hgi, ?_⟩
  have hU := (M.ds τ).2.2.1
  have m1 : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg
  have m2 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hgi
  have hprod : (M.fr τ * g⁻¹ * (M.fr τ)⁻¹) * (M.fr τ * g * (M.fr τ)⁻¹) = 1 := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hfd]
    rw [← Matrix.mul_assoc g⁻¹ g, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hfd]
  have hcomp : ∀ x, M.rep τ g⁻¹ (M.rep τ g x) = x := by
    intro x
    have := hU.1.2 _ m2 _ m1
    rw [hprod, hU.1.1] at this
    have hx := congrArg (fun T : M.H τ →L[ℂ] M.H τ => T x) this
    simpa [DSModel.rep] using hx.symm
  have hiso : ∀ x y, inner ℂ (M.rep τ g⁻¹ x) (M.rep τ g⁻¹ y) = inner ℂ x y := by
    have hn : ∀ v, ‖(M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) v‖ = ‖v‖ := fun v => hU.2.1 _ m2 v
    intro x y
    exact (LinearMap.norm_map_iff_inner_map_map (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ)).1 hn x y
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  have := hiso x (M.rep τ g y)
  rw [hcomp] at this
  simpa using this

end GlobalTheory.RepAdj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspTypeApproxX

theorem norm_sub_sum_sigma_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ j, J k j‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2‖ < δ := by
  have hs : ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2 = ∑ k, ∑ j, J k j := by
    rw [Equiv.sum_comp finSigmaFinEquiv.symm (fun x => J x.1 x.2), Fintype.sum_sigma]
  have hd : I - ∑ k, ∑ j, J k j = (I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hs, hd]
  have h3 : ‖∑ k, (L k - ∑ j, J k j)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ j, J k j‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ j, J k j)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end GlobalTheory.CuspTypeApproxX
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspTypeApproxUp

theorem norm_sub_sum_sigma_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ j, J k j‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2‖ < δ := by
  have hs : ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2 = ∑ k, ∑ j, J k j := by
    rw [Equiv.sum_comp finSigmaFinEquiv.symm (fun x => J x.1 x.2), Fintype.sum_sigma]
  have hd : I - ∑ k, ∑ j, J k j = (I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hs, hd]
  have h3 : ‖∑ k, (L k - ∑ j, J k j)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ j, J k j‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ j, J k j)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end GlobalTheory.CuspTypeApproxUp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem exists_proj_sesq_posDef_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  intro M _ _ b F hF hpos hherm
  classical
  set n := Module.finrank ℂ F
  let v : Module.Basis (Fin n) ℂ F := Module.finBasis ℂ F
  let A : F →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => (b (v i : M)).comp F.subtype)
  let B : M →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x i => star (b x (v i : M))
      map_add' := by intro x y; funext i; simp [map_add (f := _)]
      map_smul' := by intro c x; funext i; simp [mul_comm] }
  have key : ∀ (y : F) (x : M), (∀ i, b (v i : M) (y : M) = star (b x (v i : M))) →
      ∀ f ∈ F, b (y : M) f = b x f := by
    intro y x h f hf
    have hc : (b (y : M)).comp F.subtype = (b x).comp F.subtype := by
      refine v.ext (fun i => ?_)
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [← hherm _ (v i).2 _ y.2, h i, star_star]
    have := LinearMap.congr_fun hc ⟨f, hf⟩
    simpa using this
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ i, b (v i : M) (y : M) = star (b (0 : M) (v i : M)) := by
      intro i
      have := congrFun hy i
      simpa [A] using this
    have hyy := key y 0 h0 y y.2
    by_contra hne
    have hne' : (y : M) ≠ 0 := by simpa using hne
    have := hpos y y.2 hne'
    rw [hyy] at this
    simp at this
  have hdim : Module.finrank ℂ F = Module.finrank ℂ (Fin n → ℂ) := by simp [n]
  let Aeq := LinearMap.linearEquivOfInjective A hinj hdim
  refine ⟨F.subtype.comp (Aeq.symm.toLinearMap.comp B), fun x => (Aeq.symm (B x)).2, ?_⟩
  intro x f hf
  show b ((Aeq.symm (B x) : F) : M) f = b x f
  refine key (Aeq.symm (B x)) x ?_ f hf
  intro i
  have h1 : A (Aeq.symm (B x)) = B x := by
    exact Aeq.apply_symm_apply (B x)
  have := congrFun h1 i
  simpa [A, B] using this

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.JointSpectral

theorem exists_finset_joint_eigen : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F Z hfd hmap hadd hsmul hcomm b hpos hsymm hadj
  let T : ι → Module.End ℂ Z := fun i =>
    { toFun := fun x => ⟨F i x, hmap i x x.2⟩
      map_add' := fun x y => Subtype.ext (hadd i x x.2 y y.2)
      map_smul' := fun a x => Subtype.ext (hsmul i a x x.2) }
  let core : InnerProductSpace.Core ℂ Z :=
    { inner := fun x y => b x y
      conj_inner_symm := fun x y => by
        show star (b (y : E) x) = b x y
        exact hsymm y y.2 x x.2
      re_inner_nonneg := fun x => by
        show 0 ≤ (b (x : E) x).re
        by_cases hx : (x : E) = 0
        · rw [hx]; simp
        · exact (hpos x x.2 hx).le
      add_left := fun x y z => by
        show b ((x : E) + y) z = b x z + b y z
        rw [map_add (f := _), LinearMap.add_apply]
      smul_left := fun x y r => by
        show b (r • (x : E)) y = starRingEnd ℂ r * b x y
        rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      definite := fun x hx => by
        by_contra h0
        have h1 := hpos x x.2 (fun e => h0 (Subtype.ext e))
        have h2 : b (x : E) x = 0 := hx
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup Z := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (cd := core)
  letI : InnerProductSpace ℂ Z := InnerProductSpace.ofCore core.toCore
  have hT : ∀ i, (T i).IsSymmetric := fun i x y => (hadj i x x.2 y y.2).symm
  have hC : Pairwise (Function.onFun Commute T) := fun i j _ =>
    LinearMap.ext fun x => Subtype.ext (hcomm i j x x.2)
  have key := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have htop : IsCompactElement (⊤ : Submodule ℂ Z) :=
    (Submodule.fg_iff_compact _).1 (Module.finite_def.1 hfd)
  obtain ⟨s, hs⟩ := htop.exists_finset_of_le_iSup
    (fun χ : ι → ℂ => ⨅ i, Module.End.eigenspace (T i) (χ i)) key.ge
  have hle : (⊤ : Submodule ℂ Z) ≤
      (⨆ c ∈ s, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}).comap Z.subtype := by
    refine hs.trans (iSup₂_le fun c hc y hy => ?_)
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hy
    refine Submodule.mem_comap.2 ((le_iSup₂ (f := fun c (_ : c ∈ s) =>
      Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}) c hc) (Submodule.subset_span ⟨y.2, fun i => ?_⟩))
    exact congrArg Subtype.val (hy i)
  exact ⟨s, fun x hx => hle (x := ⟨x, hx⟩) Submodule.mem_top⟩

end GlobalTheory.JointSpectral
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnTypeApprox

theorem norm_sub_sum_sum_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ q, J k q‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ k, ∑ q, J k q‖ < δ := by
  have hd : I - ∑ k, ∑ q, J k q = (I - ∑ k, L k) + ∑ k, (L k - ∑ q, J k q) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hd]
  have h3 : ‖∑ k, (L k - ∑ q, J k q)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ q, J k q‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ q, J k q)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ q, J k q)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end GlobalTheory.DnTypeApprox
end
end
