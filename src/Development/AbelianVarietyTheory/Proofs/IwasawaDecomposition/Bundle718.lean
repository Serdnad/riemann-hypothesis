module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle693
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle692
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMaps
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle701
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle707
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Rat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle702
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.CoverSuper

theorem mul_evalR_le {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {e : X ≃ₗ[O] X} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hγ : IsCell bar φ γ) (hc : ∀ i, 0 ≤ c i)
    (hB : pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) (f : X ≃ₗ[O] X) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hℓ : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (N : ℝ) * φ.evalZ β ≤ ℓ β) :
    (N : ℝ) * evalR φ B ≤ ∑ i, c i * (ℓ (pull (f.trans e.symm).toLinearMap (γ i)) : ℝ) ∧
      pullR f.toLinearMap B = ∑ i, c i • toReal (pull (f.trans e.symm).toLinearMap (γ i)) := by
  have hB' : ∀ a b, B (e a) (e b) = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hB a b
  have hev : evalR φ B = ∑ i, c i * φ.evalZ (γ i) :=
    hγ.linear.eval_eq_sum (r := e.toLinearMap) e.surjective hc hB'
  refine ⟨?_, LinearMap.ext₂ fun a b => ?_⟩
  · rw [hev, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hℓ _ (pull_mem (f.trans e.symm).toLinearMap (hγ.mem i)) (fun y => hγ.nonneg i _)
    rw [evalZ_pull φ (f.trans e.symm).surjective] at h1
    calc (N : ℝ) * (c i * φ.evalZ (γ i)) = c i * (N * φ.evalZ (γ i)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (hc i)
  · have := hB' (e.symm (f a)) (e.symm (f b))
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearMap.sum_apply, this]

theorem add_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (hB : B ∈ psdCone (bar := bar) (X := X)) (hB' : B' ∈ psdCone (bar := bar) (X := X)) : B + B' ∈ psdCone (bar := bar) (X := X) := by
  obtain ⟨m₁, γ₁, c₁, h1, h2, h3, rfl⟩ := ConeSpan.exists_nonneg_comb_of_mem_psdCone O bar X B hB
  obtain ⟨m₂, γ₂, c₂, k1, k2, k3, rfl⟩ := ConeSpan.exists_nonneg_comb_of_mem_psdCone O bar X B' hB'
  have := ConeSub.sum_smul_toReal_mem_psdCone O bar X (m₁ + m₂) (Fin.append γ₁ γ₂) (Fin.append c₁ c₂)
    (fun i => Fin.addCases (fun j => by simpa using h1 j) (fun j => by simpa using k1 j) i)
    (fun i => Fin.addCases (fun j => by simpa using h2 j) (fun j => by simpa using k2 j) i)
    (fun i => Fin.addCases (fun j => by simpa using h3 j) (fun j => by simpa using k3 j) i)
  simpa [Fin.sum_univ_add] using this

theorem superadd_of_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X],
    (∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) →
    ∀ B ∈ psdCone (bar := bar) (X := X), ∀ B' ∈ psdCone (bar := bar) (X := X), evalR φ B + evalR φ B' ≤ evalR φ (B + B') := by
  intro O _ _ _ _ bar φ X _ _ _ hcov B hB B' hB'
  have hBB := add_mem_psdCone O bar X hB hB'
  obtain ⟨e₁, m₁, γ₁, c₁, hγ₁, hc₁, h₁⟩ := hcov B hB
  obtain ⟨e₂, m₂, γ₂, c₂, hγ₂, hc₂, h₂⟩ := hcov B' hB'
  obtain ⟨e₃, m₃, γ₃, c₃, hγ₃, hc₃, h₃⟩ := hcov (B + B') hBB
  obtain ⟨N, ℓ, hN, hℓ1, hℓ2, -⟩ := hγ₃.strict
  obtain ⟨i1, j1⟩ := mul_evalR_le hγ₁ hc₁ h₁ e₃ hℓ2
  obtain ⟨i2, j2⟩ := mul_evalR_le hγ₂ hc₂ h₂ e₃ hℓ2
  have hev3 : evalR φ (B + B') = ∑ i, c₃ i * φ.evalZ (γ₃ i) :=
    hγ₃.linear.eval_eq_sum (r := e₃.toLinearMap) e₃.surjective hc₃ fun a b => by
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h₃ a b
  have hN3 : (N : ℝ) * evalR φ (B + B') = ∑ i, c₃ i * (ℓ (γ₃ i) : ℝ) := by
    rw [hev3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hℓ1 i]; ring
  have hpull : pullR e₃.toLinearMap (B + B') = pullR e₃.toLinearMap B + pullR e₃.toLinearMap B' :=
    LinearMap.ext₂ fun a b => by simp
  have rel := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
    (β := Sum.elim (Sum.elim (fun i => pull (e₃.trans e₁.symm).toLinearMap (γ₁ i))
      (fun i => pull (e₃.trans e₂.symm).toLinearMap (γ₂ i))) γ₃)
    (c := Sum.elim (Sum.elim c₁ c₂) (-c₃)) (by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul,
        Finset.sum_neg_distrib]
      rw [← j1, ← j2, ← h₃, hpull]
      abel)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at rel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * (evalR φ B + evalR φ B') ≤ N * evalR φ (B + B') := by
    rw [mul_add, hN3]
    linarith
  exact le_of_mul_le_mul_left key hNpos

end GlobalTheory.PolFan.CoverSuper
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix


theorem _root_.GlobalTheory.T.boundedDomainModelMetric_contDiffAt_and_isUnit : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat ι p q → ∀ τ : ι, MContDiffAt 2 (fun w => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) v ∧ IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h v) τ))⁻¹)ᵀ).det := by
  first | exact @GlobalTheory.ModelMetricReg.invT_contDiffAt_and_isUnit | exact GlobalTheory.ModelMetricReg.invT_contDiffAt_and_isUnit | (intros; apply GlobalTheory.ModelMetricReg.invT_contDiffAt_and_isUnit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)


theorem _root_.GlobalTheory.T.exists_holomorphic_frame_slice_componentUniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (n : ℕ), n = (U.X k).Ψ.card * (Dw.p * Dw.q) → ∃ (W : Set (V n)) (a : V n) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W ∧ a ∈ W ∧ (∀ w ∈ W, ψ w ∈ (U.X k).dom) ∧ (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) ∧ (∀ h : ψ a ∈ (U.X k).dom, (U.un k ⟨ψ a, h⟩).x = (U.un k x₀).x) ∧ ∀ w ∈ W, ∀ w' ∈ W, ∀ (h : ψ w ∈ (U.X k).dom) (h' : ψ w' ∈ (U.X k).dom), (U.un k ⟨ψ w, h⟩).x = (U.un k ⟨ψ w', h'⟩).x → w = w' := by
  first | exact @GlobalTheory.UnifSlice.exists_slice | exact GlobalTheory.UnifSlice.exists_slice | (intros; apply GlobalTheory.UnifSlice.exists_slice <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.exists_analytic_frame_family_of_holomorphic_periodMaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (φ : La ≃ₗ[𝓞 E] X.Λ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (idx : Fin g → ℕ) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → (La →+ (Fin g → ℂ))) (b₀ : ReciprocityTheory.L2DbarEstimates.V d), IsOpen B → b₀ ∈ B → (∀ b ∈ B, ∀ (a : 𝓞 E) (v : La) (j : Fin g), P b (a • v) j = ty j (a : E) * P b v j) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ ρ ∈ X.Ψ, ∀ m < X.p0, ∃ j, ty j = conjEmb ρ ∧ idx j = m) → (∀ j j', ty j = ty j' → idx j = idx j' → j = j') → (∀ j, ty j ∉ X.Ψ → idx j < X.p0) → (∀ b ∈ B, ∃ x' ∈ X.dom, ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → ∃ s : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, AnalyticAt ℂ s b₀ ∧ ∀ᶠ b in 𝓝 b₀, s b ∈ X.dom ∧ ∀ x' ∈ X.dom, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, P b v = h (fun j => Formalism.L2.PjFree.perFr X x' (φ v : Fin r → E) (ty j) (idx j))) → (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat x' τ) a b' = 0) ∧ (∀ (τ : X.Ψ) (a b' : Fin r), X.p0 ≤ (a : ℕ) → (b' : ℕ) < X.p0 → ((ReciprocityTheory.ChartRestriction.G.FD.mat x' τ)⁻¹ * ReciprocityTheory.ChartRestriction.G.FD.mat (s b) τ) a b' = 0) := by
  first | exact @GlobalTheory.PeriodFamFrame.lift_frame | exact GlobalTheory.PeriodFamFrame.lift_frame | (intros; apply GlobalTheory.PeriodFamFrame.lift_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.intIsometry_fixing_rowSpace_symplectic_shift : ∀ (g r r₀ rk : ℕ) (M T : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ), r = 2 * g → Mᵀ = -M → T * M * Tᵀ = M → c * T = c → (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) → ∃ b : Matrix (Fin g) (Fin g) ℚ, (∀ i j : Fin g, (rk ≤ i.val ∨ rk ≤ j.val) → b i j = 0) ∧ φ * T.map (Int.cast : ℤ → ℚ) = φ + bᵀ * (α * c.map (Int.cast : ℤ → ℚ)) := by
  first | exact @GlobalTheory.isometry_fixing_rowSpace_shift | exact GlobalTheory.isometry_fixing_rowSpace_shift | (intros; apply GlobalTheory.isometry_fixing_rowSpace_shift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.posDef_one_sub_mul_conjTranspose_of_posDef_swap : ∀ {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ), (1 - zᴴ * z).PosDef → (1 - z * zᴴ).PosDef := by
  first | exact @GlobalTheory.PosDefSwap.main | exact GlobalTheory.PosDefSwap.main | (intros; apply GlobalTheory.PosDefSwap.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef : ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef → ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  first | exact @GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | exact GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | (intros; apply GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.coeffMatrix_mul_eq_of_same_intCombinations : ∀ (g r r₀ : ℕ) (l l' : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (T : Matrix (Fin r) (Fin r) ℤ), LinearIndependent ℤ l → (∀ i, l' i = ∑ j, T i j • l j) → (∀ i, w i = ∑ j, c i j • l j) → (∀ i, w i = ∑ j, c i j • l' j) → c * T = c := by
  first | exact @GlobalTheory.FrameFix.coeff_mul_eq_of_same_combinations | exact GlobalTheory.FrameFix.coeff_mul_eq_of_same_combinations | (intros; apply GlobalTheory.FrameFix.coeff_mul_eq_of_same_combinations <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_rational_symplecticBasis_adapted_coisotropic : ∀ (g r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ), r = 2 * g → Mᵀ = -M → M.det ≠ 0 → LinearIndependent ℚ (fun i j => (c i j : ℚ)) → (∀ v : Fin r → ℝ, (∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (c i j : ℝ)) = 0) → v ∈ Submodule.span ℝ (Set.range fun i j => (c i j : ℝ))) → ∃ (rk : ℕ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ), rk ≤ g ∧ (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 ∧ φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 ∧ φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 ∧ (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) ∧ (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) ∧ (∀ m (j : Fin g), j.val < rk → dl m j = 0) ∧ c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ := by
  first | exact @GlobalTheory.SymplecticNormalForm.exists_adapted_rational_symplectic_basis | exact GlobalTheory.SymplecticNormalForm.exists_adapted_rational_symplectic_basis | (intros; apply GlobalTheory.SymplecticNormalForm.exists_adapted_rational_symplectic_basis <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

theorem isHomogeneous_of_mul_isHomogeneous_right {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ)
    (hQ : Q ≠ 0) (hQh : Q.IsHomogeneous b) (hPQ : (P * Q).IsHomogeneous (a + b)) :
    P.IsHomogeneous a := by
  have key : ∀ k, homogeneousComponent (k + b) (P * Q) = homogeneousComponent k P * Q := by
    intro k
    conv_lhs => rw [← sum_homogeneousComponent P]

    rw [Finset.sum_mul, map_sum]
    have hterm : ∀ i, homogeneousComponent (k + b) (homogeneousComponent i P * Q)
        = if i = k then homogeneousComponent i P * Q else 0 := by
      intro i
      have hm : homogeneousComponent i P * Q ∈ homogeneousSubmodule σ ℝ (i + b) :=
        (homogeneousComponent_isHomogeneous i P).mul hQh
      rw [homogeneousComponent_of_mem hm]
      by_cases h : i = k
      · simp [h]
      · have : k + b ≠ i + b := by omega
        rw [if_neg this, if_neg h]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · subst_vars; rfl
    · simp only [Finset.mem_range, not_lt] at h
      rw [homogeneousComponent_eq_zero k P (by omega), zero_mul]
  have hzero : ∀ k, k ≠ a → homogeneousComponent k P = 0 := by
    intro k hk
    have h1 : homogeneousComponent (k + b) (P * Q) = 0 := by
      have : k + b ≠ a + b := by omega
      have e := homogeneousComponent_of_mem (m := k + b) (hPQ : P * Q ∈ homogeneousSubmodule σ ℝ (a + b))
      rw [e, if_neg this]
    rw [key] at h1
    exact (mul_eq_zero.mp h1).resolve_right hQ
  rw [← sum_homogeneousComponent P]
  apply IsHomogeneous.sum
  intro k _
  by_cases hk : k = a
  · subst hk; exact homogeneousComponent_isHomogeneous k P
  · rw [hzero k hk]; exact isHomogeneous_zero _ _ _

end GlobalTheory.GrassTop
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_common_denominator_rat_matrices : ∀ (a g : ℕ) (b : Fin a → Matrix (Fin g) (Fin g) ℚ), ∃ (D : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D ∧ ∀ k i j, (B k i j : ℚ) = D * b k i j := by
  first | exact @GlobalTheory.rat_matrix_common_denom | exact GlobalTheory.rat_matrix_common_denom | (intros; apply GlobalTheory.rat_matrix_common_denom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef : ∀ (a g rk : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → ¬ (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → ∃ v : Fin g → ℤ, v ≠ 0 ∧ (∀ j : Fin g, rk ≤ j.val → v j = 0) ∧ ∀ k, (B k).mulVec v = 0 := by
  first | exact @GlobalTheory.intPsd_common_kernel_of_sum_not_posDef | exact GlobalTheory.intPsd_common_kernel_of_sum_not_posDef | (intros; apply GlobalTheory.intPsd_common_kernel_of_sum_not_posDef <;> assumption)
end
