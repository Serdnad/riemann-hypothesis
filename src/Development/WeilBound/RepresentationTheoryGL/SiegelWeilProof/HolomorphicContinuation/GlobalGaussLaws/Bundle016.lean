module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

def cf (θ : InfFam D) (τ : D.what₂.Tau) : AE D →+* ℂ := RingHom.comp (θ τ) (infPart D)

theorem compAt_eq_map {m k : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (X : Mx D m k) :
    compAt θ τ X = X.map (cf θ τ) := rfl

theorem compAt_mulM {m k l : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (X : Mx D m k) (Y : Mx D k l) :
    compAt θ τ (X * Y) = compAt θ τ X * compAt θ τ Y := by
  rw [compAt_eq_map, compAt_eq_map, compAt_eq_map]
  exact Matrix.map_mul

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (1 : Mx D n n) = 1 := by
  rw [compAt_eq_map]
  exact Matrix.map_one (cf θ τ) (map_zero _) (map_one _)

theorem compAt_add {m k : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (X Y : Mx D m k) :
    compAt θ τ (X + Y) = compAt θ τ X + compAt θ τ Y := by
  rw [compAt_eq_map, compAt_eq_map, compAt_eq_map]
  exact Matrix.map_add (cf θ τ) (map_add (cf θ τ)) X Y

theorem ext_mx {m k : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {X Y : Mx D m k}
    (hf : X.map (finPart D) = Y.map (finPart D)) (hc : ∀ τ, compAt θ τ X = compAt θ τ Y) : X = Y := by
  obtain ⟨-, -, -, -, hext⟩ := h
  refine Matrix.ext fun i j => ?_
  refine sub_eq_zero.mp (hext _ ?_ fun τ => ?_)
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun hf i) j
  · rw [map_sub, map_sub, sub_eq_zero]
    exact congrFun (congrFun (hc τ) i) j

def baseColumnsAt (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) (M : Matrix (Fin n) (Fin n) ℂ) : Mx D n n :=
  1 + atT σ τ (M - 1)

theorem component_adelic_point_matrix {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin n) (Fin n) ℂ) : compAt θ τ (baseColumnsAt σ τ M) = M := by
  show compAt θ τ (1 + atT σ τ (M - 1)) = M
  rw [compAt_add, compAt_one, compAt_atT h]
  abel

theorem component_adelic_point_ne {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {τ τ' : D.what₂.Tau}
    (hne : τ' ≠ τ) (M : Matrix (Fin n) (Fin n) ℂ) : compAt θ τ' (baseColumnsAt σ τ M) = 1 := by
  show compAt θ τ' (1 + atT σ τ (M - 1)) = 1
  rw [compAt_add, compAt_one, compAt_atT_ne h hne, add_zero]

theorem finite_part_adelic_point_matrix {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin n) (Fin n) ℂ) : (baseColumnsAt σ τ M).map (finPart D) = 1 := by
  show (1 + atT σ τ (M - 1)).map (finPart D) = 1
  rw [Matrix.map_add (finPart D) (map_add (finPart D)), Matrix.map_one (finPart D) (map_zero _) (map_one _),
    show (atT σ τ (M - 1)).map (finPart D) = 0 from Matrix.ext fun i j => finPart_atT h τ (M - 1) i j, add_zero]

theorem finPart_atT_map {m k : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (τ : D.what₂.Tau) (M : Matrix (Fin m) (Fin k) ℂ) : (atT σ τ M).map (finPart D) = 0 := by
  exact Matrix.ext fun i j => finPart_atT h τ M i j

def unitAt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (a : GL (Fin n) ℂ) : GL (Fin n) (AE D) where
  val := baseColumnsAt σ τ a.1
  inv := baseColumnsAt σ τ a⁻¹.1
  val_inv := ext_mx h (by rw [Matrix.map_mul, finite_part_adelic_point_matrix h, finite_part_adelic_point_matrix h, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    fun τ' => by
      by_cases e : τ' = τ
      · subst e; rw [compAt_mulM, component_adelic_point_matrix h, component_adelic_point_matrix h, compAt_one]; simp
      · rw [compAt_mulM, component_adelic_point_ne h e, component_adelic_point_ne h e, compAt_one, Matrix.one_mul]
  inv_val := ext_mx h (by rw [Matrix.map_mul, finite_part_adelic_point_matrix h, finite_part_adelic_point_matrix h, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    fun τ' => by
      by_cases e : τ' = τ
      · subst e; rw [compAt_mulM, component_adelic_point_matrix h, component_adelic_point_matrix h, compAt_one]; simp
      · rw [compAt_mulM, component_adelic_point_ne h e, component_adelic_point_ne h e, compAt_one, Matrix.one_mul]

theorem unitAt_val {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (a : GL (Fin n) ℂ) : (unitAt h τ a).1 = baseColumnsAt σ τ a.1 := rfl

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneH

variable {D : D7} {n : ℕ}

def hhT (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : GA D V :=
  atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹)

def CurveSt : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (ε : Fin V.rank → Bool) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → IsTauFrame V τ s ε fr → IsUe ε X →
    hhT θ V τ fr X 0 = 1 ∧ (∀ a b, hhT θ V τ fr X (a + b) = hhT θ V τ fr X a * hhT θ V τ fr X b) ∧
    ∀ Φ : schwartzA θ V.rank n,
      (∀ y : Mx D V.rank n, Continuous fun p : GA D V × ℝ =>
        Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X p.2)) (HMul.hMul (mt V p.1⁻¹) y))) ∧
      ∀ (z : Mx D V.rank n) (t : ℝ), HasDerivAt (fun u : ℝ => Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X u)) z))
        (DX θ V τ fr X Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X t)) z)) t

end PositivityTheory.Rg.Sw.Glob.DerOneH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob

end PositivityTheory.Rg.Sw.Glob

namespace PositivityTheory.Rg.Sw.Glob.LocCellA

theorem block_matrix_mul_comm_ring {R : Type} [Ring R] {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_diagonal_one_eq_one {R : Type} [Ring R] {n : ℕ} : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = blk4 1 0 0 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_map {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.fromBlocks_map]
  rfl

theorem map_neg_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (-1 : Matrix (Fin n) (Fin n) R).map f = -1 := by
  change (f.mapMatrix) (-1) = -1
  rw [map_neg, map_one]

theorem map_one' {R S : Type} [Ring R] [Ring S] {n : ℕ} (f : R →+* S) :
    (1 : Matrix (Fin n) (Fin n) R).map f = 1 := by
  change (f.mapMatrix) 1 = 1
  rw [map_one]

theorem blockMatrixTwoByTwoFin_transpose {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d)ᵀ = blk4 aᵀ cᵀ bᵀ dᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

end PositivityTheory.Rg.Sw.Glob.LocCellA

namespace PositivityTheory.Rg.Sw.Glob


open LocCellA in
theorem wEx : WEx := by
  intro D n
  let M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 1 (-1) 0
  let Mi : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := blk4 0 (-1) 1 0
  have h1 : M * Mi = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  have h2 : Mi * M = 1 := by simp [M, Mi, block_matrix_mul_comm_ring, block_matrix_diagonal_one_eq_one]
  let u : GL (Fin (n + n)) (AE D) := ⟨M, Mi, h1, h2⟩
  have hu : u ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M * JR (AF D.host.F) (Jst D n) * M = JR (AF D.host.F) (Jst D n)
    have hJ : JR (AF D.host.F) (Jst D n) = M := by
      simp [JR, Jst, M, block_matrix_map, map_neg_one', map_one']
    rw [hJ]
    simp [Formalism.UG.cT, M, block_matrix_map, blockMatrixTwoByTwoFin_transpose, block_matrix_mul_comm_ring, map_neg_one', map_one']
  exact ⟨⟨u, hu⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def NbFacts : Prop :=
  ∀ (D : D7) (n : ℕ) (nb : hermA D n → G D n), PositivityTheory.PfSWUS.IsNMap nb →
    Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ ratHerm D n, nb γ ∈ GF D n

def CharFacts : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : HermE D n,
    Continuous (fun b : hermA D n => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧
    ∀ b : hermA D n, ‖ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1

def HermCocompact : Prop :=
  ∀ (D : D7) (r : ℕ), ∃ K : Set (hermA D r), IsCompact K ∧ ∀ x, ∃ l ∈ ratHerm D r, x - l ∈ K

theorem gLamBd_of (hNb : NbFacts) (hCh : CharFacts) (hCo : HermCocompact) : GLamBd := by
  intro D n ψ hψ L hL
  obtain ⟨nb, lam, 𝓖, β, g, ⟨hnb, hlam, hfd, hvol⟩, -, rfl⟩ := hL
  obtain ⟨hcont, hadd, hrat⟩ := hNb D n nb hnb
  obtain ⟨hχc, hχn⟩ := hCh D n ψ hψ β
  obtain ⟨K, hK, hKc⟩ := hCo D n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  set χ : hermA D n → ℂ := fun b => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) with hχ
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun b : hermA D n => nb b * g := hcont.mul continuous_const

  have hper : ∀ (F : G D n → ℂ), (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) → ∀ b, ∃ k ∈ K,
      F (nb b * g) = F (nb k * g) := by
    intro F hF b
    obtain ⟨l, hl, hbl⟩ := hKc b
    refine ⟨b - l, hbl, ?_⟩
    have e : nb b = nb l * nb (b - l) := by rw [← hadd, add_sub_cancel]
    rw [e, mul_assoc, hF _ (hrat l hl)]

  have hbd : ∀ (F : G D n → ℂ) (M : ℝ), (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) →
      (∀ x ∈ (fun b => nb b * g) '' K, ‖F x‖ ≤ M) → ∀ b, ‖F (nb b * g) * χ b‖ ≤ M := by
    intro F M hF hM b
    obtain ⟨k, hk, e⟩ := hper F hF b
    rw [norm_mul, hχn b, mul_one, e]
    exact hM _ ⟨k, hk, rfl⟩
  have hint : ∀ (F : G D n → ℂ), Continuous F → (∀ γ ∈ GF D n, ∀ x, F (γ * x) = F x) →
      IntegrableOn (fun b => F (nb b * g) * χ b) 𝓖 lam := by
    intro F hFc hF
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hFc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_
    · exact ((hFc.comp hcm).mul hχc).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun b => hbd F M hF hM b
  refine ⟨fun a F F' hFc hF'c hF hF' => ?_, ⟨(fun b => nb b * g) '' K, hK.image hcm, fun F M hFc hF hM => ?_⟩⟩
  · simp only [PositivityTheory.PfSWUS.fc]
    have e : (fun b : hermA D n => (a • F + F') (nb b * g) *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) =
        fun b => a * (F (nb b * g) * χ b) + F' (nb b * g) * χ b := by
      funext b; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]; ring
    rw [e, integral_add ((hint F hFc hF).const_mul a) (hint F' hF'c hF'), integral_const_mul]
  · show ‖∫ b in 𝓖, F (nb b * g) * χ b ∂lam‖ ≤ M
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun b _ => hbd F M hF hM b)
    have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
    rwa [hr, mul_one] at h1

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open Topology

namespace PositivityTheory.Rg.Sw.Glob

def ContDeriv : Prop :=
  ∀ (m n : ℕ) (U : Set ℂ), IsOpen U → ∀ f : ℂ → (Fin m → Fin n → ℂ) → ℂ,
    ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => f p.1 p.2) (U ×ˢ Set.univ) →
    (∀ u, DifferentiableOn ℂ (fun z => f z u) U) →
    ∀ r : ℕ, ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => iteratedDeriv r (fun z => f z p.2) p.1) (U ×ˢ Set.univ)

def SchScale : Prop :=
  ∀ (m n : ℕ) (f : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ) (X : Fin n → ℝ) (a : ℂ), IsSch f →
    IsSch (fun u => a * f (fun i j => u i j * Real.exp (s * X j)))

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def IsAwayFn {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (Ψ : Mx D m n → ℂ) : Prop :=
  ∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) → Ψ x = Ψ x'

def IsTrivAt (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop := compAt θ τ (mat x) = 1

def IsLocFact {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ι : GR n →* G D n)
    (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)) : Prop :=
  (∀ y f, IsSch f → IsSch (L y f)) ∧ ∀ (y : GR n) Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
    (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L y f) Ψ

def epsT {m : ℕ} (t : ℝ) (ε : Fin m → Bool) : Fin m → Bool := fun a => if 0 < t then ε a else !ε a

def gramB {m : ℕ} (ε : Fin m → Bool) (b : Bool) (y : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => evX (Qb ε b i j) y

def gZf {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true y).trace - Complex.I * c * (Zᴴ * gramB (epsT t ε) false y).trace)

def IsSiegel (Z : Matrix (Fin n) (Fin n) ℂ) : Prop := ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef

def actZ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂) * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂)⁻¹

def jF (e : ℤ) (p q : ℕ) (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (mR y).det ^ e * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂).det ^ (-(p : ℤ)) *
    ((mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂).det ^ (-(q : ℤ))

def GZSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSch (gZf ε t c Z)

def AwayAct : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ x : G D n, IsTrivAt θ τ x →
    ∃ A : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ), ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (A Ψ) ∧
      ∀ f (hf : IsSch f), (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (A Ψ)

def DecompAway : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsInfFam θ → IsPlaceEmb θ τ ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), IsTrivAt θ τ x ∧ g = x * ι y ∧ ∀ y' : GR n, x * ι y' = ι y' * x

def LocFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∃ L, IsLocFact ω τ fr ι L

def GaussLaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∃ e : ℤ, ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) y Z *
        gZf ε (tLoc l τ) (cLoc l τ) (actZ y Z) u

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix

namespace PositivityTheory.Rg.Sw.Glob

def SchOps : Prop :=
  ∀ (m n : ℕ), (∀ f g : (Fin m → Fin n → ℂ) → ℂ, IsSch f → IsSch g → IsSch (fun u => f u + g u)) ∧
    (∀ (c : ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsSch f → IsSch (fun u => c * f u)) ∧
    (∀ (a : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsUnit a.det → IsSch f →
      IsSch (fun u => f (Matrix.of u * a))) ∧
    (∀ (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), bᴴ = b → IsSch f →
      IsSch (fun u => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace) * f u)) ∧
    ∃ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f ∧ f 0 = 1

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open Vac

theorem lIvac : LIvac := by
  intro m n ε c t p q e hc hpq S C hS h1 hy hcell
  have hα : ((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)) ≠ 0 := by
    apply mul_ne_zero <;> apply zpow_ne_zero <;> apply pow_ne_zero <;> simp
  have key : ∀ g : GR n, (toBlocks₂₁ (mR g)).det ≠ 0 →
      S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g hg
    obtain ⟨y, h, b, hy0, hb, hh, rfl⟩ := bigcell g hg
    rw [hy y h hy0, hcell h b hb hh, secN_eval ε c t p q hc hpq b hb, vacuum_section_mul_parabolic p q e y h hy0,
      vacuum_section_big_cell p q e h b hh, mul_zpow, mul_zpow]
    field_simp
  have hall : ∀ g, S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g
    exact congrFun (Continuous.ext_on dense_cell hS (continuous_const.mul (continuous_vacuum_section p q e)) key) g
  have hlam := hall 1
  rw [h1, weight_factor_one, mul_one] at hlam
  intro g
  rw [hall g, ← hlam, one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end
