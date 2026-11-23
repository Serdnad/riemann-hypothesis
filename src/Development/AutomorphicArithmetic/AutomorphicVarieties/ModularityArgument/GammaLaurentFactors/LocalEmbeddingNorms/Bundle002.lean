module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.HodgeTateFromSandwich
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaFunctionalUniqueness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralShellMean
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdMulti
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.AutomorphicForms.AdmissibleInduction
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
import GroundTheory.AutomorphicForms.GL2.GJInducedCoeff
public import GroundTheory.AutomorphicForms.GL2.GJLocalFECoeff
import GroundTheory.AutomorphicForms.Bundle008
public import GroundTheory.AutomorphicForms.GL2.GJFEInduced
import GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi
public import GroundTheory.AutomorphicForms.GL2.GJFELevi
import GroundTheory.AutomorphicForms.GL2.GJFELeviPeel
import GroundTheory.AutomorphicForms.WhittakerGroups
import GroundTheory.AutomorphicForms.JacquetAdmissible
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.GodementJacquet
open Matrix GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic MeasureTheory GroundTheory.Automorphic.Measures
  GroundTheory.Automorphic.GJMatrix
open scoped NNReal ENNReal Pointwise

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL _root_.GlobalTheory.CompanionTheory.QL.instMeasGL

private theorem UpperTheory.V.Z.Gam.induced_matrix_coefficients {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} (hπ : IsSmooth π) {β : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi F n β) W} (hσs : IsSmooth σ)
    (ι : Representation.IntertwiningMap π (parabolicInd F n β σ))
    (hι : Function.Injective ι) (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle}
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ} (hγ : InducedFE F σ μ ψ γ) : IsGammaFactor F π μ ψ γ := by
  classical
  intro Φ hΦ v ℓ hℓ
  have : μ.IsInvInvariant := ⟨inv_eq_self_GL F n μ⟩

  obtain ⟨m₀, hm₀⟩ := hΦ.exists_congruence_invariant
  obtain ⟨m₁, -, hm₁⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((hπ v).mem_nhds (one_mem (stabilizerOf π v)))
  obtain ⟨m₂, -, hm₂⟩ := (hasBasis_nhds_one F n).mem_iff.1
    ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual π) ℓ)))
  set m := max m₀ (max m₁ m₂) with hmdef
  set K := congruenceSubgroup F n m with hKdef
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := isCompact_congruenceSubgroup F n m
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := isOpen_congruenceSubgroup F n m
  have hK0 : ∀ k ∈ K, k ∈ integralGL F n := fun k hk => congruenceSubgroup_le F n m hk
  have hvK : ∀ k ∈ K, π k v = v := fun k hk =>
    hm₁ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_left m₁ m₂)) hk)
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (π k x) = ℓ x := mem_fixedVectors_dual.1 fun k hk =>
    hm₂ (congruenceSubgroup_antitone F n (le_max_of_le_right (le_max_right m₁ m₂)) hk)
  have hΦK : ∀ k ∈ K, ∀ X, Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := fun k hk =>
    hm₀ k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)

  obtain ⟨lam, hlamK, hlam⟩ := exists_extend_dual hπ (isSmooth_parabolicInd σ) ι hι hKc hKo hℓK
  obtain ⟨R, hR₀, hR⟩ := exists_reps_congruenceSubgroup F n m
  obtain ⟨ℓx, hℓxK, hdec⟩ := exists_eval_decomposition hσs hR₀ hR lam
  set φ : parabolicIndSpace F n β σ := ι v with hφdef
  have hφK : φ ∈ fixedVectors (parabolicInd F n β σ) K := fun k hk => by
    rw [hφdef, ← ι.isIntertwining, hvK k hk]
  have hf : ∀ g, matrixCoeff π v ℓ g = lam (parabolicInd F n β σ g φ) := fun g => by
    rw [matrixCoeff, ← hlam, hφdef, ι.isIntertwining]
  have hℓxs : ∀ x, ℓx x ∈ smoothVectors (Representation.dual σ) := fun x =>
    mem_smoothVectors_of_mem_fixedVectors (isOpen_subgroupOf_levi hKo) (hℓxK x)

  set Φx : GL (Fin n) F → Matrix (Fin n) (Fin n) F → ℂ := fun x X =>
    Φ (((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X) with hΦxdef
  have hΦx : ∀ x, IsSchwartzBruhat (Φx x) := fun x => hΦ.comp_mul_left x⁻¹
  have hJ := fun x : GL (Fin n) F =>
    hγ (Φx x) (hΦx x) (φ : GL (Fin n) F → W) φ.2 (ℓx x) (hℓxs x)
  choose hJA hJB hJR using hJ
  choose sA hsA using hJA
  choose sB hsB using hJB
  set SA : ℝ := ∑ x ∈ R, |sA x| with hSA
  have hSAx : ∀ x ∈ R, sA x ≤ SA := fun x hx =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |sA x|)
      (fun _ _ => abs_nonneg _) hx)
  set SB : ℝ := -∑ x ∈ R, |sB x| with hSB
  have hSBx : ∀ x ∈ R, SB ≤ sB x := fun x hx => by
    have h1 := Finset.single_le_sum (f := fun x => |sB x|) (fun _ _ => abs_nonneg _) hx
    have h2 := neg_abs_le (sB x)
    linarith

  obtain ⟨r, A, -, hA⟩ := hΦ.exists_invariant
  have hAdec : ∀ s : ℂ, SA < s.re →
      Integrable (fun g : GL (Fin n) F => (Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2)) *
        lam (parabolicInd F n β σ g φ)) μ ∧
      ∫ g : GL (Fin n) F, (Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2)) *
        lam (parabolicInd F n β σ g φ) ∂μ =
        ∑ x ∈ R, ∫ g : GL (Fin n) F, (Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2)) *
          ℓx x ((φ : GL (Fin n) F → W) (x * g)) ∂μ := by
    intro s hs
    refine integrable_and_integral_mul_coeff_eq μ hKc hKo hK0 hlamK hφK hdec
      (H := fun g : GL (Fin n) F => Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2))
      (fun k hk g => ?_) (fun k hk g => ?_) (fun j => ?_) (fun x hx => ?_)
    · rw [Units.val_mul, (hΦK k hk _).1, detPow_mul, detPow_of_mem_integralGL (hK0 k hk), one_mul]
    · rw [Units.val_mul, (hΦK k hk _).2, detPow_mul, detPow_of_mem_integralGL (hK0 k hk), mul_one]
    · refine HasCompactSupport.intro (isCompact_shell F n A j) fun g hg => ?_
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with hj
      · by_contra hne
        exact hg ⟨hA _ (left_ne_zero_of_mul hne), hj⟩
      · rfl
    · refine ((hsA x s (lt_of_le_of_lt (hSAx x hx) hs)).comp_mul_left x).congr
        (Filter.Eventually.of_forall fun g => ?_)
      simp only [Φx]
      rw [Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul, detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul]

  have hΦh : IsSchwartzBruhat (localMatrixFourier ψ Φ) := hΦ.localMatrixFourier hψ hψ1
  have hΦhK := localMatrixFourier_invariant ψ hK0 hΦK
  obtain ⟨r', A', -, hA'⟩ := hΦh.exists_invariant
  have hBdec : ∀ s : ℂ, s.re < SB →
      Integrable (fun g : GL (Fin n) F =>
        (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * lam (parabolicInd F n β σ g φ)) μ ∧
      ∫ g : GL (Fin n) F, (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * lam (parabolicInd F n β σ g φ) ∂μ =
        ∑ x ∈ R, ∫ g : GL (Fin n) F,
          (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * ℓx x ((φ : GL (Fin n) F → W) (x * g)) ∂μ := by
    intro s hs
    refine integrable_and_integral_mul_coeff_eq μ hKc hKo hK0 hlamK hφK hdec
      (H := fun g : GL (Fin n) F =>
        localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2))
      (fun k hk g => ?_) (fun k hk g => ?_) (fun j => ?_) (fun x hx => ?_)
    · rw [_root_.mul_inv_rev, Units.val_mul, (hΦhK k⁻¹ (inv_mem hk) _).2, detPow_mul,
        detPow_of_mem_integralGL (hK0 _ (inv_mem hk)), mul_one]
    · rw [_root_.mul_inv_rev, Units.val_mul, (hΦhK k⁻¹ (inv_mem hk) _).1, detPow_mul,
        detPow_of_mem_integralGL (hK0 _ (inv_mem hk)), one_mul]
    · refine HasCompactSupport.intro ((isCompact_shell F n A' (-j)).image continuous_inv)
        fun g hg => ?_
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with hj
      · by_contra hne
        exact hg ⟨g⁻¹, ⟨hA' _ (left_ne_zero_of_mul hne), by rw [ordDet_inv, hj]⟩, inv_inv g⟩
      · rfl
    · refine (((hsB x s (lt_of_lt_of_le hs (hSBx x hx))).comp_inv).comp_mul_left x).congr
        (Filter.Eventually.of_forall fun g => ?_)
      simp only [Φx]
      rw [inv_inv, _root_.mul_inv_rev, Units.val_mul, localMatrixFourier_inv_mul ψ (hR₀ x hx),
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
        detPow_mul, detPow_of_mem_integralGL (inv_mem (hR₀ x hx)), mul_one]

  have hsumFE := RatFE.sum (F := F) (γ := γ) R (fun x _ => hJR x)
  refine hsumFE.congr ⟨SA, fun s hs => ?_⟩ ⟨SB, fun s hs => ?_⟩
  · have e1 : zetaIntegral μ Φ (matrixCoeff π v ℓ) s = ∫ g : GL (Fin n) F,
        (Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2)) *
          lam (parabolicInd F n β σ g φ) ∂μ := by
      rw [zetaIntegral]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only
      rw [hf g]
      ring
    rw [e1, (hAdec s hs).2]
    refine Finset.sum_congr rfl fun x hx => ?_
    calc ∫ g : GL (Fin n) F, (Φ (g : Matrix (Fin n) (Fin n) F) *
          detPow g (s + ((n : ℂ) - 1) / 2)) * ℓx x ((φ : GL (Fin n) F → W) (x * g)) ∂μ
        = ∫ g : GL (Fin n) F, (fun g : GL (Fin n) F => Φx x (g : Matrix (Fin n) (Fin n) F) *
            detPow g (s + ((n : ℂ) - 1) / 2) * ℓx x ((φ : GL (Fin n) F → W) g)) (x * g) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          simp only [Φx]
          rw [Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul, detPow_mul, detPow_of_mem_integralGL (hR₀ x hx), one_mul]
      _ = _ := integral_mul_left_eq_self (μ := μ) (fun g : GL (Fin n) F =>
          Φx x (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) *
            ℓx x ((φ : GL (Fin n) F → W) g)) x
  · have e1 : zetaIntegral μ (localMatrixFourier ψ Φ) (fun g => matrixCoeff π v ℓ g⁻¹) (1 - s) =
        ∫ g : GL (Fin n) F, (fun g : GL (Fin n) F =>
          (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * lam (parabolicInd F n β σ g φ)) g⁻¹ ∂μ := by
      rw [zetaIntegral]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [inv_inv]
      rw [hf g⁻¹]
      ring
    rw [e1, integral_inv_eq_self (fun g : GL (Fin n) F =>
      (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * lam (parabolicInd F n β σ g φ)) μ,
      (hBdec s hs).2]
    refine Finset.sum_congr rfl fun x hx => ?_
    set Bx : GL (Fin n) F → ℂ := fun g => localMatrixFourier ψ (Φx x) (g : Matrix (Fin n) (Fin n) F) *
      detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓx x ((φ : GL (Fin n) F → W) g⁻¹) with hBx
    calc ∫ g : GL (Fin n) F,
          (localMatrixFourier ψ Φ ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            detPow g⁻¹ (1 - s + ((n : ℂ) - 1) / 2)) * ℓx x ((φ : GL (Fin n) F → W) (x * g)) ∂μ
        = ∫ g : GL (Fin n) F, (fun g => Bx g⁻¹) (x * g) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          simp only [Bx, Φx]
          rw [inv_inv, _root_.mul_inv_rev, Units.val_mul, localMatrixFourier_inv_mul ψ (hR₀ x hx),
            Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
            detPow_mul, detPow_of_mem_integralGL (inv_mem (hR₀ x hx)), mul_one]
      _ = ∫ g : GL (Fin n) F, Bx g⁻¹ ∂μ :=
          integral_mul_left_eq_self (μ := μ) (fun g : GL (Fin n) F => Bx g⁻¹) x
      _ = ∫ g : GL (Fin n) F, Bx g ∂μ := integral_inv_eq_self Bx μ

theorem UpperTheory.V.Z.Gam.coefInd :
    UpperTheory.V.Z.Gam.CoefInd := by
  intro F _ _ _ _ _ _ n _ _ V _ _ π hπ β W _ _ σ hσ ι hι μ _ ψ hψ hψ1 γ hγ
  exact UpperTheory.V.Z.Gam.induced_matrix_coefficients hπ hσ ι hι μ hψ hψ1 hγ
end
end

section

noncomputable section

open MeasureTheory Measure GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal ENNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL _root_.GlobalTheory.CompanionTheory.QL.instMeasGL

namespace UpperTheory.V.Z.Gam

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {β : Fin n → ℕ}
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

private theorem exists_shape (hB : LdBlock) (hσ : IsAdmissible σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (κ : levi F n β →* ℝ≥0) (hκ : Continuous κ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure]
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ γ : RatFunc ℂ, LdShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ (cntF σ) ∧ LeviFE F σ κ μM ψ γ := by
  classical
  have hsm : IsSmooth σ := hσ.1
  haveI bGL : ∀ m, BorelSpace (GL (Fin m) F) := fun m => borelSpace_GL_units m
  haveI nz : ∀ a : ↑(Set.range β), NeZero (blockSize β a) := fun a => ⟨(blockSize_pos β a).ne'⟩
  obtain ⟨e, he⟩ : ∃ e, e = leviEquivPi F β := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = twist (nnrealCharC κ) σ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (prodPUnitEquiv.{_, 0} ((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F)).trans e.symm :=
    ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Representation ℂ (((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F) × PUnit.{1}) W,
      ρ = τ.comp E.toMonoidHom := ⟨_, rfl⟩
  have hEx : ∀ x, E (x, (1 : PUnit.{1})) = e.symm x := fun x => by subst hE; rfl
  have hτm : ∀ m v, τ m v = nnrealCharC κ m • σ m v := fun m v => by subst hτ; rfl
  have hρx : ∀ x v, ρ (x, (1 : PUnit.{1})) v = nnrealCharC κ (e.symm x) • σ (e.symm x) v := fun x v => by
    subst hρ; rw [← hτm, ← hEx]; rfl
  have hτA : IsAdmissible τ := hτ ▸ isAdmissible_twist κ hκ σ hσ
  haveI hτI : Representation.IsIrreducible τ := hτ ▸ isIrreducible_twist κ σ
  have hρA : IsAdmissible ρ := hρ ▸ (isAdmissible_comp_iff E τ).2 hτA
  haveI hρI : Representation.IsIrreducible ρ := hρ ▸ (isIrreducible_comp_iff E τ).2 hτI
  have hℓ : ∀ ℓ, ℓ ∈ smoothVectors (Representation.dual ρ) ↔ ℓ ∈ smoothVectors σ.dual := fun ℓ => by
    subst hρ hτ
    rw [mem_smoothVectors_dual_comp_iff, mem_smoothVectors_dual_twist_iff κ hκ]
  haveI : Nontrivial W := nontrivial_of_isIrreducible σ
  obtain ⟨ω, hω⟩ := exists_blockChar (σ := τ) hτA.1
  have hω0 : ∀ b, ω b ≠ 0 := by
    intro b h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    have h1 : τ (blockUnif F b)⁻¹ (τ (blockUnif F b) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hω, h0, zero_smul, map_zero]
  have hcent : ∀ (i : ↑(Set.range β)) (v : W),
      ρ (Pi.mulSingle i (centralUnif F (blockSize β i)), (1 : PUnit.{1})) v = ω i • v := by
    intro i v
    rw [← hω, ← leviEquivPi_symm_mulSingle, ← he, ← hEx]
    subst hρ; rfl
  have hcpt : ∀ (v : W), ∀ ℓ ∈ smoothVectors (Representation.dual ρ), ∃ C, IsCompact C ∧
      ∀ (x : (a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F),
        ℓ (ρ (x, (1 : PUnit.{1})) v) ≠ 0 →
          ∃ j : ↑(Set.range β) → ℤ, (fun i => centralUnif F (blockSize β i) ^ j i) * x ∈ C := by
    intro v ℓ hl
    obtain ⟨C0, hC0, hC0m⟩ := exists_compact_of_coeff hsm hc v ((hℓ ℓ).1 hl) (fun _ => 0)
      (fun a => (blockSize β a : ℤ) - 1)
    refine ⟨e '' C0, hC0.image e.continuous, fun x hx => ?_⟩
    refine ⟨fun a => -(ordDet (x a) / (blockSize β a : ℤ)), ?_⟩
    obtain ⟨y, hy⟩ : ∃ y, y = (fun i => centralUnif F (blockSize β i) ^ (-(ordDet (x i) / (blockSize β i : ℤ)))) * x :=
      ⟨_, rfl⟩
    rw [← hy]
    refine ⟨e.symm y, hC0m _ ?_ ?_, e.apply_symm_apply y⟩
    · have h1 : ρ (y, (1 : PUnit.{1})) v =
          (∏ i, ω i ^ (-(ordDet (x i) / (blockSize β i : ℤ)))) • ρ (x, (1 : PUnit.{1})) v := by
        have hp : (y, (1 : PUnit.{1})) = ((fun i => centralUnif F (blockSize β i) ^ (-(ordDet (x i) / (blockSize β i : ℤ)))),
            (1 : PUnit.{1})) * (x, (1 : PUnit.{1})) := by rw [hy]; rfl
        rw [hp, map_mul, Module.End.mul_apply, apply_centralPow ρ hω0 hcent]
      intro h0
      apply hx
      have h2 : ℓ (ρ (y, (1 : PUnit.{1})) v) = 0 := by rw [hρx, map_smul, h0, smul_zero]
      rw [h1, map_smul, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hω0 i))
    · intro b
      rw [← ordDet_leviEquivPi, ← he, e.apply_symm_apply, hy]
      simp only [Pi.mul_apply, ordDet_centralUnif_zpow_mul]
      have hd : (0:ℤ) < blockSize β b := by exact_mod_cast blockSize_pos β b
      have h3 := Int.emod_nonneg (ordDet (x b)) hd.ne'
      have h4 := Int.emod_lt_of_pos (ordDet (x b)) hd
      have h5 := Int.mul_ediv_add_emod (ordDet (x b)) (blockSize β b)
      constructor <;> linarith
  obtain ⟨μ', hμ'⟩ : ∃ μ' : (a : ↑(Set.range β)) → Measure (GL (Fin (blockSize β a)) F),
      μ' = fun _ => Measure.haar := ⟨_, rfl⟩
  haveI hμ'H : ∀ a, (μ' a).IsHaarMeasure := fun a => by subst hμ'; infer_instance
  obtain ⟨γ, hγs, hγfe⟩ := ldMulti_all (F := F) (W := W) hB hψ hψ1 (Fintype.card ↑(Set.range β))
    ↑(Set.range β) rfl (fun a => blockSize β a) μ' PUnit.{1} ρ hρA hρI ω hω0 hcent hcpt
  obtain ⟨s₁, hs₁⟩ := exists_integrable_multi ρ hρA.1 hω0 hcent hcpt μ'
  refine ⟨γ, ?_, ?_⟩
  · convert hγs using 1
    subst he
    unfold cntF
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    apply Finset.filter_congr
    intro i _
    apply and_congr_right
    intro _
    apply forall₂_congr
    intro g hg
    have hk : κ ((leviEquivPi F β).symm (Pi.mulSingle i g)) = 1 := by
      refine eq_one_of_mem_compact κ hκ (K := (integralGL F (blockSize β i)).map
        (((leviEquivPi F β).symm.toMonoidHom).comp (MonoidHom.mulSingle _ i))) ?_ (Subgroup.mem_map_of_mem _ hg)
      rw [Subgroup.coe_map]
      exact (isCompact_integralGL F _).image
        (f := fun x => (leviEquivPi F β).symm (Pi.mulSingle i x))
        ((leviEquivPi F β).symm.continuous.comp (continuous_mulSingle (A := fun a : ↑(Set.range β) => GL (Fin (blockSize β a)) F) i))
    have hx : ρ (Pi.mulSingle i g, (1 : PUnit.{1})) = σ ((leviEquivPi F β).symm (Pi.mulSingle i g)) := by
      refine LinearMap.ext fun v => ?_
      rw [hρx, nnrealCharC_apply, hk]
      simp
    rw [hx]
  · intro φ hφ w ℓ hl
    have hlρ := (hℓ ℓ).2 hl
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (a : ↑(Set.range β)) → Matrix (Fin (blockSize β a)) (Fin (blockSize β a)) F → ℂ,
        Ψ = fun a => blockTensor β φ a := ⟨_, rfl⟩
    have hΨs : ∀ a, IsSchwartzBruhat (Ψ a) := by subst hΨ; exact isSchwartzBruhat_blockTensor hφ
    have hΨh : ∀ a, IsSchwartzBruhat (GJMatrix.localMatrixFourier ψ (Ψ a)) :=
      fun a => (hΨs a).localMatrixFourier hψ hψ1
    have hA : ∀ s x, leviIntegrand σ κ (leviTensor β φ) w ℓ s (e.symm x) = multiA ρ Ψ w ℓ s x := by
      intro s x
      subst he hΨ
      simp only [leviIntegrand, multiA, leviTensor_leviEquivPi_symm, detPow_leviEquivPi_symm, hρx, map_smul,
        smul_eq_mul, nnrealCharC_apply, Finset.prod_mul_distrib]
      ring
    have hB2 : ∀ s x, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s (e.symm x) =
        multiB ρ (fun a => GJMatrix.localMatrixFourier ψ (Ψ a)) w ℓ s x := by
      intro s x
      subst he hΨ
      have hd : ∀ a, detPow (x a) ((blockSize β a : ℂ) - s) = ((detModulusPow (x a) : ℝ) : ℂ) * detPow (x a) (-s) :=
        fun a => by rw [sub_eq_add_neg, detPow_add, detPow_natCast]
      simp only [leviIntegrandB, multiB, leviTensorHat_leviEquivPi_symm, detPow_leviEquivPi_symm,
        leviModulus_leviEquivPi_symm, hρx, map_inv, map_smul, smul_eq_mul, nnrealCharC_apply, hd,
        Finset.prod_mul_distrib]
      push_cast
      ring
    obtain ⟨em, hem⟩ : ∃ em : levi F n β ≃ᵐ ((a : ↑(Set.range β)) → GL (Fin (blockSize β a)) F),
        em = e.toHomeomorph.toMeasurableEquiv := ⟨_, rfl⟩
    have hemx : ∀ m, em m = e m := fun m => by subst hem; rfl
    haveI : (μM.map em).IsHaarMeasure := by
      subst hem
      exact ContinuousMulEquiv.isHaarMeasure_map μM e
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, c = (μM.map em).haarScalarFactor (Measure.pi μ') := ⟨_, rfl⟩
    have hmap : μM.map em = (c : ℝ≥0∞) • Measure.pi μ' := by
      rw [hc]; exact isMulLeftInvariant_eq_smul _ _
    have hcomp : ∀ g : levi F n β → ℂ, (fun x => g (e.symm x)) ∘ em = g := fun g => by
      funext m; simp only [Function.comp, hemx, ContinuousMulEquiv.symm_apply_apply]
    have hint : ∀ g : levi F n β → ℂ,
        Integrable (fun x => g (e.symm x)) (Measure.pi μ') → Integrable g μM := by
      intro g hg
      have := hg.smul_measure (c := (c : ℝ≥0∞)) ENNReal.coe_ne_top
      rw [← hmap, em.measurableEmbedding.integrable_map_iff, hcomp] at this
      exact this
    have hI : ∀ g : levi F n β → ℂ, ∫ m, g m ∂μM = (c : ℂ) * ∫ x, g (e.symm x) ∂(Measure.pi μ') := by
      intro g
      have h1 := integral_map_equiv (μ := μM) em (fun x => g (e.symm x))
      rw [hmap, integral_smul_measure] at h1
      simp only [hemx, ContinuousMulEquiv.symm_apply_apply] at h1
      rw [← h1]
      simp [Complex.real_smul]
    refine ⟨⟨s₁, fun s hs => hint _ ?_⟩, ⟨-s₁, fun s hs => hint _ ?_⟩, ?_⟩
    · simp only [hA]
      exact (hs₁ Ψ hΨs w ℓ hlρ).1 s hs
    · simp only [hB2]
      exact (hs₁ _ hΨh w ℓ hlρ).2 s hs
    · refine ((hγfe Ψ hΨs w ℓ hlρ).const_mul (c : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
      · rw [hI]; simp only [hA]
      · rw [hI]; simp only [hB2]

end UpperTheory.V.Z.Gam

theorem UpperTheory.V.Z.Gam.leviDiv :
    UpperTheory.V.Z.Gam.LeviDiv := by
  intro F _ _ _ _ _ _ n β W _ _ σ hσ hirr hc κ hκ μ _ ψ hψ hψ1 γ hγ
  have hB : LdBlock := ldBlock_of UpperTheory.local_zeta_integral_laurent_expansion UpperTheory.local_zeta_integral_shell_mean UpperTheory.local_zeta_integral_tate_comparison
  obtain ⟨γ₀, hshape, hfe⟩ := UpperTheory.V.Z.Gam.exists_shape hB hσ hc κ hκ μ hψ hψ1
  obtain rfl := UpperTheory.local_zeta_functional_uniqueness F n β W σ hσ hirr κ hκ μ ψ γ γ₀ hγ hfe
  exact hshape
end
end

section

open NumberField IsDedekindDomain MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.GJStandardL
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL _root_.GlobalTheory.CompanionTheory.QL.instMeasGL

theorem UpperTheory.V.Z.Gam.gamLocOf :
    UpperTheory.V.Z.Gam.GamLocOf := by
  intro hL hC hS K _ _ n _ v V _ _ π s hs
  have hirr : π.IsIrreducible := hs.isIrreducible
  have hsm : IsSmooth π := hs.isSmooth
  have hψ := GroundTheory.Global.continuous_localAdelicChar (K := K) v
  have hψ1 := GroundTheory.Global.localAdelicChar_ne_one (K := K) v
  obtain ⟨β, W, _, _, σ, hσirr, hσs, hσc, hσa, ι, hι⟩ := exists_embedding_parabolicInd (π := π) hsm
  obtain ⟨γ, hγ⟩ := exists_leviFE hσa hσc (inducedChar β) continuous_inducedChar
    (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψ hψ1
  obtain ⟨P, c, j, h0, hd, hc, hγ'⟩ := hL _ n β W σ hσa hσirr hσc _ continuous_inducedChar _ _ hψ hψ1 γ hγ
  refine ⟨P, c, j, h0, ?_, hc, ?_⟩
  · rw [hd]
    exact (hS _ n V π s hs β W σ hσa hσirr hσc ι hι).symm
  · rw [← GroundTheory.Global.residueCard_adicCompletion, ← hγ']
    exact hC _ n V π hsm β W σ hσs ι hι _ _ hψ hψ1 γ (inducedFE_of_leviFE _ hψ hψ1 hγ)
end
