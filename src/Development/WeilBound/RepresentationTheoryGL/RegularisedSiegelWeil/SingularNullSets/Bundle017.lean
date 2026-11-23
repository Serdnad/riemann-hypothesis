module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWA
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle252
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle433
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullSingOfIdemEx
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

noncomputable section




open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

theorem block_matrix_apply_inl_inl_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem block_matrix_apply_inl_inr_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = b i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem block_matrix_apply_inr_inr_alt {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = d i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem block_matrix_mul_comm_ring {R : Type} [CommRing R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  rw [blk4, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rfl

theorem one_ll {R : Type} [Zero R] [One R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) =
      (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne (fun h' => h (Sum.inl_injective (finSumFinEquiv.injective h'))), Matrix.one_apply_ne h]

theorem one_lr {R : Type} [Zero R] [One R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = 0 :=
  Matrix.one_apply_ne fun h => Sum.inl_ne_inr (finSumFinEquiv.injective h)

variable {S : Finset (Pl D)}

theorem offM_of_N {g : G D n} (hg : g ∈ KOff D n S) {b : Mx D n n} (hb : mat g = blk4 1 b 0 1) : OffM S b := by
  intro i j
  have e : b i j = mat g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) := by rw [hb, block_matrix_apply_inl_inr_alt]
  refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [e, LFixTh.kOff_inf hg, one_lr]
  · rw [e, LFixTh.kOff_at hg hv, one_lr]
  · rw [e]; exact (LFixTh.kOff_int hg hv _ _).1

theorem intS_inner (V : HSp D) {S : Finset (Pl D)} (hQ : ∀ i j, IntS S (rat V.gram i j)) {x : Mx D V.rank n}
    (hx : IntOff S x) (i j : Fin n) : IntS S (GlobalTheory.StdUnn.inner V x x i j) :=
  intS_mul (adj_intS ((intOff_iff x).1 hx)) (intS_mul hQ ((intOff_iff x).1 hx)) i j

theorem fixN (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ (n : ℕ) (θ : InfFam D) (μ : Measure (Mx D V.rank n))
      (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (χ : (AE D)ˣ →* Circle),
      GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω →
      ∀ g ∈ KOff D n S, IsN g → ∀ Ψ : schwartzA θ V.rank n, (∀ x, ¬ IntOff S x → Ψ.1 x = 0) → ω g Ψ = Ψ := by
  classical
  obtain ⟨S₁, hS₁⟩ := psi_off hψ
  obtain ⟨S₂, hS₂⟩ := exists_rat_int V.gram
  refine ⟨S₁ ∪ S₂, fun S hS n θ μ ω χ hω g hg hN Ψ hΨ => ?_⟩
  obtain ⟨b, hb⟩ := hN
  have hQ := hS₂ S (fun v h => hS (Finset.mem_union_right _ h))
  refine Subtype.ext (funext fun x => ?_)
  rw [hω.unip g b hb Ψ x]
  by_cases hx : IntOff S x
  · have h := (hS₁ S (fun v h => hS (Finset.mem_union_left _ h)) _
      (offS_trace (offS_mul_right (offM_of_N hg hb) (intS_inner V hQ hx)))).2
    rw [h, one_mul]
  · rw [hΨ x hx, mul_zero]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField




namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

theorem theta_e (θ : InfFam D) (hθ : IsInfFam θ) {e : AE D} (he : ∀ w, compInf D.host.F D.host.E w e = 1)
    (τ : D.what₂.Tau) : θ τ (infPart D e) = 1 := by
  have h := ((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (e - 1)).1
    (fun w => by rw [map_sub, map_one, he w, sub_self])
  have h' := h τ
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h'
  exact h'

end PositivityTheory.Rg.Rsw.L.LBumpEx

open PositivityTheory.Rg.Rsw.L.LBumpEx Classical in
theorem PositivityTheory.Rg.Rsw.L.bumpEx : IdemEx → BumpEx := by
  intro hI D θ hθ a b S e he C hC hCi
  obtain ⟨hee, -⟩ := (hI D S).2 e he
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨hom⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := hom.isEmbedding.t2Space
  set ef : AfE D := finPart D e with hef_def
  have hef : ef * ef = ef := by rw [hef_def, ← map_mul, hee]
  have hefI : ef ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D ef hef
  have hS : ∀ v : Pl D, PositivityTheory.Rg.Rsw.L.LBumpEx.cf v ef = if v ∈ S then 1 else 0 := fun v => by
    rw [← cv_eq]; exact he.2 v
  have hθe := theta_e θ hθ he.1
  obtain ⟨N, hN, hNC⟩ := exists_nat_mul_mem (D := D)
    (Q := ⋃ i, ⋃ j, (fun x : Mx D a b => ef * finPart D (x i j)) '' C)
    (isCompact_iUnion fun i => isCompact_iUnion fun j => hC.image
      (continuous_const.mul ((GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j))))
  let W := U S ef N 1 b
  have hWo : IsOpen (W : Set (Matrix (Fin 1) (Fin b) (AfE D))) := U_isOpen hefI N 1 b
  have hWc : IsCompact (W : Set (Matrix (Fin 1) (Fin b) (AfE D))) := U_isCompact hefI hS hN 1 b
  let g : Matrix (Fin 1) (Fin b) (AfE D) → ℂ := fun w =>
    if (QuotientAddGroup.mk w : _ ⧸ W) = 0 then 1 else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → AfE D) := GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  have hg1 : ∀ w, g w = if w ∈ W then 1 else 0 := fun w => by
    simp only [g, QuotientAddGroup.eq_zero_iff]
  let rc : Mx D 1 b → (D.what₂.Tau → Fin 1 → Fin b → ℂ) := fun y τ i j => compAt θ τ y i j
  have hrc : Continuous rc := continuous_pi fun τ => GlobalTheory.RealWeil.continuous_compAt hθ τ 1 b
  have hK : IsCompact (⋃ i, (fun x : Mx D a b => rc (x.submatrix (fun _ : Fin 1 => i) id)) '' C) :=
    isCompact_iUnion fun i => hC.image (hrc.comp (continuous_id.matrix_submatrix _ _))
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let bump : ContDiffBump (0 : D.what₂.Tau → Fin 1 → Fin b → ℂ) :=
    ⟨max R 1, max R 1 + 1, lt_max_of_lt_right one_pos, by linarith⟩
  have hc : HasCompactSupport fun y => ((bump y : ℝ) : ℂ) :=
    bump.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (D.what₂.Tau → Fin 1 → Fin b → ℂ) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp bump.contDiff)
  have hf : ∀ y, f y = ((bump y : ℝ) : ℂ) := fun y => rfl
  let η₀ : Mx D 1 b → ℂ := fun y => f (fun τ i j => compAt θ τ y i j) * g (fun i j => finPart D (y i j))
  have hη : ∀ y, η₀ y = ((bump (rc y) : ℝ) : ℂ) *
      (if (Matrix.of fun i j => finPart D (y i j)) ∈ W then 1 else 0) := fun y => by
    show f _ * g _ = _
    rw [hf]
    congr 1
    exact hg1 _
  refine ⟨fun _ => η₀, fun i => ⟨Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨Ka, hKa, hKaC⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (max R 1 + 1)
      (⋃ i, ⋃ j, (fun w : Matrix (Fin 1) (Fin b) (AfE D) => w i j) '' (W : Set _))
      (isCompact_iUnion fun i => isCompact_iUnion fun j =>
        (hWc.image ((continuous_apply j).comp (continuous_apply i)) :
          IsCompact ((fun w : Matrix (Fin 1) (Fin b) (AfE D) => w i j) '' (W : Set _))))
    have hKc : IsCompact {y : Mx D 1 b | ∀ i j, y i j ∈ Ka} :=
      isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hKa
    refine HasCompactSupport.intro' hKc hKc.isClosed fun y hy => ?_
    by_contra hne
    change ¬ η₀ y = 0 at hne
    apply hy
    intro i j
    rw [hη] at hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have hw : (Matrix.of fun i j => finPart D (y i j)) ∈ W := by
      by_contra h
      exact h2 (if_neg h)
    refine hKaC _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, _, hw, rfl⟩⟩) fun ρ => ?_
    have hb : bump (rc y) ≠ 0 := fun h => h1 (by rw [h, Complex.ofReal_zero])
    have hmem : rc y ∈ Metric.ball (0 : D.what₂.Tau → Fin 1 → Fin b → ℂ) (max R 1 + 1) := by
      rw [← bump.support_eq]; exact hb
    rw [mem_ball_zero_iff] at hmem
    have h3 : ‖rc y ρ i j‖ ≤ ‖rc y‖ :=
      ((norm_le_pi_norm (rc y ρ i) j).trans (norm_le_pi_norm (rc y ρ) i)).trans (norm_le_pi_norm (rc y) ρ)
    exact h3.trans hmem.le
  ·
    intro y
    show η₀ y = if IntOff S y then η₀ (e • y) else 0
    by_cases hy : IntOff S y
    · rw [if_pos hy, hη, hη]
      have hr : rc (e • y) = rc y := by
        funext τ i j
        show θ τ (infPart D ((e • y) i j)) = θ τ (infPart D (y i j))
        rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, hθe τ, one_mul]
      have hw : (Matrix.of fun i j => finPart D ((e • y) i j)) = Matrix.of fun i j => ef * finPart D (y i j) := by
        funext i j
        rw [Matrix.of_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      have hiff := mem_U_iff (N := N) hef hS (w := Matrix.of fun i j => finPart D (y i j))
        (fun v hv i j => by rw [Matrix.of_apply, ← cv_eq]; exact hy v hv i j)
      rw [hr, hw]
      simp only [Matrix.of_apply] at hiff
      by_cases hm : (Matrix.of fun i j => finPart D (y i j)) ∈ W
      · rw [if_pos hm, if_pos (hiff.1 hm)]
      · rw [if_neg hm, if_neg (fun h => hm (hiff.2 h))]
    · rw [if_neg hy, hη, if_neg, mul_zero]
      intro hm
      exact hy fun v hv i j => by rw [cv_eq]; exact hm.1 v hv i j
  ·
    intro y
    show 0 ≤ (η₀ y).re ∧ (η₀ y).re ≤ 1 ∧ (η₀ y).im = 0
    rw [hη]
    split_ifs
    · rw [mul_one, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨bump.nonneg, bump.le_one, rfl⟩
    · simp
  ·
    intro x hx
    show η₀ (x.submatrix (fun _ => i) id) = 1
    rw [hη, if_pos, bump.one_of_mem_closedBall]
    · simp
    · exact Metric.closedBall_subset_closedBall (le_max_left _ _)
        (hR (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩))
    · refine ⟨fun v hv i' j => ?_, fun i' j => ?_⟩
      · rw [Matrix.of_apply, ← cv_eq]; exact hCi x hx v hv i j
      · exact hNC _ (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, x, hx, rfl⟩⟩)

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LRowTotal

open GlobalTheory.RegSch.IkSchwartz (AEf)

theorem finBump (D : D7) {a b : ℕ} {w₀ : Fin a → Fin b → AEf D} {B : Set (Fin a → Fin b → AEf D)} (hB : B ∈ 𝓝 w₀) :
    ∃ C : Set (Fin a → Fin b → AEf D), IsOpen C ∧ IsCompact C ∧ IsClosed C ∧ w₀ ∈ C ∧ C ⊆ B := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  let H : (Fin a → Fin b → AEf D) ≃ₜ (Fin a × Fin b × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) :=
    { toFun := fun w k => e0 (w k.1 k.2.1) k.2.2
      invFun := fun z i j => e0.symm fun l => z (i, j, l)
      left_inv := fun w => funext fun i => funext fun j => by simp
      right_inv := fun z => funext fun k => by simp
      continuous_toFun := continuous_pi fun k => (continuous_apply k.2.2).comp
        (e0.continuous.comp ((continuous_apply k.2.1).comp (continuous_apply k.1)))
      continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
        e0.symm.continuous.comp (continuous_pi fun l => continuous_apply (i, j, l)) }
  obtain ⟨C, hCo, hCc, hCl, hwC, hCB⟩ :=
    GlobalTheory.CompanionTheory.AdelicBump.exists_compact_open_nhds D.host.F (H.isOpenMap.image_mem_nhds hB)
  exact ⟨H ⁻¹' C, hCo.preimage H.continuous, H.isCompact_preimage.2 hCc, hCl.preimage H.continuous, hwC,
    fun w hw => H.injective.mem_set_image.1 (hCB hw)⟩

theorem bump1 {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (p : ℕ) (y₁ : Mx D 1 p) {N : Set (Mx D 1 p)}
    (hN : N ∈ 𝓝 y₁) : ∃ η ∈ schwartzA θ 1 p, Continuous η ∧ HasCompactSupport η ∧
      (∀ y, 0 ≤ (η y).re ∧ (η y).im = 0) ∧ (∀ y, y ∉ N → η y = 0) ∧ 0 < (η y₁).re := by
  obtain ⟨e, he⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ 1 p
  let E' := e.toHomeomorph
  have hE : ∀ x, E' x = e x := fun x => rfl
  have hN' : E'.symm ⁻¹' N ∈ 𝓝 (E' y₁) :=
    E'.symm.continuous.continuousAt.preimage_mem_nhds (by rw [E'.symm_apply_apply]; exact hN)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hN'
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hA
  obtain ⟨C, hCo, hCc, hCcl, hwC, hCB⟩ := finBump D hB
  have hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ) := hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (D.what₂.Tau → Fin 1 → Fin p → ℂ) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)
  have hf : ∀ y, f y = ((φ y : ℝ) : ℂ) := fun y => rfl
  let g : (Fin 1 → Fin p → AEf D) → ℂ := Set.indicator C fun _ => 1
  have hgl : IsLocallyConstant g := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ C
    · exact ⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by
        simp only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin p → AEf D) :=
    ⟨hgl, HasCompactSupport.intro' hCc hCcl fun x hx => Set.indicator_of_notMem hx _⟩
  have hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ) := fun w => by
    by_cases hw : w ∈ C <;> simp [g, hw]
  let η : Mx D 1 p → ℂ := fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
  have hη : ∀ x, η x = ((φ (E' x).1 * Set.indicator C (fun _ => (1 : ℝ)) (E' x).2 : ℝ) : ℂ) := fun x => by
    rw [Complex.ofReal_mul, ← hgval, ← hf, hE, he]
  have hnn : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hK : IsCompact (E' ⁻¹' (tsupport φ ×ˢ C)) := E'.isCompact_preimage.2 (hφc.prod hCc)
  have hKl : IsClosed (E' ⁻¹' (tsupport φ ×ˢ C)) := ((isClosed_tsupport _).prod hCcl).preimage E'.continuous
  have hout : ∀ x, x ∉ E' ⁻¹' (tsupport φ ×ˢ C) → η x = 0 := by
    intro x hx
    rw [hη]
    simp only [Set.mem_preimage, Set.mem_prod, not_and_or] at hx
    rcases hx with hx | hx
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp
  refine ⟨η, Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, HasCompactSupport.intro' hK hKl hout, fun y => ?_, fun y hy => ?_, ?_⟩
  · have : η = fun x => f (E' x).1 * g (E' x).2 := funext fun x => by rw [hE, he]
    rw [this]
    exact (f.continuous.comp (continuous_fst.comp E'.continuous)).mul (hgl.continuous.comp (continuous_snd.comp E'.continuous))
  · rw [hη, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩
  · by_contra hne
    apply hy
    have h1 : (E' y) ∈ tsupport φ ×ˢ C := by
      by_contra h; exact hne (hout y h)
    have h2 : E' y ∈ E'.symm ⁻¹' N := hAB ⟨hφs h1.1, hCB h1.2⟩
    simpa using h2
  · rw [hη, Complex.ofReal_re, Set.indicator_of_mem (show (E' y₁).2 ∈ C from hwC),
      show φ (E' y₁).1 = 1 from hφ1]
    norm_num

def rowsH (D : D7) (ρ p : ℕ) : Mx D ρ p ≃ₜ (Fin ρ → Mx D 1 p) where
  toFun y i := y.submatrix (fun _ => i) id
  invFun z := fun i j => z i 0 j
  left_inv y := rfl
  right_inv z := by
    funext i a j
    fin_cases a
    rfl
  continuous_toFun := continuous_pi fun i => continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp ((continuous_apply (0 : Fin 1)).comp (continuous_apply i))

theorem real_eq {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])

end PositivityTheory.Rg.Rsw.L.LRowTotal


open PositivityTheory.Rg.Rsw.L.LRowTotal in
theorem PositivityTheory.Rg.Rsw.L.rowTotal : IdemEx → BumpEx → RowTotal := by
  intro _ _ D θ hθ ρ p μ hμ u hu horth
  by_contra hne
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.mp hne
  have : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  set c := u y₀ with hc
  let U : Set (Mx D ρ p) := {y | 0 < (u y * conj c).re}
  have hUo : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp (hu.mul continuous_const))
  have hy₀U : y₀ ∈ U := by
    show 0 < (u y₀ * conj (u y₀)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 hy₀
  let R := rowsH D ρ p
  have hR : R.symm ⁻¹' U ∈ 𝓝 (R y₀) :=
    R.symm.continuous.continuousAt.preimage_mem_nhds (by rw [R.symm_apply_apply]; exact hUo.mem_nhds hy₀U)
  rw [nhds_pi, Filter.mem_pi] at hR
  obtain ⟨I, -, t, ht, hsub⟩ := hR
  choose η hηS hηc hηK hηpos hηN hηy using fun i => bump1 hθ p (R y₀ i) (ht i)
  have h0 := horth η fun i => ⟨hηS i, hηK i⟩
  have hRy : ∀ y i, y.submatrix (fun _ => i) id = R y i := fun y i => rfl
  let Pr : Mx D ρ p → ℝ := fun y => ∏ i, (η i (R y i)).re
  have hP : ∀ y, conj (∏ i, η i (y.submatrix (fun _ => i) id)) = (Pr y : ℂ) := by
    intro y
    have : (∏ i, η i (y.submatrix (fun _ => i) id)) = (Pr y : ℂ) := by
      simp only [Pr, Complex.ofReal_prod, hRy]
      exact Finset.prod_congr rfl fun i _ => real_eq (hηpos i _).2
    rw [this, Complex.conj_ofReal]
  let G : Mx D ρ p → ℂ := fun y => conj c * (u y * conj (∏ i, η i (y.submatrix (fun _ => i) id)))
  have hG0 : ∫ y, G y ∂μ = 0 := by
    simp only [G]
    rw [integral_const_mul, h0, mul_zero]
  have hGre : ∀ y, (G y).re = (u y * conj c).re * Pr y := by
    intro y
    simp only [G]
    rw [hP, show conj c * (u y * (Pr y : ℂ)) = (u y * conj c) * (Pr y : ℂ) by ring, Complex.re_mul_ofReal]
  have hGc : Continuous G := by
    refine continuous_const.mul (hu.mul ?_)
    refine Complex.continuous_conj.comp (continuous_finsetProd _ fun i _ => ?_)
    exact (hηc i).comp ((continuous_apply i).comp R.continuous)
  let K : Set (Mx D ρ p) := R ⁻¹' Set.univ.pi fun i => tsupport (η i)
  have hKc : IsCompact K := R.isCompact_preimage.2 (isCompact_univ_pi fun i => hηK i)
  have hKl : IsClosed K := (isClosed_set_pi fun i _ => isClosed_tsupport _).preimage R.continuous
  have hGK : HasCompactSupport G := by
    refine HasCompactSupport.intro' hKc hKl fun y hy => ?_
    simp only [K, Set.mem_preimage, Set.mem_univ_pi, not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    have : ∏ i, η i (y.submatrix (fun _ => i) id) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hRy]; exact image_eq_zero_of_notMem_tsupport hi)
    simp only [G, this, map_zero, mul_zero]
  have hGi : Integrable G μ := hGc.integrable_of_hasCompactSupport hGK
  have hpos : 0 < ∫ y, (G y).re ∂μ := by
    refine (Complex.continuous_re.comp hGc).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hGK.comp_left Complex.zero_re) (fun y => ?_) (x := y₀) ?_
    · show 0 ≤ (G y).re
      rw [hGre]
      by_cases hPr : Pr y = 0
      · rw [hPr, mul_zero]
      · have hall : ∀ i, R y i ∈ t i := by
          intro i
          by_contra hn
          apply hPr
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hηN i _ hn, Complex.zero_re])
        have hyU : y ∈ U := by
          have := hsub (fun i _ => hall i)
          simpa using this
        exact mul_nonneg hyU.le (Finset.prod_nonneg fun i _ => (hηpos i _).1)
    · show (G y₀).re ≠ 0
      rw [hGre]
      exact (mul_pos hy₀U (Finset.prod_pos fun i _ => hηy i)).ne'
  have := integral_re hGi
  simp only [RCLike.re_to_complex] at this
  rw [this, hG0, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end
end

section

namespace PositivityTheory.Rg.Rsw.L

theorem nullSing : IdemEx → NullSing := GlobalTheory.CompanionTheory.NullFr.nullSing_of_idemEx

end PositivityTheory.Rg.Rsw.L
end
