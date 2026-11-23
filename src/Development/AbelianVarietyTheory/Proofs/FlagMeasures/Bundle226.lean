module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle211
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle115
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle169
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle082
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle215
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.LiePos

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_mul_J : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem inG_conjTranspose {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) : Formalism.REAL.inG ε Xᴴ := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have hJ' : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← mul_assoc, hJ, one_mul]
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_conjTranspose]
  have e := congrArg (fun M => Formalism.REAL.Jm ε * M * Formalism.REAL.Jm ε) h
  simp only [mul_add, add_mul, mul_assoc, hJ, hJ', mul_one, mul_zero, zero_mul] at e
  rw [add_comm]
  exact e

theorem inG_sub {X Y : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) (k : Formalism.REAL.inG ε Y) :
    Formalism.REAL.inG ε (X - Y) := by
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_sub, sub_mul, mul_sub]
  rw [show Xᴴ * Formalism.REAL.Jm ε - Yᴴ * Formalism.REAL.Jm ε + (Formalism.REAL.Jm ε * X - Formalism.REAL.Jm ε * Y) =
      (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) - (Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y) by abel, h, k, sub_zero]

theorem comm_of_maxK {g : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) :
    uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp hg
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hU]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h1, one_mul]

theorem skew_of_comm {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X)
    (hc : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) : Xᴴ = -X := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have h' : Xᴴ * Formalism.REAL.Jm ε = -(X * Formalism.REAL.Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = -(X * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [h']
    _ = -X := by rw [neg_mul, mul_assoc, hJ, mul_one]

theorem exp_unitary {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Z))ᴴ * NormedSpace.exp ((t : ℂ) • Z) = 1 := by
  have hA : ((t : ℂ) • Z)ᴴ = -((t : ℂ) • Z) := by
    rw [conjTranspose_smul, hZ, smul_neg, Complex.star_def, Complex.conj_ofReal]
  have hc : Commute (-((t : ℂ) • Z)) ((t : ℂ) • Z) := (Commute.refl _).neg_left
  rw [← Matrix.exp_conjTranspose, hA, ← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]

theorem mem_span_of_subset {S S' : Set (Formalism.REAL.UJ ε)} {d d' : ℕ} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    {E' : Fin d' → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) (h' : IsCut ε S' E') (hS : S ⊆ S') (i : Fin d) :
    E i ∈ Submodule.span ℝ (Set.range E') := by
  obtain ⟨A', -, -, hA', hS'⟩ := h'
  have hT : E i ∈ A' := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε S d E h).2.1 A' (fun g hg => by
    have hg' : g ∈ S' := hS hg
    rw [hS'] at hg'
    exact hg') i
  exact (hA' _).1 ⟨hT, h.inG (Submodule.subset_span ⟨i, rfl⟩)⟩

theorem lieRel : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsCut ε (maxK ε ∩ flagM ε W) EL → LieRel EN EM EK EL := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL
  obtain ⟨hlow, hkeep⟩ := GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps n ε a j W hW
  obtain ⟨htr, hle, hone, -⟩ := GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag n ε a j W hW
  have hENlow : ∀ i, EN i ∈ lowers ε W := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dN EN hN).2.1 (lowers ε W) hlow
  have hEMkeep : ∀ k, EM k ∈ keeps ε W :=
    (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dM EM hM).2.1 (keeps ε W) (fun m hm => sub_mem (hkeep m hm).1 hone)
  have hEMstar : ∀ k, (EM k)ᴴ ∈ keeps ε W := by
    let T2 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      { carrier := {Y | Yᴴ ∈ keeps ε W}
        add_mem' := fun {A B} hA hB => by
          simp only [Set.mem_ofPred_eq, conjTranspose_add] at *
          exact add_mem hA hB
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, conjTranspose_zero]
          exact zero_mem _
        smul_mem' := fun c Y hY => by
          simp only [Set.mem_ofPred_eq] at *
          rw [conjTranspose_smul, star_trivial]
          exact Submodule.smul_mem _ c hY }
    exact (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dM EM hM).2.1 T2 (fun m hm => by
      change (uMat m - 1)ᴴ ∈ keeps ε W
      rw [conjTranspose_sub, conjTranspose_one]
      exact sub_mem (hkeep m hm).2 hone)
  let TC : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {Y | Y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Y}
      add_mem' := fun {A B} hA hB => by
        simp only [Set.mem_ofPred_eq] at *
        rw [add_mul, mul_add, hA, hB]
      zero_mem' := by simp
      smul_mem' := fun c Y hY => by
        simp only [Set.mem_ofPred_eq] at *
        rw [smul_mul_assoc, mul_smul_comm, hY] }
  have hEK : ∀ i, EK i ∈ TC := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dK EK hK).2.1 TC (fun g hg => by
    change (uMat g - 1) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (uMat g - 1)
    rw [sub_mul, mul_sub, one_mul, mul_one, comm_of_maxK hg])
  have hspan : Submodule.span ℝ (Set.range EK) ≤ TC :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hEK i)
  have hELK : ∀ i, EL i ∈ Submodule.span ℝ (Set.range EK) :=
    mem_span_of_subset hL hK Set.inter_subset_left
  refine ⟨fun i k => htr _ (hENlow i) _ (hEMstar k), fun i k => htr _ (hENlow i) _ (hEMkeep k),
    fun i k => htr _ (hENlow i) _ (hle (hENlow k)), mem_span_of_subset hL hM Set.inter_subset_right, hELK,
    fun i => skew_of_comm (hK.inG (hELK i)) (hspan (hELK i)), fun i => ?_⟩
  have hG : Formalism.REAL.inG ε (EN i) := hN.inG (Submodule.subset_span ⟨i, rfl⟩)
  have hY : Formalism.REAL.inG ε (EN i - (EN i)ᴴ) := inG_sub hG (inG_conjTranspose hG)
  have hskew : (EN i - (EN i)ᴴ)ᴴ = -(EN i - (EN i)ᴴ) := by
    rw [conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]
  refine (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dK EK hK).2.2 _ hY (fun t g hg => ?_)
  change (uMat g)ᴴ * uMat g = 1
  rw [hg]
  exact exp_unitary hskew t

end GlobalTheory.IwConst.LiePos
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwDelta

variable {n : ℕ}

theorem exists_cont_detOn (V : Submodule ℂ (Fin n → ℂ)) :
    ∃ D : Matrix (Fin n) (Fin n) ℂ → ℝ, Continuous D ∧
      ∀ X, (∀ y ∈ V, X *ᵥ y ∈ V) → detOn X V = D X := by
  obtain ⟨U, hVU⟩ := Submodule.exists_isCompl V
  let p := Submodule.projectionOnto V U hVU
  let b := Module.finBasis ℂ V
  refine ⟨fun X => ‖(Matrix.of fun i k => b.repr (p (X *ᵥ (b k : Fin n → ℂ))) i).det‖, ?_, ?_⟩
  · apply Continuous.norm
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i k
    have hlin : Continuous fun y : Fin n → ℂ => b.repr (p y) i :=
      ((b.coord i).comp p).continuous_of_finiteDimensional
    exact hlin.comp (continuous_id.matrix_mulVec continuous_const)
  · intro X hX
    have h' : ∀ y ∈ V, Matrix.toLin' X y ∈ V := fun y hy => by
      simpa [Matrix.toLin'_apply] using hX y hy
    have e : ∀ k, p (X *ᵥ (b k : Fin n → ℂ)) = (Matrix.toLin' X).restrict h' (b k) := by
      intro k
      have hp : p (X *ᵥ (b k : Fin n → ℂ)) = ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩ :=
        Submodule.projectionOnto_apply_left hVU ⟨X *ᵥ (b k : Fin n → ℂ), hX _ (b k).2⟩
      rw [hp]
      apply Subtype.ext
      simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
    rw [detOn, dite_eq_left h', ← LinearMap.det_toMatrix b]
    congr 2
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.of_apply, e k]

theorem detOn_one (V : Submodule ℂ (Fin n → ℂ)) : detOn (1 : Matrix (Fin n) (Fin n) ℂ) V = 1 := by
  have h' : ∀ y ∈ V, Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ) y ∈ V := fun y hy => by simpa using hy
  rw [detOn, dite_eq_left h']
  have hid : (Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ)).restrict h' = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by simp [LinearMap.restrict_apply])
  rw [hid, LinearMap.det_id, norm_one]

private theorem detOn_le_one_of_unitary_of_invariant (U : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ))
    (hU : Uᴴ * U = 1) (hV : ∀ y ∈ V, U *ᵥ y ∈ V) : detOn U V ≤ 1 := by
  obtain ⟨D, hDc, hD⟩ := exists_cont_detOn V
  have hKc : IsCompact {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} := by
    have hcl : IsClosed {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * X = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
        Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin n) (Fin n) ℂ)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hbox.of_isClosed_subset hcl ?_
    intro X hX
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i k
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 hX) i k
  have hUg : U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hU
  have hpow : ∀ k : ℕ, (∀ y ∈ V, U ^ k *ᵥ y ∈ V) ∧ detOn (U ^ k) V = detOn U V ^ k := by
    intro k
    induction k with
    | zero => exact ⟨fun y hy => by simpa using hy, by simpa using detOn_one V⟩
    | succ k ih =>
      have hs : ∀ y ∈ V, U ^ (k + 1) *ᵥ y ∈ V := fun y hy => by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih.1 _ (hV y hy)
      refine ⟨hs, ?_⟩
      rw [pow_succ, GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ V ih.1 hV, ih.2, pow_succ]
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hDc.continuousOn
  by_contra hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.mp hlt)
  have hmem : (U ^ k)ᴴ * U ^ k = 1 := Matrix.mem_unitaryGroup_iff'.1 (pow_mem hUg k)
  have hb := hC (U ^ k) hmem
  rw [← hD _ (hpow k).1, (hpow k).2, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (GlobalTheory.FlagMeas.SizeMove.detOn_nonneg U V) k)] at hb
  linarith

theorem detOn_le_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) ≤ 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  exact detOn_le_one_of_unitary_of_invariant _ _ hl.1 (fun y hy => (hl2 i y hy).1)

theorem detOn_eq_one {ε : Fin n → Bool} {a : ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    {l : Formalism.REAL.UJ ε} (hl : l ∈ maxK ε ∩ flagM ε W) (i : Fin (a + 1)) : detOn (uMat l) (W i) = 1 := by
  have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
  have hU : (uMat l)ᴴ * uMat l = 1 := hl.1
  have hU' : (uMat l)ᴴᴴ * (uMat l)ᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have h1 := detOn_le_one hl i
  have h2 := detOn_le_one_of_unitary_of_invariant _ (W i) hU' (fun y hy => (hl2 i y hy).2)
  have hprod : detOn ((uMat l)ᴴ) (W i) * detOn (uMat l) (W i) = 1 := by
    rw [← GlobalTheory.FlagMeas.SizeMove.detOn_mul _ _ _ (fun y hy => (hl2 i y hy).2) (fun y hy => (hl2 i y hy).1), hU,
      detOn_one]
  have h3 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg (uMat l) (W i)
  have h4 := GlobalTheory.FlagMeas.SizeMove.detOn_nonneg ((uMat l)ᴴ) (W i)
  exact le_antisymm h1 (by nlinarith)

theorem measurable_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Measurable fun τ : Fin a → ℝ => layerProd n 1 j τ id := by
  unfold layerProd
  fun_prop

theorem continuousAt_layerProd {a : ℕ} (j : Fin a → ℕ) :
    Filter.Tendsto (fun τ : Fin a → ℝ => layerProd n 1 j τ id) (nhds 1) (nhds 1) := by
  have hc : ContinuousAt (fun τ : Fin a → ℝ => layerProd n 1 j τ id) 1 := by
    unfold layerProd
    fun_prop (disch := simp)
  have h1 : layerProd n 1 j (1 : Fin a → ℝ) id = 1 := by simp [layerProd]
  simpa [h1] using hc.tendsto

open scoped Matrix.Norms.Frobenius in
theorem exists_ball {s : Set (Matrix (Fin n) (Fin n) ℂ)} (hs : s ∈ nhds 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ X, nrm (X - 1) < t → X ∈ s := by
  obtain ⟨t, ht, hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨t, ht, fun X hX => hsub ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, ← nrm_eq]
  exact hX

theorem dlt_props : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), Measurable (dlt (ε := ε) j W) ∧ (∀ l ∈ maxK ε ∩ flagM ε W, ∀ m ∈ flagM ε W, dlt j W (m * l) = dlt j W m) ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ m ∈ flagM ε W, nrm (uMat m - 1) < t → dlt j W m ≤ ENNReal.ofReal (1 + η) ∧ 1 ≤ ENNReal.ofReal (1 + η) * dlt j W m := by
  intro n ε a j W
  refine ⟨?_, ?_, ?_⟩
  · unfold dlt
    exact ENNReal.measurable_ofReal.comp ((measurable_layerProd j).comp
      (Measurable.of_eval fun i => measurable_locSize_uMat n ε a j W i))
  · intro l hl m hm
    have hl2 : ∀ i, ∀ y ∈ W i, uMat l *ᵥ y ∈ W i ∧ (uMat l)ᴴ *ᵥ y ∈ W i := hl.2
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hmul : uMat (m * l) = uMat m * uMat l := rfl
    have hloc : locSize j W (uMat (m * l)) = locSize j W (uMat m) := by
      funext i
      simp only [locSize]
      rw [hmul,
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.succ) (fun y hy => (hm2 i.succ y hy).1)
          (fun y hy => (hl2 i.succ y hy).1),
        GlobalTheory.FlagMeas.SizeMove.detOn_mul (uMat m) (uMat l) (W i.castSucc) (fun y hy => (hm2 i.castSucc y hy).1)
          (fun y hy => (hl2 i.castSucc y hy).1),
        detOn_eq_one hl i.succ, detOn_eq_one hl i.castSucc, mul_one, mul_one]
    unfold dlt
    rw [hloc]
  · intro η hη
    choose D hDc hD using fun i : Fin (a + 1) => exists_cont_detOn (W i)
    have hD1 : ∀ i, D i 1 = 1 := fun i => by
      rw [← hD i 1 (fun y hy => by simpa using hy), detOn_one]
    set G : Matrix (Fin n) (Fin n) ℂ → Fin a → ℝ :=
      fun X i => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i) with hGdef
    have hG : Filter.Tendsto G (nhds 1) (nhds 1) := by
      rw [tendsto_pi_nhds]
      intro i
      have hc : ContinuousAt (fun X => (D i.succ X / D i.castSucc X) ^ (-(1 : ℝ) / j i)) 1 :=
        ((hDc _).continuousAt.div (hDc _).continuousAt (by simp [hD1])).rpow_const
          (Or.inl (by simp [hD1]))
      have ht := hc.tendsto
      simp only [hD1, div_one, Real.one_rpow] at ht
      exact ht
    have hF := (continuousAt_layerProd (n := n) j).comp hG
    have hpos : 0 < 1 + η := by linarith
    have hU : Set.Ioo (1 / (1 + η)) (1 + η) ∈ nhds (1 : ℝ) :=
      Ioo_mem_nhds ((div_lt_one hpos).2 (by linarith)) (by linarith)
    obtain ⟨t, ht, hball⟩ := exists_ball (Filter.tendsto_def.1 hF _ hU)
    refine ⟨t, ht, fun m hm hmt => ?_⟩
    have hm2 : ∀ i, ∀ y ∈ W i, uMat m *ᵥ y ∈ W i ∧ (uMat m)ᴴ *ᵥ y ∈ W i := hm
    have hin := hball _ hmt
    have hGm : G (uMat m) = locSize j W (uMat m) := by
      funext i
      simp only [hGdef, locSize]
      rw [hD i.succ _ (fun y hy => (hm2 i.succ y hy).1), hD i.castSucc _ (fun y hy => (hm2 i.castSucc y hy).1)]
    simp only [Set.mem_preimage, Function.comp_apply, hGm, Set.mem_Ioo] at hin
    obtain ⟨hlo, hhi⟩ := hin
    unfold dlt
    refine ⟨ENNReal.ofReal_le_ofReal hhi.le, ?_⟩
    rw [← ENNReal.ofReal_mul hpos.le, ENNReal.one_le_ofReal]
    rw [div_lt_iff₀ hpos] at hlo
    linarith [mul_comm (layerProd n 1 j (locSize j W (uMat m)) id) (1 + η)]

end GlobalTheory.IwDelta
end
end

section

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.PsiPolarProof

variable {n : ℕ}

lemma exp_posDef_of_herm {X : Matrix (Fin n) (Fin n) ℂ} (h : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℝ) • X)ᴴ = (1 / 2 : ℝ) • X := by
    rw [Matrix.conjTranspose_smul, h]; simp
  have e : X = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X := by rw [← add_smul]; norm_num
  have e2 : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℝ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℝ) • X) := by
    rw [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e]
  rw [e2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_exp _))

lemma mem_KC_of_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

lemma mul_mem_K {ε : Fin n → Bool} {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hk' : k' ∈ Kset ε) : k * k' ∈ Kset ε :=
  ⟨mul_mem hk.1 hk'.1, by rw [Matrix.mul_assoc, hk'.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]⟩

lemma star_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have := congrArg Matrix.conjTranspose hk.2
  simpa [Matrix.conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem psiPolar_of (hB : PsBasic) (hE : PsEquiv) : PsiPolar := by
  intro n ε lam W _ _ τ w hl hτ
  refine ⟨fun k hk X hX => Psi_unitary_mul ε lam τ w hk.1
    (exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)), ?_, ?_⟩
  · have h := Psi_unitary_mul ε lam τ w (one_mem _) (Matrix.PosDef.one (n := Fin n) (R := ℂ))
    rw [Matrix.mul_one] at h
    rw [h, (hB n ε lam W τ w hl hτ).2.2.2, hτ.2.1.1]
    rfl
  · intro k₁ h₁ k₂ h₂ g hg
    obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
    have hp := exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)
    set p := NormedSpace.exp X
    have hs : k₂ * k₂ᴴ = 1 := Unitary.mul_star_self_of_mem h₂.1
    have hc := mem_KC_of_mem_K (star_mem_K h₂)
    have hq : (k₂ᴴ * p * k₂).PosDef :=
      hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (mem_KC_of_mem_K h₂).1)
    have e : k₁ * (k * p) * k₂ = (k₁ * k * k₂) * (k₂ᴴ * p * k₂) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂ k₂ᴴ, hs, Matrix.one_mul]
    have hk3 := mul_mem_K (mul_mem_K h₁ hk) h₂
    have he := hE n ε lam W τ w hl hτ p k₂ᴴ hp hc
    rw [Matrix.conjTranspose_conjTranspose] at he
    rw [e, Psi_unitary_mul ε lam τ w hk3.1 hq, Psi_unitary_mul ε lam τ w hk.1 hp, he,
      ← ContinuousLinearMap.comp_assoc]
    have hm : (τ (k₁ * k * k₂)).comp (τ k₂ᴴ) = (τ k₁).comp (τ k) := by
      have a := hτ.2.1.2 _ (mem_KC_of_mem_K hk3) _ hc
      have b := hτ.2.1.2 _ (mem_KC_of_mem_K h₁) _ (mem_KC_of_mem_K hk)
      rw [Matrix.mul_assoc, hs, Matrix.mul_one] at a
      exact a.symm.trans b
    rw [hm]
    rfl

end GlobalTheory.Dec.PsiPolarProof

theorem GlobalTheory.Dec.psiPolar : GlobalTheory.Dec.PsiPolar :=
  GlobalTheory.Dec.PsiPolarProof.psiPolar_of GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one GlobalTheory.T.psi_complexifiedK_equivariance
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WtPos

theorem finrank_loc {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem wt_pos : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d0 d : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → (∃ t, LocNG.IsTermOver P d t) → 0 < LocNG.Datum.wt d0 d := by
  intro D Z p P hR d0 d ⟨t0, ht0⟩ ⟨t, ht⟩
  have hOK := (Z.agree p).1
  haveI := hOK.loc
  haveI := hOK.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord (Z.M p) hOK (locH Z p) D.R.rS D.R.k P (finrank_loc p) hR
  have h0 := ((GlobalTheory.HL.CoordTermWt.terms_correspond (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).1 d0 t0 ht0).1
  have h1 := ((GlobalTheory.HL.CoordTermWt.terms_correspond (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).1 d t ht).1
  obtain ⟨a0, b0⟩ := (GlobalTheory.HL.Frames.stab_commensurable_invVol_smul (Z.M p).L D.R.rS D.R.k S).2 _ _ h0
  obtain ⟨a1, b1⟩ := (GlobalTheory.HL.Frames.stab_commensurable_invVol_smul (Z.M p).L D.R.rS D.R.k S).2 _ _ h1
  rw [(GlobalTheory.HL.CoordDatum.transport (Z.M p) hOK (locH Z p) D.R.rS D.R.k P S c).2.2.2.2 d0 d]
  have e1 := Subgroup.relIndex_ne_zero_trans b1 a0
  have e2 := Subgroup.relIndex_ne_zero_trans b0 a1
  unfold GlobalTheory.HL.invVol
  positivity

end GlobalTheory.WtPos
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_adelicLatticeClosure_iff_swap_mem_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → Af F ⊗[F] E), y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  first | exact @GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf | exact GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf | (intros; apply GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf <;> assumption)
end
