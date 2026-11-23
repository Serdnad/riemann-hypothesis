module

import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle030
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootsLevelPointsSameVacuumTranslates
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolution
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPlaceKernelHolomorphicWeightRowHighest
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledIsotropicStructureGeneral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MapConjInv
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.SW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

noncomputable def spOf (γ : GL (Fin r) E) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℚ :=
  Matrix.of fun p q => crd X bas (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
    ((bas (Pi.single p.swap 1) : X.Λ) : Fin r → E)) q.swap


omit [NumberField E] [IsCMField E] in
theorem gl_mulVec_inv_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

variable {X bas}

theorem IsUn.lact_mem {γ : GL (Fin r) E} (hγ : IsUn X γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  apply GlobalTheory.Dict.Extend.lact_mem <;> assumption

theorem spOf_mem (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ) :
    spOf X bas γ ∈ Matrix.symplecticGroup (Fin g) ℚ := by

  have hinv : ∀ u v : Fin r → E, EF X (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF X u v := by
    intro u v
    have h := hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
    rw [gl_mulVec_inv_mulVec, gl_mulVec_inv_mulVec] at h
    rw [EF_def, EF_def, h]

  have hrow : ∀ p p' : Fin g ⊕ Fin g,
      ∑ i, (spOf X bas γ p (Sum.inr i) * spOf X bas γ p' (Sum.inl i) -
        spOf X bas γ p (Sum.inl i) * spOf X bas γ p' (Sum.inr i)) =
      ((omegaStd (Pi.single p.swap 1 : Fin g ⊕ Fin g → ℤ) (Pi.single p'.swap 1) : ℤ) : ℚ) := by
    intro p p'
    have h := hinv (bas (Pi.single p.swap 1)) (bas (Pi.single p'.swap 1))
    rw [EF_crd hs, hs] at h
    simp only [spOf, Matrix.of_apply, Sum.swap_inl, Sum.swap_inr]
    linarith
  rw [SymplecticGroup.mem_iff]
  ext p p'
  have hJl : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inl j) = spOf X bas γ p (Sum.inr j) := by
    intro j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]
  have hJr : ∀ j, (spOf X bas γ * Matrix.J (Fin g) ℚ) p (Sum.inr j) = -spOf X bas γ p (Sum.inl j) := by
    intro j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J, Matrix.one_apply]
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hJl, hJr, Matrix.transpose_apply, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg,
    ← Finset.sum_sub_distrib]
  rw [hrow]
  rcases p with i | i <;> rcases p' with j | j <;>
    simp [omegaStd, Pi.single_apply, Matrix.J, Matrix.one_apply, eq_comm]

theorem hMat_mul_perMat_lact (hs : IsSympl X bas) {γ : GL (Fin r) E} (hγ : IsUn X γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : Fin g → Fin g ⊕ Fin g) :
    hMat X bas idx x * perMat X bas idx s (lact γ x) =
      (qm (Matrix.of fun k j => spOf X bas γ (s k).swap (Sum.inl j)) * tauMat X bas idx x +
        qm (Matrix.of fun k j => spOf X bas γ (s k).swap (Sum.inr j)))ᵀ := by
  have hsym := tauMat_isSymm (idx := idx) hs hx
  ext i k
  have hcol : (fun l => perMat X bas idx s (lact γ x) l k) =
      per X x (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)) ∘ idx := by
    funext l
    rw [perMat_apply, Function.comp_apply,
      ← per_lact x hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((bas (Pi.single (s k) 1) : X.Λ) : Fin r → E)), gl_mulVec_inv_mulVec]
  have hlhs : (hMat X bas idx x * perMat X bas idx s (lact γ x)) i k =
      (hMat X bas idx x *ᵥ fun l => perMat X bas idx s (lact γ x) l k) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hlhs, hcol, hMat_mulVec_per_crd (idx := idx) hs hx]
  simp only [spOf, qm, qv, Matrix.of_apply, Matrix.transpose_apply, Matrix.add_apply, Pi.add_apply,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Sum.swap_swap, Sum.swap_inl,
    Sum.swap_inr]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym.apply]
  ring

theorem periods_lact_symplectic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∃ σ ∈ Matrix.symplecticGroup (Fin g) ℚ, ∀ x ∈ X.dom, lact γ x ∈ X.dom ∧ tauMat X bas idx x ∈ Siegel (Fin g) ∧ tauMat X bas idx (lact γ x) = spAct σ (tauMat X bas idx x) ∧ hMat X bas idx (lact γ x) = ((spDen σ (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
  intro E _ _ _ r X g bas idx n hs _ γ hγ
  refine ⟨spOf X bas γ, spOf_mem hs hγ, fun x hx => ?_⟩
  have hx' := IsUn.lact_mem hγ hx
  have hD : hMat X bas idx x * perMat X bas idx Sum.inl (lact γ x) =
      (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ :=
    hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inl
  have hN : hMat X bas idx x * perMat X bas idx Sum.inr (lact γ x) =
      (qm (spOf X bas γ).toBlocks₁₁ * tauMat X bas idx x + qm (spOf X bas γ).toBlocks₁₂)ᵀ :=
    hMat_mul_perMat_lact (idx := idx) hs hγ hx Sum.inr
  have hH := isUnit_det_hMat (idx := idx) hs hx
  have hP := isUnit_det_perMat (idx := idx) hs hx'
  have hPeq : perMat X bas idx Sum.inl (lact γ x) =
      (hMat X bas idx x)⁻¹ * (spDen (spOf X bas γ) (tauMat X bas idx x))ᵀ := by
    rw [← hD, Matrix.nonsing_inv_mul_cancel_left _ _ hH]
  have hh : hMat X bas idx (lact γ x) =
      ((spDen (spOf X bas γ) (tauMat X bas idx x))⁻¹)ᵀ * hMat X bas idx x := by
    change (perMat X bas idx Sum.inl (lact γ x))⁻¹ = _
    rw [hPeq, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hH, Matrix.transpose_nonsing_inv]
  refine ⟨hx', ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩, ?_, hh⟩
  have ht : tauMat X bas idx (lact γ x) = (spAct (spOf X bas γ) (tauMat X bas idx x))ᵀ := by
    change hMat X bas idx (lact γ x) * perMat X bas idx Sum.inr (lact γ x) = _
    rw [hh, Matrix.mul_assoc, hN, spAct, Matrix.transpose_mul]
  have hsym := tauMat_isSymm (idx := idx) hs hx'
  rw [← hsym, ht, Matrix.transpose_transpose]

end GlobalTheory.SW
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.roots_levelPoints_same_vacuum_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (n : ℕ), IsSympl X bas → Even n → ∀ L : Lt E r, SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n l.M, ∀ Λ' ∈ Vset E n l.M, Moves h Λ Λ' → ∀ N N' : ℕ, (⟨Λ⟩ : GenLat E n).LevOK N l.M → (⟨Λ'⟩ : GenLat E n).LevOK N' l.M → ∀ Y Y' : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → IsRoots l L mk N' Y' → (∃ e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l), ∀ q, LevMoves h q (e q)) ∧ ∀ q q', LevMoves h q q' → ∀ u : TF n g, IsVac X bas (H.w0 : E) (tens Λ' L) u → heisG X bas (Y' q') u = heisG X bas (h * Y q) u := by
  first | exact @GlobalTheory.Dict.RootsMove.roots_move | exact GlobalTheory.Dict.RootsMove.roots_move | (intros; apply GlobalTheory.Dict.RootsMove.roots_move <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private theorem det_sgnM_eq_prod_sgn {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : (sgnM X).det = ∏ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  simp [sgnM, Matrix.det_diagonal]

theorem normSq_det_of_isONFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {X : Data E r} {x : Frame X.Ψ r} (hx : IsONFr X x) (τ : X.Ψ) :
    normSq (mat x τ).det = ‖(X.Gm.map τ.1).det‖⁻¹ := by

  have hdet := congrArg Matrix.det (hx τ)
  rw [GlobalTheory.SW.Slab.det_gram, det_sgnM_eq_prod_sgn X] at hdet
  have hG : (X.Gm.map τ.1).det = τ.1 X.Gm.det := (RingHom.map_det τ.1 X.Gm).symm
  have hn := congrArg norm hdet
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_prod] at hn
  simp only [GlobalTheory.SW.Slab.norm_sgn, Finset.prod_const_one] at hn
  rw [hG, Complex.normSq_eq_norm_sq]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hn]
  ring

theorem kZero_onFr_const_entire : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∃ κ : ℝ, 0 < κ ∧ ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ kZero X idx x x (0 : Fin n → Fin g → ℂ) 0 = κ) ∧ ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, Differentiable ℂ (fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) => kZero X idx x₁ x₂ p.1 p.2) := by
  intro E _ _ _ r X g q0 hr bas idx n _ _
  refine ⟨⟨∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖⁻¹ ^ (n / 2), ?_, fun x hx => ⟨?_, ?_⟩⟩, ?_⟩
  ·
    refine Finset.prod_pos fun τ _ => pow_pos (inv_pos.mpr (norm_pos_iff.mpr ?_)) _
    exact GlobalTheory.SW.KernSym.det_map_Gm X τ
  ·
    obtain ⟨δ₀, hδ₀, hs⟩ := GlobalTheory.SW.thin_slab E r X
    obtain ⟨-, hsub, hon, -⟩ := hs δ₀ hδ₀ le_rfl
    exact hsub (hon x hx)
  ·

    rw [GlobalTheory.SW.KernSym.kZero_ortho idx hx]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [normSq_det_of_isONFr hx τ]
  ·
    intro x₁ _ x₂ _ p
    exact (GlobalTheory.SW.KernSym.analyticAt_kZero X idx x₁ x₂ p).differentiableAt

end GlobalTheory.Ker
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.AtRecord

theorem isRelTraceOneIdempotentModTwo_hostElement {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    IdemTwo (H.w0 : E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 : (H.w0 : E) + cc (H.w0 : E) = 1 := by
    have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
    rw [map_add (f := _), map_one] at this
    exact (congrArg _ (H.bar_eq _).symm).trans this
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have h3 : (H.rt : E) ^ 2 = -(16 * k + 7) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast, hk] at this
    exact this.trans (by push_cast; rfl)
  refine ⟨((2 * k + 1 : ℕ) : E), isIntegral_natCast _, ?_⟩
  rw [eq_sub_of_add_eq' h1]
  push_cast
  linear_combination (-(1 / 4 : E)) * h3 - (1 / 4 : E) * (2 * (H.w0 : E) - 1 + (H.rt : E)) * h2

end GlobalTheory.Ker.AtRecord
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.det_hermitianFormAtFramePeriodCoords_of_unitFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, IsUnitFr X x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ z w, hermForm Hm z w = hx X bas idx x z w) → Hm.det = ((∏ τ : X.Ψ, X.c τ ^ r : ℝ) : ℂ) := by
  first | exact @GlobalTheory.Dict.det_hx_of_isUnitFr | exact GlobalTheory.Dict.det_hx_of_isUnitFr | (intros; apply GlobalTheory.Dict.det_hx_of_isUnitFr <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.invariant_polyDeriv_kills_doubled_heat_solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), r ≤ n → InvFam P → ∀ D : CM X.Ψ r r → CM X.Ψ n r → CM X.Ψ n r → ℂ, IsHeat X.Ψ D → (∀ Z ∈ Hn X.Ψ r, D Z 0 0 = 0) → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, biDeriv X hr idx P (fun z₁ w => kZero X idx x₁ x₂ z₁ w * D (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = 0 := by
  first | exact @GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | exact GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | (intros; apply GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.realPlaceKernel_holomorphic_weight_rowHighest : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → ∀ x₂ ∈ X.dom, DifferentiableOn ℂ (fun x₁ => kern X hr idx P x₁ x₂) X.dom ∧ ∀ x₁ ∈ X.dom, ∀ b ∈ Bor X.Ψ r, kern X hr idx P (rmul x₁ b) x₂ = bchar (wtOf X hr c c' n) b * kern X hr idx P x₁ x₂ := by
  first | exact @GlobalTheory.KernHol.kern_hol_weight | exact GlobalTheory.KernHol.kern_hol_weight | (intros; apply GlobalTheory.KernHol.kern_hol_weight <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblLag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in
theorem mem_botSpan (g : M2 E r) (v : Fin r ⊕ Fin r → E) :
    v ∈ botSpan g ↔ ∃ c : Fin r → E, Sum.elim 0 c ᵥ* g = v := by
  rw [botSpan, Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => Eq.congr_left ?_
  ext j
  simp [vecMul, dotProduct, Finset.sum_apply]

theorem pair_vecMul (A B : M2 E r) (u v : Fin r ⊕ Fin r → E) :
    ((u ᵥ* A) ᵥ* B) ⬝ᵥ (fun j => cc ((v ᵥ* A) j)) = (u ᵥ* (A * B * ccT A)) ⬝ᵥ fun j => cc (v j) := by
  have e : (fun j => cc ((v ᵥ* A) j)) = ccT A *ᵥ fun j => cc (v j) := by
    ext j

    simp only [vecMul, mulVec, dotProduct, cc, ccT, map_sum, map_mul, transpose_apply, map_apply,
    mul_comm]
  rw [e, dotProduct_mulVec, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc]

theorem iso_of_mem {g : M2 E r} (hg : g ∈ UU E r) {u v : Fin r ⊕ Fin r → E}
    (hu : u ∈ botSpan g) (hv : v ∈ botSpan g) :
    (u ᵥ* Matrix.J (Fin r) E) ⬝ᵥ (fun j => cc (v j)) = 0 := by
  obtain ⟨c, rfl⟩ := (mem_botSpan _ _).1 hu
  obtain ⟨d, rfl⟩ := (mem_botSpan _ _).1 hv
  have h : ccT (ccT g) * Matrix.J (Fin r) E * ccT g = Matrix.J (Fin r) E :=
    (HAct.group_part hg).2.2.1
  rw [HAct.ccT_ccT] at h
  rw [pair_vecMul, h, Matrix.J, vecMul_fromBlocks]
  simp [dotProduct, cc]

theorem finrank_botSpan {g : M2 E r} (hg : g ∈ UU E r) : Module.finrank E (botSpan g) = r := by
  have h : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (HAct.group_part hg).1
  have hl := (Matrix.linearIndependent_rows_iff_isUnit.2 h).comp _
    (Sum.inr_injective (α := Fin r) (β := Fin r))
  have := finrank_span_eq_card hl
  rw [Fintype.card_fin] at this
  exact this

variable (X : Data E r)

theorem isUnit_dblT : IsUnit (dblT X) :=
  IsUnit.of_mul_eq_one_right _ (DblPair.dblT_left X)

theorem pair_dblT (x y x' y' : Fin r → E) :
    ((Sum.elim x y ᵥ* dblT X) ᵥ* Matrix.J (Fin r) E) ⬝ᵥ (fun j => cc ((Sum.elim x' y' ᵥ* dblT X) j)) =
      X.κ0 / 2 * (herm X.Gm x x' - herm X.Gm y y') := by
  rw [pair_vecMul, DblPair.dblT_form, vecMul_fromBlocks]
  have e : ∀ x y : Fin r → E, herm X.Gm x y = ∑ b, (x ᵥ* X.Gm) b * cc (y b) := fun x y => by
    rw [herm, Finset.sum_comm]
    simp only [vecMul, dotProduct, Finset.sum_mul]
  simp [dotProduct, e, vecMul_neg, vecMul_smul, mul_add, Finset.mul_sum, mul_assoc, sub_eq_add_neg]

theorem mem_iota (γ : GL (Fin r) E) (x y : Fin r → E) :
    Sum.elim x y ᵥ* dblT X ∈ botSpan (iota X 1 γ) ↔ y = (γ⁻¹).1 *ᵥ x := by
  have hinj : Function.Injective fun v => v ᵥ* dblT X :=
    Matrix.vecMul_injective_iff_isUnit.2 (isUnit_dblT X)
  have hk : (2 * (X.κ0 / 4)) ≠ 0 := by simp [DblPair.kappa_ne X]
  have key : ∀ c : Fin r → E, Sum.elim 0 c ᵥ* iota X 1 γ =
      Sum.elim (c ᵥ* ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹))
        ((γ⁻¹).1 *ᵥ (c ᵥ* ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹))) ᵥ* dblT X := fun c => by
    rw [iota, Matrix.inv_eq_left_inv (DblPair.dblT_left X), ← vecMul_vecMul, ← vecMul_vecMul,
      vecMul_fromBlocks, vecMul_fromBlocks]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_vecMul, vecMul_zero, zero_add, add_zero,
      inv_one, Units.val_one, transpose_one, vecMul_one, vecMul_transpose]
  rw [mem_botSpan]
  constructor
  · rintro ⟨c, hc⟩
    rw [key] at hc
    have h := hinj hc
    have h1 := congrArg (· ∘ Sum.inl) h
    have h2 := congrArg (· ∘ Sum.inr) h
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h1 h2
    rw [← h2, h1]
  · rintro rfl
    refine ⟨x ᵥ* ((2 * (X.κ0 / 4)) • X.Gm), ?_⟩
    rw [key, vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hk,
      mul_nonsing_inv _ (Ne.isUnit X.Gm_det), one_smul, vecMul_one]

noncomputable def coord : ((Fin r → E) × (Fin r → E)) ≃ₗ[E] (Fin r ⊕ Fin r → E) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r) E E).symm.trans
    (LinearEquiv.ofBijective (dblT X).vecMulLinear
      ⟨Matrix.vecMul_injective_iff_isUnit.2 (isUnit_dblT X),
        Matrix.vecMul_surjective_iff_isUnit.2 (isUnit_dblT X)⟩)

theorem coord_apply (p : (Fin r → E) × (Fin r → E)) :
    coord X p = Sum.elim p.1 p.2 ᵥ* dblT X := rfl

end GlobalTheory.SW.DblLag


open GlobalTheory.SW.DblLag in
theorem GlobalTheory.SW.lag_graph_or_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ γ' : GL (Fin r) E, IsUn X γ → IsUn X γ' → botSpan (iota X 1 γ) = botSpan (iota X 1 γ') → γ = γ') ∧ ∀ U : Lag E r, (∃ γ : GL (Fin r) E, IsUn X γ ∧ botSpan (iota X 1 γ) = U.1) ∨ ∃ ξ : Fin r → E, ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0 ∧ Sum.elim ξ 0 ᵥ* dblT X ∈ U.1 := by
  intro E _ _ _ r X
  refine ⟨fun γ γ' _ _ h => ?_, ?_⟩
  · refine inv_injective (Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_)))
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mem_iota X, ← h, mem_iota]
  rintro ⟨U, g, hg, rfl⟩
  set I := (botSpan g).comap (coord X).toLinearMap with hI
  have hm : ∀ p, p ∈ I ↔ Sum.elim p.1 p.2 ᵥ* dblT X ∈ botSpan g := fun p => Iff.rfl
  have hiso : ∀ p ∈ I, ∀ q ∈ I, herm X.Gm p.1 q.1 - herm X.Gm p.2 q.2 = 0 := fun p hp q hq => by
    have := iso_of_mem hg ((hm p).1 hp) ((hm q).1 hq)
    rw [pair_dblT] at this
    exact (mul_eq_zero.1 this).resolve_left (by simp [DblPair.kappa_ne X])
  have hd : Module.finrank E I = r := by
    rw [hI, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, finrank_botSpan hg]
  obtain ⟨a1, -, -, -, -, -, a2, -⟩ :=
    (doubled_isotropic_structure X.Gm X.Gm_herm X.Gm_det).1 I hiso hd
  by_cases h0 : DoubledSpace.left I = ⊥
  · obtain ⟨δ, ⟨d1, d2⟩, -⟩ := a2.1 h0
    refine Or.inl ⟨δ⁻¹, fun x y => ?_, ?_⟩
    · rw [← d1, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
    · ext v
      obtain ⟨⟨x, y⟩, rfl⟩ := (coord X).surjective v
      rw [coord_apply, mem_iota, inv_inv, ← d2, hm]
  · obtain ⟨ξ, hξ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact Or.inr ⟨ξ, hne, a1 ξ hξ ξ hξ, (hm (ξ, 0)).1 hξ⟩
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.thetaCharacteristics_iff_testFunction_thetaSeries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∀ (a b : Fin n → Fin g → ℚ), ∃ φ : TF n g, IsSB φ ∧ (∀ m : Matrix (Fin n) (Fin g) ℚ, φ m = if ∀ k i, IsIntegral ℤ (m k i - a k i) then cexp (2 * π * I * ((∑ k, m k ⬝ᵥ b k : ℚ) : ℂ)) else 0) ∧ ∀ P, ∀ x ∈ X.dom, thP X hr bas idx φ P x = thFr X hr bas idx n (fun k i => (a k i : ℝ)) (fun k i => (b k i : ℝ)) P x) ∧ ∀ φ : TF n g, IsSB φ → ∃ (m : ℕ) (a b : Fin m → Fin n → Fin g → ℚ) (t : Fin m → ℂ), ∀ P, ∀ x ∈ X.dom, thP X hr bas idx φ P x = ∑ j, t j * thFr X hr bas idx n (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x := by
  first | exact @GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic | exact GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic | (intros; apply GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic <;> assumption)
end
