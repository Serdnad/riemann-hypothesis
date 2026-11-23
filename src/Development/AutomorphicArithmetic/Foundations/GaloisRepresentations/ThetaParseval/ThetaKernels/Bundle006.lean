module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DefsPlus
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle005
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle006
public import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.KCptPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.CellsSub
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.Imports

@[expose] public section

section



section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinLatF
theorem latRepF_cont_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om h f u
  have hσ : ∀ x, σ (σ x) = x := fun x => GlobalTheory.AdelicU.cm_conj_conj hB.cm x
  have H := isHeis_opFF hσ hS hT hξ hc h.hw
  have hfix : ∀ p : GAF σ JS × GAF σ JT, (∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ) →
      ∀ e, Fixes (opFF hc w) (latF F E nS nT Λ) e → Om p e = e := by
    intro p hp e he
    rw [h.vac p e he]
    exact GlobalTheory.FinWeilO.normOp_of_le H lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he
  have hev : ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
    intro f
    have hf : f ∈ Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} := by
      rw [h.span]; trivial
    induction hf using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨x, e, he, rfl⟩ := hm
      obtain ⟨N, hN, hNl⟩ := h.lev (w • x)
      filter_upwards [h.near, h.near' x N hN] with p hp hp'
      obtain ⟨l, hl, hl'⟩ := hp'
      have e2 : gamFF σ JS JT ξ₀ B.ψ (w • x) (N • l) = 1 := by
        rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNl l hl, one_mul]
      have e4 := H.comp x (N • l) e
      rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
      rw [h.op, hfix p hp e he, hl', ← e4]
    | zero => exact Filter.Eventually.of_forall fun p => map_zero _
    | add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add (f := _), h3, h4]
    | smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]
  haveI : IsTopologicalGroup (GAF σ JS) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GAF σ JT) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WOF F E nS nT → ℂ) u) ?_
  filter_upwards [h1.eventually (hev f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]
end GlobalTheory.FinLatF
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
set_option linter.unusedSectionVars false
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y}
theorem sigma_invol_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem cells'_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (hnb : IsNMap b nb) (T : nF σ Y b)
    (hT : IsND T) (γ : G2 σ Y) (hγ : γ ∈ rat2 σ Y) :
    (∃ p ∈ par2 σ Y, p ∈ rat2 σ Y ∧ ∃ ν ∈ nF σ Y b, γ = p * (w * nb ν)) ∨
    (∃ β₀ : nA σ Y b, B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace)) ≠ 1 ∧
      ∃ t, IsPar (γ * nb β₀ * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1) := by
  have hb0 := hb
  obtain ⟨⟨ε₀, hε₀⟩, t₀, ht₀⟩ := hb
  have hs := _root_.PositivityTheory.SiegelWeilFormula.kunf.sigma_invol_k B hB
  set e : E := ((ε₀ : ℤ) : E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : σ.toRingHom e = e := map_intCast _ _
  obtain ⟨M, hM, hMf⟩ := rat_frame hε₀ hγ
  obtain ⟨hMM', hM'M⟩ := frame_inv σ.toRingHom hs e he hse M hMf
  have hMi := inFrame_inv_of_rat hM hMM'
  by_cases hc : M.toBlocks₂₁.det ≠ 0
  · left
    have hblk : M.toBlocks₂₁ * (M.toBlocks₂₂.map σ.toRingHom)ᵀ +
        M.toBlocks₂₂ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) = 0 := by
      have h1 := congrArg Matrix.toBlocks₂₁ hMM'
      conv_lhs at h1 => rw [← Matrix.fromBlocks_toBlocks M]
      rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁] at h1
      simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
        Matrix.toBlocks_fromBlocks₂₂] at h1
      rw [h1]; ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have hν := herm_quot σ.toRingHom he _ _ hc hblk
    set νE := M.toBlocks₂₁⁻¹ * M.toBlocks₂₂ with hνE
    have hνA : (incM F νE)ᵀ = -((((ε₀ : ℤ) : AE F E)) • (incM F νE).map (cA σ)) := by
      rw [← incM_transpose', hν, incM_map_cA]
      ext i j; simp [incM, he_def]
    let ν : nA σ Y b := ⟨incM F νE, (mem_nA_iff hε₀ _).2 hνA⟩
    have hνF : ν ∈ nF σ Y b := mem_nF_iff.2 ⟨νE, rfl⟩
    have hwrat : w ∈ rat2 σ Y := rat_of_inFrame (M := jw n ((ε : ℤ) : E)) (by rw [hw, incM_jw, map_intCast]; rfl)
    refine ⟨γ * (w * nb ν)⁻¹, ?_, mul_mem hγ (inv_mem (mul_mem hwrat (nb_rat hnb hνF))), ν, hνF, by group⟩
    rw [mem_stabiliser_iff_frame_lower_block hb0, mul_inv_rev, ← nb_neg hnb, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul,
      GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hM, hnb, inFrame_w_inv hw, incM_toBlocks, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]
    have hcd : incM F M.toBlocks₂₁ * incM F νE = incM F M.toBlocks₂₂ := by
      rw [← incM_mul', hνE, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hc), Matrix.one_mul]
    show _ = 0
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
    change incM F M.toBlocks₂₁ * -(incM F νE) + incM F M.toBlocks₂₂ = 0
    rw [Matrix.mul_neg, hcd, neg_add_cancel]
  · right
    push Not at hc
    obtain ⟨T', hT'⟩ := mem_nF_iff.1 T.2
    have hTh : T'ᵀ = -(e • T'.map σ.toRingHom) := by
      have h1 := (mem_nA_iff hε₀ T.1.1).1 T.1.2
      rw [hT'] at h1
      apply incM_inj (F := F)
      rw [incM_transpose', h1, incM_map_cA]
      ext i j; simp [incM, he_def]
    have hTd : T'.det ≠ 0 := by
      intro h0; apply hT
      show T.1.1.det = 0
      rw [hT', incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    have hda : e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ * M.toBlocks₁₁ + (M.toBlocks₁₁.map σ.toRingHom)ᵀ * M.toBlocks₂₁ = 0 := by
      have h1 := congrArg Matrix.toBlocks₂₁ hM'M
      rw [toBlocks₂₁_mul', Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at h1
      rw [h1]; ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    obtain ⟨β₁, hβh, hcβ, ⟨v, w', hvw, hvw0⟩, htr⟩ :=
      exists_beta σ.toRingHom hs e he hse M.toBlocks₁₁ M.toBlocks₂₁ _ hc hda T' hTh hTd
    have hx0 : Algebra.trace F E (2 : E) ≠ 0 := by
      rw [show (2 : E) = algebraMap F E 2 from (map_ofNat (algebraMap F E) 2).symm, Algebra.trace_algebraMap, nsmul_eq_mul]
      exact mul_ne_zero (Nat.cast_ne_zero.2 Module.finrank_pos.ne') two_ne_zero
    obtain ⟨l, hl⟩ := psi_moves hB.std _ hx0
    set Λ : AE F E := algebraMap (AF F) (AE F E) l with hΛ
    have hcΛ : cA σ Λ = Λ := (cA σ).commutes l
    have hβA : (Λ • incM F β₁)ᵀ = -((((ε₀ : ℤ) : AE F E)) • (Λ • incM F β₁).map (cA σ)) := by
      have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun _ => rfl
      rw [Matrix.transpose_smul, ← incM_transpose', hβh]
      ext i j
      simp [incM, he_def, hcΛ, hc]
      ring
    let β₀ : nA σ Y b := ⟨Λ • incM F β₁, (mem_nA_iff hε₀ _).2 hβA⟩
    refine ⟨β₀, ?_, ?_⟩
    · have htt : Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace = l * algebraMap F (AF F) (Algebra.trace F E 2) := by
        show Algebra.trace (AF F) (AE F E) (T.1.1 * (Λ • incM F β₁)).trace = _
        rw [hT', Matrix.mul_smul, Matrix.trace_smul, ← incM_mul', smul_eq_mul, hΛ, ← Algebra.smul_def,
          LinearMap.map_smul, tt_rat, htr, smul_eq_mul]
      rw [htt]; exact hl
    · set Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := Matrix.fromBlocks 0 β₁ 0 0 with hZ
      have hN : Matrix.fromBlocks 1 (β₀ : Matrix (Fin n) (Fin n) (AE F E)) 0 1 = 1 + Λ • incM F Z := by
        show Matrix.fromBlocks 1 (Λ • incM F β₁) 0 1 = _
        ext (i | i) (j | j) <;> simp [hZ, incM, Matrix.one_apply]
      have h1 : incM F M * incM F (Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
          (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ) = 1 := by
        rw [← incM_mul', hMM']; ext i j; simp [incM, Matrix.one_apply]
      have hX : M * Z * Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
          (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ =
          Matrix.fromBlocks (M.toBlocks₁₁ * β₁ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ))
            (M.toBlocks₁₁ * β₁ * (M.toBlocks₁₁.map σ.toRingHom)ᵀ)
            (M.toBlocks₂₁ * β₁ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ))
            (M.toBlocks₂₁ * β₁ * (M.toBlocks₁₁.map σ.toRingHom)ᵀ) := by
        conv_lhs => enter [1, 1]; rw [← Matrix.fromBlocks_toBlocks M]
        rw [hZ, conj_blocks]
      have hP : inFrame b (γ * nb β₀ * γ⁻¹) = 1 + Λ • incM F (M * Z *
          Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
            (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ) := by
        rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hM, hnb, hMi, hN, Matrix.mul_add,
          Matrix.mul_one, Matrix.add_mul, h1, Matrix.mul_smul, Matrix.smul_mul, incM_mul', incM_mul']
      have h21 : (inFrame b (γ * nb β₀ * γ⁻¹)).toBlocks₂₁ = 0 := by
        rw [hP, hX, hcβ]
        ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply, incM]
      have h11 : (inFrame b (γ * nb β₀ * γ⁻¹)).toBlocks₁₁ = 1 + Λ • incM F (Matrix.vecMulVec v w') := by
        rw [hP, hX, hvw]
        ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply, incM]
      obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 ((mem_stabiliser_iff_frame_lower_block hb0 _).2 h21)
      have ht1 := ((isPar_frame ht₀ _ t).1 ht).2
      refine ⟨t, ht, Units.ext ?_⟩
      show t.1.det = 1
      have hdet : (1 + Λ • incM F (Matrix.vecMulVec v w')).det = 1 := by
        rw [show Λ • incM F (Matrix.vecMulVec v w') =
          Matrix.vecMulVec (fun i => Λ * inclR (F := F) (AF F) (v i)) (fun j => inclR (F := F) (AF F) (w' j)) by
            ext i j; simp [incM, Matrix.vecMulVec_apply, mul_assoc]]
        apply det_one_add_rank_one
        have : (fun j => inclR (F := F) (AF F) (w' j)) ⬝ᵥ (fun i => Λ * inclR (F := F) (AF F) (v i)) =
            Λ * inclR (F := F) (AF F) (w' ⬝ᵥ v) := by

          simp [dotProduct, Finset.mul_sum, map_sum, mul_left_comm]
        rw [this, hvw0, map_zero, mul_zero]
      rw [ht1, Matrix.det_mul, Matrix.det_mul, h11, hdet, mul_one, ← Matrix.det_mul, incM_GL_mul_inv, Matrix.det_one]
theorem cells_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (hnb : IsNMap b nb) (T : nF σ Y b)
    (hT : IsND T) (γ : G2 σ Y) (hγ : γ ∈ rat2 σ Y) :
    (∃ p ∈ par2 σ Y, p ∈ rat2 σ Y ∧ ∃ ν ∈ nF σ Y b, γ = p * (w * nb ν)) ∨
    (∃ β₀ : nA σ Y b, B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace)) ≠ 1 ∧
      ∃ t, IsPar (γ * nb β₀ * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1) :=
  _root_.PositivityTheory.SiegelWeilFormula.kunf.cells'_k B hB hb hw hnb T hT γ hγ
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def FinLevel_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (K : Subgroup (G2 σ Y)),
    IsCompact (K : Set (G2 σ Y)) → ∀ Φ ∈ schA F κ, ∃ Λ : Set (Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      (∀ u ∈ Λ, (∀ i, evI F ((dd.e u).1 i) = 0) ∧ (∀ i, evI F ((dd.e u).2 i) = 0) ∧ ∀ k ∈ K, actB (cA σ) k u ∈ Λ) ∧
      (∀ u ∈ Λ, dd.rho B.ψ u Φ = Φ) ∧ ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧
        ∀ Ψ : (κ → AF F) → ℂ, (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) → ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) →
          ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def VacFix2_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ → ∀ χ : Chr F E, IsHecke F E χ → ∀ dd om, IsDblCoordX M dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (dbl (incM F X.J)) dd χ (diagCols (Fin n)) om →
    ∀ K, IsStab2 (σ := σ) (Y := X) B K → ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
      Acts (evFin F v) (om k) (boxFun (M.vac v) (star (M.vac v))) (boxFun (M.vac v) (star (M.vac v)))
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Bad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
variable {Y : Spc F E n} {B : Base F E} {v : Pl F} {r s : ℕ}
theorem theta_pm_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) : Y.θ w = 1 ∨ Y.θ w = -1 :=
  cartan_pm (h.sig w) h0 (fun i j => (hB.cm.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))) (h.cartan w)
theorem commute_theta_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) (A) : Commute A (Y.θ w) := by
  rcases _root_.GlobalTheory.ThK.Dbl.Bad.theta_pm_k hB h h0 w with e | e <;> rw [e]
  exacts [Commute.one_right _, Commute.neg_one_right _]
theorem stab_iff_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (UA σ Y.J)} (hK : IsStab B K)
    {g : UA σ Y.J} : g ∈ K ↔ ∀ v, IntAt v g :=
  (hK g).trans ⟨fun a _ z hz _ => a.2 z hz, fun a => ⟨fun w => _root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _, fun _ hz =>
    ⟨mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).1) hz, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).2) hz⟩⟩⟩
theorem emb_mem_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K)
    {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : ∀ v, IntAt v g) :
    e (g, 1) ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k hk => ?_⟩
  · rw [he g 1, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    simp only [Commute, SemiconjBy, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (_root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _).eq, (_root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _).neg_right.eq]
  · obtain ⟨g', e1, hg'⟩ : ∃ g', k = e (g', 1) ∧ mat g' *ᵥ z ∈ latHat Y := by
      rcases hk with rfl | rfl
      · exact ⟨g, rfl, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).1) hz⟩
      · exact ⟨g⁻¹, by rw [← map_inv, Prod.inv_mk, inv_one], mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).2) hz⟩
    rw [e1, he g' 1, Matrix.fromBlocks_mulVec, show mat (1 : UA σ Y.J) = 1 from rfl]
    simpa using ⟨hg', hz'⟩
end GlobalTheory.ThK.Dbl.Bad
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def SiegelWeilStd_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ)
    (A : Spc F E m) (Y : Spc F E n) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n → min r s = 0 →
    (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
namespace SiegelEisensteinSeries.BRoad
open Filter Topology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
def SiegelMult_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ (A : ℂ → ℂ) (H : ℂ → modFun σ Y) (t : ℝ), Differentiable ℂ A ∧ (∃ z, A z ≠ 0) ∧
        (∀ μ, IsGrowForm μ → Differentiable ℂ (fun s => μ (H s))) ∧
        ∀ s : ℂ, t < s.re → ∀ x, HasSum (fun q => A s * eisTerm (flat a f s₁ s) x q) ((H s).1 x)
end SiegelEisensteinSeries.BRoad
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.BRoad
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.kunf.SecA
attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
theorem isCompact_stdK'_k (B : Base F E) (Y : Spc F E n) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (b : GL (Fin n ⊕ Fin n) E)
    (K : Subgroup (G2 σ Y)) (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) := by
  obtain ⟨Φ, hΦ, eΦ⟩ := GlobalTheory.ThK.Dbl.St.exists_section hB.cm B.emb
  have hI : IsCompact (intHat F E : Set (AE F E)) := isCompact_intHat
  have hfe : finOne F = GlobalTheory.ThK.Dbl.St.eF F := rfl
  set T : Set (AE F E) := Φ '' Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) + (intHat F E : Set (AE F E))
    with hTdef
  have hT : IsCompact T := ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).image hΦ).add hI
  have hentry : ∀ k ∈ K, ∀ i j, inFrame b k i j ∈ T := by
    intro k hk i j
    obtain ⟨h1, h2⟩ := (hK k).1 hk
    rw [eΦ (inFrame b k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      have hu : (inFrame b k).map (piInf (B.emb w)) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ :=
        Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact h1 w)
      exact entry_norm_bound_of_unitary hu i j
    · rw [← hfe]
      exact h2 k (Set.mem_insert _ _) i j
  set S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) => incM F b.1 * M * incM F (b⁻¹).1) '' Set.univ.pi (fun _ => Set.univ.pi fun _ => T) with hSdef
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hT).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hmat : ∀ k ∈ K, mat2 k ∈ S := fun k hk => ⟨inFrame b k, fun i _ j _ => hentry k hk i j, by
    show incM F b.1 * (incM F (b⁻¹).1 * mat2 k * incM F b.1) * incM F (b⁻¹).1 = mat2 k
    simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]⟩
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have hIc := hI.isClosed
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := Y) b
  have hKset : (K : Set (G2 σ Y)) =
      (⋂ w, {k | (inFrame b k).map (piInf (B.emb w)) * ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, {k : G2 σ Y | finOne F • inFrame b k i j ∈ intHat F E}) ∩
          (⋂ i, ⋂ j, {k : G2 σ Y | finOne F • inFrame b k⁻¹ i j ∈ intHat F E})) := by
    ext k
    simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.forall_mem_insert,
      Set.mem_singleton_iff, forall_eq]
  have hKc : IsClosed (K : Set (G2 σ Y)) := by
    rw [hKset]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_))
    · exact (hfr.matrix_map (hp w)).matrix_mul (hfr.matrix_map (hp w)).matrix_conjTranspose
    · exact (hfr.matrix_elem i j).const_smul (finOne F)
    · exact ((hfr.comp continuous_inv).matrix_elem i j).const_smul (finOne F)
  exact GlobalTheory.ThK.Dbl.St.isCompact_of_units (UG (cA σ) (dbl (incM F Y.J))) (GlobalTheory.EisBL.DoubledGroupTopology.isClosed_doubled_group σ Y) K hKc S hS
    fun k hk => ⟨hmat k hk, hmat k⁻¹ (K.inv_mem hk)⟩
variable {Y : Spc F E n}
end PositivityTheory.SiegelWeilFormula.kunf.SecA
end
end
end
