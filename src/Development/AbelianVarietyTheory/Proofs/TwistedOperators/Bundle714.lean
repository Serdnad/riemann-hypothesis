module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle695
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle474
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle429
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle605
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle706
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle707
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowMovedLatticeSplitsBesselLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle704
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors




namespace GlobalTheory.RowShape.LastBF

open GlobalTheory.GoodPos GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mem_completedHomLattice_iff_selfDual_source {S T : HSp D} {LS : Lat S} (LT : Lat T) (hS : IsSelfDualC S LS) (P : Pl D → Prop) (u : WO S T) :
    u ∈ latO S T (LS : Set _) (LT : Set _) P ↔
      MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  refine ⟨fun hu => ⟨latO_mxAt hu, fun y hy => latO_maps hS hu hy⟩, fun ⟨hP, hmap⟩ => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := exists_dualBasis S hS
  let yv : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)
  have hyv : ∀ i, yv i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨indP D.host.F P, indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hu : u = ∑ i, rowMul S T (s' i) (u *ᵥ yv i) := by
    ext k j
    simp only [Matrix.sum_apply, rowMul, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, yv]
    simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← TensorProduct.tmul_sum, hdual]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; exact (mul_indP (hP k j)).symm
    · intro l _ hl; rw [if_neg hl, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hu]
  exact sum_mem fun i _ => rowMul_mem (hs' i) (hmap _ (hyv i))

theorem last_of_line {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} (LW : Lat W)
    (hM : IsSelfDualC V₀ M) {x : Pl D} {m : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hW : ∀ t ∈ idAt D (· = x), colMul d.jY r t ∈ latA W LW (· = x) ↔
      incA D D.host.xi0 * cA D (m : AE D) * t ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [mem_completedHomLattice_iff_selfDual_source LW hM, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hW _ (Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.LocSD.hermAt_mem_idAt (hsd.1 y hy) _)),
    ← herm_conj V₀ y (((m : AE D) * a) • ratV z), int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1]
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D m * GlobalTheory.IwaPlace.hermAt V₀ y (a • ratV z)) * e3

theorem const_mem_latPi {S : HSp D} (i₀ : Fin S.rank) (I : FI D) (v : Pl D) (s : AE D) :
    (fun _ => s) ∈ latV S (latPi S I) (· = v) ↔ s ∈ idV I v := by
  constructor
  · intro hy
    have key : ∀ y ∈ latV S (latPi S I) (· = v), y i₀ ∈ idV I v := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, a, rfl, z, hz, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨α, hα, h0, z i₀, mem_latPi.1 hz i₀, by simp only [one_mul]⟩
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | neg a _ ha => exact neg_mem ha
    exact key _ hy
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, z, hz, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, fun _ => z, mem_latPi.2 fun _ => hz,
        funext fun i => by rw [one_mul]⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha

theorem AA_mul_rowId (j τ : ℕ) (hj : j + 2 * (τ + 1) + 2 = D.R.m) (p : Fin (D.R.m - 1 - (j + 1))) (hp : p.1 = τ + 1) :
    D.host.AA * rowId D (j + 1) p = FractionalIdeal.spanSingleton _ (star (D.host.xi0 ^ τ)) * lineId D j := by
  have hodd : Odd (j + 1) := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - τ - 2, by omega⟩
  unfold rowId tiltSc lineId stairId
  rw [if_pos hodd, if_neg (by omega), show D.R.m - 1 - (j + 1) - 1 - p.1 = τ by omega,
    show D.R.m - 1 - (j + 1) - p.1 = τ + 1 by omega, show (D.R.m - 2 - j) / 2 = τ + 1 by omega, hp,
    pow_succ D.host.AA (τ + 1)]
  ring

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem last_rowN (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) (hσ : 0 < σ) :
    ∀ a ∈ idAt D (· = v),
    (rowJac G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (G.V (.grid D.R.m (j + 1)))
        (coreL G j : Set _) (rowN G (j + 1) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  obtain ⟨τ, rfl⟩ : ∃ τ, σ = τ + 1 := ⟨σ - 1, by omega⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hL : IsSelfDualC _ (lineL D j) :=
    isSelfDualC_latPi (GlobalTheory.RowShape.nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (G.Λ (.top j)) :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  have hM : IsSelfDualC _ (coreL G j) := GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL
  have ho : OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (coreL G j) (G.Λ (.top j)) (lineL D j) v := GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v (lineId D j) (lineId_ne_zero D j)
  have hx : D.host.xi0 ^ (τ + 1) ≠ 0 := pow_ne_zero _ hξ
  have hm0 : g * (D.host.xi0 ^ (τ + 1))⁻¹ ≠ 0 := mul_ne_zero hg (inv_ne_zero hx)
  have hline : ∀ a ∈ idAt D (· = v),
      a • ratV (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ∈
        latV (GlobalTheory.SeeSaw.Model.nLine D) (lineL D j) (· = v) ↔
      (((inU _ hm0)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = v) := fun a ha => by
    refine (const_mem_latPi (S := GlobalTheory.SeeSaw.Model.nLine D) (0 : Fin 1) (lineId D j) v
      (a * incA D (D.host.xi0 ^ (τ + 1)))).trans ?_
    rw [hgen, and_iff_left (Ideal.mul_mem_right _ _ ha), inU_inv, mul_inv, inv_inv, RingHom.map_mul, mul_assoc, mul_comm a]
  have hU := line_norm (GlobalTheory.SeeSaw.Model.isLineVec_nLine hx) hL hline
  have hN : star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ⬝ᵥ
      (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => D.host.xi0 ^ (τ + 1)) =
      -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) := by
    rw [GlobalTheory.RowShape.nLine_gram, neg_mulVec, one_mulVec, dotProduct_neg]
    exact congrArg Neg.neg (Fin.sum_univ_one (fun _ : Fin 1 => star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)))
  rw [hN] at hU
  refine last_of_line _ _ _ hM (m := inU _ hm0) (Fin.last τ) rfl (fun t ht => ?_)
    (fun a ha => (orth_line _ ho _ a).symm.trans (hline a ha))
  have hc : colMul (rowJac G (j + 1) (by omega) (τ + 1) (by omega)).jY (Fin.last τ) t =
      fun k => t * incA D ((G.rowDec (j + 1) (by omega)).a k
        (Fin.castLE (by omega : τ + 1 ≤ D.R.m - 1 - (j + 1)) (Fin.last τ)).rev) := by
    funext k
    rfl
  have hs : star (D.host.xi0 ^ τ) ≠ 0 := star_ne_zero.2 (pow_ne_zero _ hξ)
  rw [hc, rowN, dite_eq_left (by omega), (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2,
    AA_mul_rowId j τ hj _ (by simp only [Fin.val_rev, Fin.val_castLE, Fin.val_last]; omega),
    idV_spanSingleton_mul_iff D v _ _ hs t, and_iff_left ht, hgen, and_iff_left (Ideal.mul_mem_left _ _ ht),
    hU _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ht)), inU_val]
  have e : g * (D.host.xi0 ^ (τ + 1))⁻¹ * -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) *
      (g⁻¹ * (star (D.host.xi0 ^ τ))⁻¹) = D.host.xi0 := by
    rw [pow_succ D.host.xi0 τ, star_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    have := pow_ne_zero τ hξ
    field_simp
  have e' := congrArg (incA D) e
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul (incA D) g⁻¹] at e'
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D (incA D (g * (D.host.xi0 ^ (τ + 1))⁻¹)) * t) * e'

end GlobalTheory.RowShape.LastBF

theorem GlobalTheory.RowShape.big_last_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj v hσ =>
    GlobalTheory.RowShape.LastBF.last_rowN ch.G j σ hj v hσ⟩⟩

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gridRowMovedLattice_splits_jacobi_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.MonoAt (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) (ch.G.Λ (.top n)) v := by
  first | exact @GlobalTheory.RowShape.rowN_monoAt | exact GlobalTheory.RowShape.rowN_monoAt | (intros; apply GlobalTheory.RowShape.rowN_monoAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.jacobiFlagChar_primitive_movedLattice_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) v := by
  first | exact @GlobalTheory.RowShape.big_primAt_rowJac | exact GlobalTheory.RowShape.big_primAt_rowJac | (intros; apply GlobalTheory.RowShape.big_primAt_rowJac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.negLineLattice_and_besselCoreLattice_selfDual_split : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ, j + 2 * σ + 2 = D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.lineL D j) ∧
    IsSelfDualC _ (GlobalTheory.RowShape.coreL ch.G j) ∧ ∀ v, GlobalTheory.FinPl.OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (GlobalTheory.RowShape.coreL ch.G j) (ch.G.Λ (.top j)) (GlobalTheory.RowShape.lineL D j) v := by
  first | exact @GlobalTheory.RowShape.coreL_selfDual_split | exact GlobalTheory.RowShape.coreL_selfDual_split | (intros; apply GlobalTheory.RowShape.coreL_selfDual_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.posNormLine_selfDual_and_topLattice_splits : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v := by
  first | exact @GlobalTheory.RowShape.topL_selfDual_orthAt | exact GlobalTheory.RowShape.topL_selfDual_orthAt | (intros; apply GlobalTheory.RowShape.topL_selfDual_orthAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselToJacobi_basePoint_carries_row_lattice_lines : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, GlobalTheory.FinPl.ColsAt (besDecAt ch.G j σ hj) (xZero (rowJac ch.G (j + 1) (by omega) σ (by omega)))
    (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.rowN ch.G (j + 1)) v := by
  first | exact @GlobalTheory.RowColsBF.colsAt_bf | exact GlobalTheory.RowColsBF.colsAt_bf | (intros; apply GlobalTheory.RowColsBF.colsAt_bf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.jacobiToBessel_carries_flagLines_rowPeriod_succ : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ i σ (hi : i + 2 * (σ + 1) + 1 = D.R.m) v, GlobalTheory.FinPl.ColsAt (rowJac ch.G i (by omega) (σ + 1) (by omega))
    (xLast (besDecAt ch.G (i + 1) σ (by omega)) (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ))
    (GlobalTheory.RowShape.rowN ch.G i) (GlobalTheory.RowShape.rowN ch.G (i + 1)) v := by
  first | exact @GlobalTheory.RowShape.cols_jacBes_rowN | exact GlobalTheory.RowShape.cols_jacBes_rowN | (intros; apply GlobalTheory.RowShape.cols_jacBes_rowN <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastSeesawLineMap_keeps_lattices_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j + 2 = D.R.m → ∀ v, ∀ w ∈ latO (ch.G.V (.top (j + 1))) (pLine D) (ch.G.Λ (.top (j + 1)) : Set _) (GlobalTheory.RowShape.topL D : Set _) (· = v),
    GlobalTheory.FinPl.kap lastTau _ w ∈ latO (GlobalTheory.SeeSaw.Model.nLine D) (ch.G.V (.top (j + 1))) (GlobalTheory.RowShape.lineL D j : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (· = v) := by
  first | exact @GlobalTheory.LastLineLat.kap_lastTau_latO | exact GlobalTheory.LastLineLat.kap_lastTau_latO | (intros; apply GlobalTheory.LastLineLat.kap_lastTau_latO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselFlag_character_primitive_rowTest_movedLattice : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (besDecAt ch.G j σ hj) (GlobalTheory.RowShape.rowN ch.G j) v := by
  first | exact @GlobalTheory.RowShape.big_primAt_rowN | exact GlobalTheory.RowShape.big_primAt_rowN | (intros; apply GlobalTheory.RowShape.big_primAt_rowN <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gridRowMovedLattice_splits_bessel_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, GlobalTheory.FinPl.MonoAt (besDecAt ch.G j σ hj) (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.coreL ch.G j) v := by
  first | exact @GlobalTheory.RowShape.big_monoAt_rowN | exact GlobalTheory.RowShape.big_monoAt_rowN | (intros; apply GlobalTheory.RowShape.big_monoAt_rowN <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowRepLoc
open GlobalTheory.LocGrp GlobalTheory.LocMod

private lemma lev_le_of_sum_elim_le {σ p' : ℕ} (hp : p' = σ ∨ p' = σ + 1) {n : Type} (r s : n ⊕ Fin (2 * σ))
    (h : (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2) : n ⊕ Fin (2 * σ) → ℕ) s ≤
      (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2) : n ⊕ Fin (2 * σ) → ℕ) r) :
    GlobalTheory.RootEx.lev p' s ≤ GlobalTheory.RootEx.lev p' r := by

  rcases hp with rfl | rfl <;> rcases r with r | r <;> rcases s with s | s <;>
    simp only [Sum.elim_inl, Sum.elim_inr, GlobalTheory.RootEx.lev] at h ⊢ <;> (try split_ifs at h) <;> omega

private lemma mul_apply_eq_of_mul_eq_of_col_eq {K : Type} [Field K] {m n n' : Type} [Fintype m] (M : Matrix m m K) (X : Matrix m n K)
    (Y : Matrix m n' K) (hX : M * X = X) (i : n) (j : n') (hc : ∀ t, X t i = Y t j) (r : m) : (M * Y) r j = Y r j := by

  have h := congrFun (congrFun hX r) i
  simp only [Matrix.mul_apply, hc] at h ⊢
  exact h

theorem mem_jac {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    {A B : HSp D} {σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B (2 * σ) ε)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) k} (hb : b * b' = 1) (hb' : b' * b = 1) {u : Fin (2 * σ) → k}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ)) (Fin B.rank) k} (h1 : Γ * sumCols d p.π b u = 1) (h2 : sumCols d p.π b u * Γ = 1)
    {g : GA D B} (hg : SuppAt p.e B g) {x : GL (Fin A.rank ⊕ Fin (2 * σ)) k}
    (e : x.val = Γ * ((mt B g).map p.π * sumCols d p.π b u)) (hx : x ∈ symR k (Fin A.rank) (2 * σ)) :
    g ∈ jacGrp (jacDec d rfl) := by
  classical
  have hS : ∀ r (j : Fin (2 * σ)), sumCols d p.π b u r (Sum.inr j) = p.π (incA D (d.a r j)) * u j := by
    intro r j
    simp only [sumCols, Matrix.fromCols_apply_inr, Matrix.mul_diagonal, Matrix.map_apply, RingHom.comp_apply]
  let F : Frame k B.rank (Fin A.rank ⊕ Fin (2 * σ)) := ⟨sumCols d p.π b u, Γ, h2, h1⟩
  let FA : Frame k A.rank (Fin A.rank) := ⟨b, b', hb, hb'⟩
  obtain ⟨φ, hφ⟩ := exists_hom p F
  have hgx : p.IsLoc F g x := by
    refine ⟨hg, ?_⟩
    show (mt B g).map p.π = sumCols d p.π b u * x.val * Γ
    rw [e]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [isLoc_unique p hgx (hφ x)]

  have hfix : ∀ g₀ : GA D A, (mt B ((jacDec d rfl).emb0 g₀)).map p.π * d.a.map (p.π.comp (incA D)) =
      d.a.map (p.π.comp (incA D)) := by
    intro g₀
    have hX := map_fix p (HypDec.wittDecomp_anisotropicEmbedding_inclX (d := jacDec d rfl) (g := g₀))
    have hY := map_fix p (HypDec.wittDecomp_anisotropicEmbedding_inclY (d := jacDec d rfl) (g := g₀))
    ext r j
    by_cases hj : j.val < σ
    · exact mul_apply_eq_of_mul_eq_of_col_eq _ _ _ hX ⟨j.val, hj⟩ j (fun t => rfl) r
    · refine mul_apply_eq_of_mul_eq_of_col_eq _ _ _ hY ⟨2 * σ - 1 - j.val, by omega⟩ j (fun t => ?_) r
      show p.π (incA D ((jacDec d rfl).e' t ⟨2 * σ - 1 - j.val, by omega⟩)) = p.π (incA D (d.a t j))
      dsimp only [jacDec, Matrix.submatrix_apply, id]
      congr 3
      apply Fin.ext
      simp
      omega
  have hN : ∀ p', (p' = σ ∨ p' = σ + 1) → GlobalTheory.RootEx.N k (Fin A.rank) (2 * σ) p' ≤ (jacGrp (jacDec d rfl)).comap φ := by
    intro p' hp'
    unfold GlobalTheory.RootEx.N
    rw [Subgroup.closure_le]
    intro q hq
    show φ q ∈ flagN (jacDec d rfl) ⊔ (jacDec d rfl).emb0.range
    refine Subgroup.mem_sup_left (flag_of_strict p (jacDec d rfl) FA F
      (Sum.elim (fun a => Sum.inl a) (Sum.elim (fun i : Fin σ => Sum.inr ⟨i.val, by omega⟩)
        (fun i : Fin σ => Sum.inr ⟨2 * σ - 1 - i.val, by omega⟩))) ?_
      (Sum.elim (fun _ => (1 : k)) (Sum.elim (fun i : Fin σ => u ⟨i.val, by omega⟩)
        (fun i : Fin σ => u ⟨2 * σ - 1 - i.val, by omega⟩))) ?_
      (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2)) ?_ (hφ q) ?_)
    · rintro (a | j)
      · exact ⟨Sum.inl a, rfl⟩
      · by_cases hj : j.val < σ
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, hj⟩), rfl⟩
        · refine ⟨Sum.inr (Sum.inr ⟨2 * σ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext ?_)⟩
          show 2 * σ - 1 - (2 * σ - 1 - j.val) = j.val
          omega
    · rintro r (a | i | i)
      · show sumCols d p.π b u r (Sum.inl a) = 1 * ((jacDec d rfl).j0.map p.π * b) r a
        rw [one_mul]
        rfl
      · show sumCols d p.π b u r (Sum.inr ⟨i.val, _⟩) = u ⟨i.val, _⟩ * ((jacDec d rfl).jX.map p.π) r i
        rw [hS, mul_comm]
        rfl
      · show sumCols d p.π b u r (Sum.inr ⟨2 * σ - 1 - i.val, _⟩) = u ⟨2 * σ - 1 - i.val, _⟩ * ((jacDec d rfl).jY.map p.π) r i
        rw [hS, mul_comm]
        show u ⟨2 * σ - 1 - i.val, _⟩ * p.π (incA D (d.a r ⟨2 * σ - 1 - i.val, _⟩)) =
          u ⟨2 * σ - 1 - i.val, _⟩ * p.π (incA D ((jacDec d rfl).e' r i))
        dsimp only [jacDec, Matrix.submatrix_apply, id]
        congr 4
        apply Fin.ext
        simp
        omega
    · rintro (a | i | i)
      · rfl
      · show (if i.val < σ then i.val + 1 else i.val + 2) = i.val + 1
        rw [if_pos i.isLt]
      · show (if 2 * σ - 1 - i.val < σ then 2 * σ - 1 - i.val + 1 else 2 * σ - 1 - i.val + 2) = 2 * σ - i.val + 1
        have := i.isLt
        rw [if_neg (by omega)]
        omega
    · intro r s hrs
      have hq' : GlobalTheory.RootEx.InN p' q := hq
      rw [Matrix.sub_apply, hq' r s (lev_le_of_sum_elim_le hp' r s hrs), sub_self]
  have hR : symR k (Fin A.rank) (2 * σ) ≤ (jacGrp (jacDec d rfl)).comap φ := by
    unfold symR symN
    rw [show (2 * σ + 1) / 2 = σ by omega, show 2 * σ / 2 + 1 = σ + 1 by omega]
    refine sup_le ?_ (sup_le (hN σ (Or.inl rfl)) (hN (σ + 1) (Or.inr rfl)))
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨ψ, hψ⟩ := exists_hom p FA
    have hloc : p.IsLoc F ((jacDec d rfl).emb0 (ψ g₀)) (embX (2 * σ) g₀) := by
      refine ⟨suppAt_wittLeviEmbedding _ (hψ g₀).1, ?_⟩
      refine eq_embX F _ g₀ ((frameMat B A d.ι).map (p.π.comp (incA D)) * b) (fun r a => rfl) ?_ ?_
      · exact intertwine p (HypDec.wittDecomp_anisotropicEmbedding_inclAnisotropic (d := jacDec d rfl) (g := ψ g₀)) (hψ g₀)
      · intro j
        refine fix_col (hfix (ψ g₀)) (u j) j (fun r => ?_)
        show sumCols d p.π b u r (Sum.inr j) = u j * (d.a.map (p.π.comp (incA D))) r j
        rw [hS, mul_comm]
        rfl
    show φ (embX (2 * σ) g₀) ∈ flagN (jacDec d rfl) ⊔ (jacDec d rfl).emb0.range
    rw [isLoc_unique p (hφ _) hloc]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  exact hR hx

end GlobalTheory.RowRepLoc

theorem GlobalTheory.RowRepLoc.mem_jacGrp_of_symR : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ), 1 ≤ σ → ∀ (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b) (q : GlobalTheory.FinPl.SplitPt D (Kw w)), (∀ x, q.pr x = GlobalTheory.RowRep.piAt w x) → ∀ g : GA D B, SuppAt q.e B g → frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c → g ∈ jacGrp (jacDec d h) := by
  intro D A B c σ ε d h _ w β β' u hF _ a b ha hb hab q hq g hg hx
  subst h ha hb
  obtain ⟨Γ, hΓ1, hΓ2, hΓ⟩ := frame_val d w hF
  have hπ : (GlobalTheory.LocMod.Place.ofSplitPt q).π = piAt w := RingHom.ext hq
  refine GlobalTheory.RowRepLoc.mem_jac (GlobalTheory.LocMod.Place.ofSplitPt q) d (b' := (GlobalTheory.StdFrames.loc w β)⁻¹.val)
    (Units.mul_inv _) (Units.inv_mul _) (u := u) (Γ := Γ) ?_ ?_ hg (x := frameGL hab (inBasis rfl β' w (Lev.finE B g))) ?_ hx
  · rw [hπ]; exact hΓ1
  · rw [hπ]; exact hΓ2
  · rw [hπ]; exact hΓ g

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistCharacter_mem_twistFiniteValueProductSubgroup : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (x : (AE D)ˣ), Circle.toUnits (R.toLevCh.xi t x) ∈ xiVals R.toLevCh t := by
  first | exact @GlobalTheory.XiVals.xi_mem | exact GlobalTheory.XiVals.xi_mem | (intros; apply GlobalTheory.XiVals.xi_mem <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselLastVector_mem_homLattice_iff_integral : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) := by
  first | exact @GlobalTheory.RowShape.big_last_rowN | exact GlobalTheory.RowShape.big_last_rowN | (intros; apply GlobalTheory.RowShape.big_last_rowN <;> assumption)

end
end
