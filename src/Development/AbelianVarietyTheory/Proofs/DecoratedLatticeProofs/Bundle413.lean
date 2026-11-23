module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle362
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle007
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.RowFormsAdelic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.CjVol

open GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem colE_inv_val_eq_zero (ρ : ℕ) (β : n → k) (t s : n ⊕ Fin c) (h : lev (ρ + 1) t ≠ lev (ρ + 1) s) :
    (colE c (ρ + 1) β)⁻¹.val t s = 0 := by
  rcases t with t | t <;> rcases s with s | s
  · exact absurd rfl h
  · simp only [colE, upU, Units.inv_mk, fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.of_apply]
    rw [if_neg, neg_zero]
    intro hs; apply h; simp [lev, hs]
  · simp [colE, upU]
  · have : t ≠ s := by rintro rfl; exact h rfl
    simp [colE, upU, Matrix.one_apply, this]

theorem colE_uni (ρ : ℕ) (β : n → k) :
    ∀ r s, (Sum.elim (fun _ => 0) (fun _ => 1) : n ⊕ Fin c → ℕ) s ≤ Sum.elim (fun _ => 0) (fun _ => 1) r →
      (colE c (ρ + 1) β).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rintro (r | r) (s | s) h
  · simp [colE, upU, Matrix.one_apply]
  · simp at h
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem colE_inv_uni (ρ : ℕ) (β : n → k) :
    ∀ r s, (Sum.elim (fun _ => 0) (fun _ => 1) : n ⊕ Fin c → ℕ) s ≤ Sum.elim (fun _ => 0) (fun _ => 1) r →
      (colE c (ρ + 1) β)⁻¹.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rintro (r | r) (s | s) h
  · simp [colE, upU, Matrix.one_apply]
  · simp at h
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem extendAboveDiagonalEntries_mul_blockRespecting (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (hh : ∀ t s, lev p t ≠ lev p s → h t s = 0) (e : Ix n c p → k) :
    ext0 (Up n c p) e * h = ext0 (Up n c p) ((rm (Up n c p) h).mulVec e) := by
  ext r s
  by_cases hrs : lev p r < lev p s
  · rw [matrixExtendByZero_mul (Up n c p) h e ⟨(r, s), hrs⟩]
    simp [ext0, hrs]
  · have : ext0 (Up n c p) ((rm (Up n c p) h).mulVec e) r s = 0 := by
      simp only [ext0, Matrix.of_apply]; rw [dite_eq_right hrs]
    rw [this, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hts : lev p t = lev p s
    · have : ext0 (Up n c p) e r t = 0 := by
        simp only [ext0, Matrix.of_apply]; rw [dite_eq_right (show ¬ lev p r < lev p t by rw [hts]; exact hrs)]
      rw [this, zero_mul]
    · rw [hh t s hts, mul_zero]

theorem cjE_mkNel (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (e : Ix n c (ρ + 1) → k) :
    cjE ρ h1 h2 β (mkNel (ρ + 1) e) =
      mkNel (ρ + 1) ((lm (Up n c (ρ + 1)) (colE c (ρ + 1) β).val *
        rm (Up n c (ρ + 1)) (colE c (ρ + 1) β)⁻¹.val).mulVec e) := by
  rw [← mkNel_co (ρ + 1) (cjE ρ h1 h2 β (mkNel (ρ + 1) e))]
  congr 1
  funext a
  have hne : a.1.1 ≠ a.1.2 := fun h => by have := a.2; rw [h] at this; exact lt_irrefl _ this
  rw [← Matrix.mulVec_mulVec, ← mul_matrixExtendSelectedEntriesByZero_apply, ← extendAboveDiagonalEntries_mul_blockRespecting (ρ + 1) _ (colE_inv_val_eq_zero ρ β)]
  simp only [co, cjE_coe, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Units.mul_inv, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.mul_assoc]

theorem det_L (ρ : ℕ) (β : n → k) :
    (lm (Up n c (ρ + 1)) (colE c (ρ + 1) β).val * rm (Up n c (ρ + 1)) (colE c (ρ + 1) β)⁻¹.val).det = 1 := by
  rw [det_mul, det_lm, det_rm]
  rw [Finset.prod_eq_one fun s _ => det_block_unitri _ _ (colE_uni ρ β) _,
    Finset.prod_eq_one fun s _ => det_block_unitri _ _ (colE_inv_uni ρ β) _, mul_one]

end GlobalTheory.HaarR.CjVol

open GlobalTheory.HaarR.CjVol GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model in
theorem GlobalTheory.HaarR.map_volN_cjE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k), ν.IsAddHaarMeasure → ∀ β : n → k, (volN ν n c (ρ + 1)).map (cjE ρ h1 h2 β) = volN ν n c (ρ + 1) := by
  intro k _ _ _ _ _ _ n _ _ c ρ h1 h2 ν hν β
  exact map_volN_of_affine ν (ρ + 1) (cjE ρ h1 h2 β) _ (det_L ρ β) 0
    (fun e => by rw [add_zero]; exact cjE_mkNel ρ h1 h2 β e)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarFJInt

open GlobalTheory.RootEx.Radical

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def midLev (c ρ : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * ρ + 1) (fun i => 2 * (i.val + 1))

theorem uni_of_mem_N {ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c (ρ + 1)) :
    Uni (midLev c ρ) u.val := by
  rw [mem_N_iff] at hu
  intro r s hrs
  refine hu r s ?_
  rcases r with r | r <;> rcases s with s | s <;> simp only [midLev, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega

theorem uni_colE (ρ : ℕ) (β : n → k) : Uni (midLev c ρ) (colE c (ρ + 1) β).val := by
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [colE, upU, Matrix.one_apply]
  · simp only [midLev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : s.val ≠ ρ := by omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem uni_inl_inl {ρ : ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Uni (midLev c ρ) M) (i j : n) :
    M (Sum.inl i) (Sum.inl j) = (1 : Matrix n n k) i j := by
  rw [h _ _ (by simp [midLev])]
  simp [Matrix.one_apply]

theorem embX_mem_KO {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  have one_int : ∀ (i j : Fin c), (1 : Matrix (Fin c) (Fin c) k) i j ∈ 𝒪[k] := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [embX_val]
    rcases i with i | i <;> rcases j with j | j
    · exact hg.1 i j
    · exact zero_mem _
    · exact zero_mem _
    · exact one_int i j
  · rw [← map_inv, embX_val]
    rcases i with i | i <;> rcases j with j | j
    · exact hg.2 i j
    · exact zero_mem _
    · exact zero_mem _
    · exact one_int i j

theorem colE_mem_KO (p : ℕ) {β : n → k} (hβ : ∀ i, β i ∈ 𝒪[k]) : colE c p β ∈ KO k (n ⊕ Fin c) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  have one_int : ∀ {m : Type} [DecidableEq m] (i j : m), (1 : Matrix m m k) i j ∈ 𝒪[k] := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rcases i with i | i <;> rcases j with j | j
    · exact one_int i j
    · simp only [colE, upU, fromBlocks_apply₁₂, Matrix.of_apply]
      split_ifs
      · exact hβ i
      · exact zero_mem _
    · simp only [colE, upU, fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
    · exact one_int i j
  · rcases i with i | i <;> rcases j with j | j
    · exact one_int i j
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl i) (Sum.inr j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.of_apply]
      split_ifs
      · exact neg_mem (hβ i)
      · rw [neg_zero]; exact zero_mem _
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₂₂]; exact one_int i j

theorem embX_mul_inl {ρ : ℕ} (g : GL n k) (w : GL (n ⊕ Fin c) k) (hw : Uni (midLev c ρ) w.val) (i j : n) :
    (embX c g * w).val (Sum.inl i) (Sum.inl j) = g.val i j := by
  rw [Units.val_mul, embX_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [uni_inl_inl hw, Matrix.one_apply]

theorem mul_embX_inl {ρ : ℕ} (g : GL n k) (w : GL (n ⊕ Fin c) k) (hw : Uni (midLev c ρ) w.val) (i j : n) :
    (w * embX c g).val (Sum.inl i) (Sum.inl j) = g.val i j := by
  rw [Units.val_mul, embX_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [uni_inl_inl hw, Matrix.one_apply]

theorem col_eq {ρ : ℕ} (hρ : ρ < c) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c (ρ + 1)) (β : n → k) (t : n) :
    (u * colE c (ρ + 1) β).val (Sum.inl t) (Sum.inr ⟨ρ, hρ⟩) = β t := by
  have h1 := uni_inl_inl (uni_of_mem_N hu)
  have h0 : u.val (Sum.inl t) (Sum.inr ⟨ρ, hρ⟩) = 0 := by
    rw [mem_N_iff] at hu
    rw [hu _ _ (by simp [lev])]
    simp
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [colE, upU, h1, Matrix.one_apply, h0]

theorem mem_KO_iff_prod {ρ : ℕ} (hρ : ρ < c) (g : GL n k) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c (ρ + 1))
    (β : n → k) :
    embX c g * u * colE c (ρ + 1) β ∈ KO k (n ⊕ Fin c) ↔
      g ∈ KO k n ∧ u ∈ KO k (n ⊕ Fin c) ∧ ∀ i, β i ∈ 𝒪[k] := by
  constructor
  · intro hr
    have hw : Uni (midLev c ρ) (u * colE c (ρ + 1) β).val :=
      Uni.mul (uni_of_mem_N hu) (uni_colE ρ β)
    have hwi : Uni (midLev c ρ) ((u * colE c (ρ + 1) β)⁻¹).val := Uni.inv hw
    have hr' := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hr
    have hg : g ∈ KO k n := by
      rw [GlobalTheory.SplitFlip.mem_KO_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have := hr'.1 (Sum.inl i) (Sum.inl j)
        rwa [mul_assoc, embX_mul_inl g _ hw] at this
      · have := hr'.2 (Sum.inl i) (Sum.inl j)
        rwa [mul_assoc, _root_.mul_inv_rev, ← map_inv, mul_embX_inl g⁻¹ _ hwi] at this
    have hwK : u * colE c (ρ + 1) β ∈ KO k (n ⊕ Fin c) := by
      have := mul_mem (inv_mem (embX_mem_KO (c := c) hg)) hr
      rwa [mul_assoc, inv_mul_cancel_left] at this
    have hβ : ∀ i, β i ∈ 𝒪[k] := fun i => by
      have := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hwK).1 (Sum.inl i) (Sum.inr ⟨ρ, hρ⟩)
      rwa [col_eq hρ u hu β i] at this
    refine ⟨hg, ?_, hβ⟩
    have := mul_mem hwK (inv_mem (colE_mem_KO (c := c) (ρ + 1) hβ))
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨hg, huK, hβ⟩
    exact mul_mem (mul_mem (embX_mem_KO hg) huK) (colE_mem_KO _ hβ)

end GlobalTheory.HaarFJInt

open GlobalTheory.HaarFJInt in
theorem GlobalTheory.HaarFJInt.prodRFJ_preimage_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), ρ < c → prodRFJ (k := k) (n := n) (c := c) ρ ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = ((KO k n : Set (GL n k)) ×ˢ {u : N k n c (ρ + 1) | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)}) ×ˢ {β : n → k | ∀ i, β i ∈ 𝒪[k]} := by
  intro k _ _ _ _ n _ _ c ρ hρ
  ext ⟨⟨g, u⟩, β⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prodRFJ_coe, Set.mem_prod, SetLike.mem_coe]
  rw [mem_KO_iff_prod hρ g u u.2 β, and_assoc]
end
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Col GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top GlobalTheory.TopVal

namespace GlobalTheory.TopVal

def DatVal {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {G : Type} [Group G] [Fintype G]
    {Pl0 T : Type} {A : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [aK : Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) A Ks) (tup : T → I.ι) : Prop :=
  ∃ c : Val B →ₛₗ[B.embLL] R.cX.W,
    (∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
      GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = R.cX.ρ γ.1 (c v)) ∧
    ∀ (t : T) (φ : Frm I (tup t)) (x : A.fam.amb.FR t), IsRes φ x →
      ∀ (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') y, HasMat h y → IsUni B y →
        (R.HX t).e (R.jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h) = c (val φ (latOf I (tup t) y))

theorem matEq_of_hasMat {D : D7} {h : GA D D.sp.X'} {y} (hm : HasMat h y) :
    GlobalTheory.Mem.R3.MatEq (R3.matIn D.sp.X' 1 ((finHom D.sp.X').rangeRestrict h)) y := by
  refine ⟨Formalism.L2.Forms.rankP D, fun i j i' j' hi hj => ?_⟩
  have e1 : finCongr (Formalism.L2.Forms.rankP D) i = i' := Fin.ext hi
  have e2 : finCongr (Formalism.L2.Forms.rankP D) j = j' := Fin.ext hj
  rw [← e1, ← e2, ← hm.2 i j]
  unfold R3.matIn
  rw [mul_one]
  rfl



theorem datVal_rows (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : Bl.RowsT K w Z Wt p0) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := t.r.z.alg) t.r.z.R.toRealDat t.r.Y.tup := by
  obtain ⟨c, h1, h2, -, -⟩ := hs.1
  have h3 := t.r.z.pins.char.base.models.jX
  have h4 := t.r.z.lev.beta.2
  refine ⟨c, fun γ γE g hr hm v => h1 γ γE g hr hm v, fun s => ?_⟩
  have h5 : w.I.tup (t.r.Y.tup s) = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have key : ∀ (a : w.I.ι), w.I.tup a = s.1 → ∀ (φ : Frm w.I a) (x : (R3.famT t).A.fam.amb.FR s), IsRes φ x →
      ∀ (h : GA (w.D Z) (w.D Z).sp.X') y, HasMat h y → IsUni B y →
        t.r.z.R.B.jR s x ((finHom (w.D Z).sp.X').rangeRestrict h) = c (val φ (latOf w.I a y)) := by
    intro a ha
    obtain ⟨s, hs'⟩ := s
    change w.I.tup a = s at ha
    subst ha
    rintro φ x ⟨ok, hx⟩ h y hm hu
    have hx' : ((by with_unfolding_all exact ((mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a)).res ok φ :)) : (R3.famT t).A.fam.amb.FR ⟨w.I.tup a, hs'⟩) = x := by
      apply eq_of_heq
      exact (by with_unfolding_all exact (hx :))
    have hM := matEq_of_hasMat hm
    have e := h2 B.sp.cm ⟨w.I.tup a, hs'⟩ ⟨⟨ok⟩, φ⟩ ((finHom (w.D Z).sp.X').rangeRestrict h) ⟨y, hu⟩ (by rw [h4]; exact hM)
    have e2 := decoPt_mk B.sp.cm (B.R.N B.R.m - 1) ∅ (rowSG (B.primes w.px) w.I.sel (w.I.tup a)) ⟨y, hu⟩
    rw [← hx']
    refine Eq.trans ((by with_unfolding_all exact (e :))) (congrArg (fun d => c (val φ d)) e2)
  intro φ x hx h y hm hu
  exact (congrFun (h3 s x) _).trans (key _ h5 φ x hx h y hm hu)



theorem datVal_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := a.x.alg) a.x.R.toRealDat a.x.Y.tup := by
  have h := datVal_rows K B f T w Z Wt ex.p0 t hs
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  rw [← hT'] at h
  obtain ⟨c, h1, h2⟩ := h
  refine ⟨(by with_unfolding_all exact (c :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h2 :))


end GlobalTheory.TopVal
end

section

noncomputable section

namespace GlobalTheory.TopVal.DecoPt

section General

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix GlobalTheory.Mem.ColAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem hasRes_red {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) :
    HasRes P (algebraMap E _ a) (redP P a) := by
  obtain ⟨r, s, hs, h⟩ := id ha
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (redP P a)
  refine ⟨t, ht, ?_⟩
  have h1 := reduction_spec P hs h
  rw [← ht, ← map_mul, eq_comm, Ideal.Quotient.eq] at h1
  have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).2 h1
  have h3 : P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    le_antisymm (HeightOneSpectrum.valuation_le_one (K := E) P s)
      (not_lt.1 fun hl => hs ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).1 hl))
  have h4 : P.valuation E (algebraMap (𝓞 E) E s * (a - algebraMap (𝓞 E) E t)) < 1 := by
    rw [mul_sub, h, ← map_mul, ← map_sub]
    exact h2
  rw [map_mul, h3, one_mul] at h4
  rw [← map_sub, valued_algebraMap]
  exact h4

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g : GL (Fin n) (AfE F E)}

theorem adAt_pull {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) (x : Sp E n) (i : Fin n) :
    adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x i) = algebraMap E _ ((p.fr P).symm x i) := by
  have e : ratM P.1 (p.fr P) = locM P.1 g := Matrix.ext fun i j => (h.fr P i j).symm
  have h1 := ratM_mulVec (P := P.1) (p.fr P) ((p.fr P).symm x)
  rw [LinearEquiv.apply_symm_apply, e] at h1
  have h2 := congrFun (congrArg (fun v => locM P.1 g⁻¹ *ᵥ v) h1) i
  simp only [Matrix.mulVec_mulVec] at h2
  rw [← locM_mul, inv_mul_cancel, locM_one, Matrix.one_mulVec] at h2
  rw [h2]

  simp only [GlobalTheory.Mem.Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE, locM, Matrix.map_apply]

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST (uSG SG Q) ∅ :=
  ⟨(forgetFr p, fun _ => 1), fun P => absurd P.2 (Finset.notMem_empty _)⟩

theorem isPtOf_noFr {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) : IsPtOf hc g (noFr p) := by
  refine ⟨h.uni, h.lat, h.f, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  show HasRes _ _ ((forgetDeco p).be w x i)
  by_cases hw : w.1 ∈ SG
  · rw [forgetDeco_be_of_mem p w hw]
    exact h.be ⟨w.1, hw⟩ x hx i
  · have hs : (p.fr (rightOf w hw)).symm x ∈ stdAt E n w.1 := by
      refine (p.2 (rightOf w hw) _).1 ?_
      show p.fr (rightOf w hw) ((p.fr (rightOf w hw)).symm x) ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact le_locP _ _ hx
    have e : frBe w.1 (p.fr (rightOf w hw)) x = redV w.1 ((p.fr (rightOf w hw)).symm x) := if_pos hs
    rw [forgetDeco_be_of_not p w hw, e, adAt_pull h (rightOf w hw) x i]
    exact hasRes_red (mem_stdAt.1 hs i)

theorem decoOf_eq_forgetFr [NeZero n] {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    decoOf ST (uSG SG Q) g = forgetFr p :=
  Subtype.ext ((rlc_decoOf_val hc n ST (uSG SG Q) h.uni).trans (near_of_isPtOf (isPtOf_noFr h) 0).deco)

end General

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latOf_eq_toRow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X), I.Ok → ∀ (a : I.ι) (y : GlobalTheory.Mem.Col2.TC.GA B (B.R.N B.R.m - 1)) (p : GlobalTheory.Mem.Col2.XPt (B.primes X) B.R I.sel (I.tup a)), GlobalTheory.Mem.Col2.TC.PtOf y p → GlobalTheory.TopVal.latOf I a y = GlobalTheory.Mem.Col2.toRow I.sel (I.tup a) p := by
  intro B X I _ a y p h
  letI := GlobalTheory.Mem.Col2.starE B
  exact decoOf_eq_forgetFr (F := B.fields.F) (E := B.fields.E) h

end GlobalTheory.TopVal.DecoPt

end
end
