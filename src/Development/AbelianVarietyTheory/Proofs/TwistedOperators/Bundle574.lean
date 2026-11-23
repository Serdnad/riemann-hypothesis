module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle564
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvector
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor


open GlobalTheory.SplitLinear GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv in
open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm in
theorem om_placeModel_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (e a : AE D), IsSplitIdem D e → e + cA D e = idem D (.inl v) → (a = e ∨ a = cA D e) → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∃ r : ℝ, 0 < r ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = ((r : ℂ) * ((splitFacO χS χT x y : Circle) : ℂ)) • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ hW hB v e a he _ ha Tm hTm g h hg hh x y hx hy
  have orth : ∀ b : AE D, IsSplitIdem D b → GlobalTheory.PlaceModelSum.IsOrthSum b := fun b hb =>
    ⟨Unit, {()}, fun _ => b, fun _ _ => hb, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => b) ()).symm⟩
  have ho := orth e he
  rcases ha with ha | ha
  · rw [ha] at hTm ⊢
    refine ⟨modFac S T x y, modFac_pos S T x y, fun Φ hΦ => ?_⟩
    rw [law_orth hW hB.2.2.1 hB.2.2.2.1 ho he.2.1 (base_theta hB) hB.2.2.2.2.2.lat one_ne_zero hTm hg hh hx hy Φ hΦ,
      fac, mul_comm]
  · rw [ha] at hTm ⊢
    have ho' := ho.conj
    have sc : ∀ (V : HSp D) (k : GA D V), SuppAt e V k → SuppAt (cA D e) V k := fun V k hk i j => by
      rw [GlobalTheory.SplitOnto.cA_cA, add_comm]; exact hk i j
    have dx := det_conj ho'.idem hx
    have dy := det_conj ho'.idem hy
    refine ⟨modFac S T (detAt _ ho'.idem S g) (detAt _ ho'.idem T h), modFac_pos S T _ _, fun Φ hΦ => ?_⟩
    rw [law_orth hW hB.2.2.1 hB.2.2.2.1 ho' (by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, he.2.1]) (base_theta hB)
      hB.2.2.2.2.2.lat one_ne_zero hTm (sc S g hg) (sc T h hh) (isDetAt_detAt _ ho'.idem S g)
      (isDetAt_detAt _ ho'.idem T h) Φ hΦ, fac, mul_comm, splitFacO, splitFacO,
      GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resT _ _ dx, GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resS _ _ dy]

end GlobalTheory.PlaceTensor
end

section

open Formalism.IndefR.Datum Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

namespace GlobalTheory.PlusDetONB

open GlobalTheory.CompactFockAction GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

def sgnP {k : ℕ} (p : ℕ) : Fin k → Bool := fun a => decide (a.val < p)

theorem onb_facts {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    B * B⁻¹ = 1 ∧ B⁻¹ * B = 1 ∧ s = B * Formalism.REAL.Jm (sgnP p) * B⁻¹ := by
  obtain ⟨ε, hε, hG, hs⟩ := h
  have hd : Matrix.diagonal (fun a => (ε a : ℂ)) = Formalism.REAL.Jm (sgnP (k := k) p) := by
    unfold Formalism.REAL.Jm sgnP
    congr 1
    funext a
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · have : ¬ a.val < p := by omega
      simp [h1, this]
  have hsq : Matrix.diagonal (fun a => (ε a : ℂ)) * Matrix.diagonal (fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hsq
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hB : B.det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hG, Matrix.det_mul, h0, mul_zero]
  have hU : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hU
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hU
  refine ⟨h1, h2, ?_⟩
  rw [← hd, ← hs, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem isBlock_of_isKMat {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) : IsBlock (sgnP p) κ := by
  intro i j hij
  apply h.2 i j
  intro hiff
  apply hij
  unfold sgnP
  exact decide_eq_decide.2 hiff

theorem card_sgnP {k p : ℕ} (hp : p ≤ k) (e : Bool) :
    (Finset.univ.filter fun i : Fin k => sgnP p i = e).card = if e then p else k - p := by
  have h1 : (Finset.univ.filter fun i : Fin k => i.val < p).card = p := by
    rw [Fin.card_filter_val_lt]; omega
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (p := fun i : Fin k => i.val < p)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  cases e
  · simp only [sgnP, decide_eq_false_iff_not, Bool.false_eq_true, if_false]
    omega
  · simp only [sgnP, decide_eq_true_eq, if_true]
    exact h1

theorem signBlockDeterminant_positive_eq {k p : ℕ} (κ : Matrix (Fin k) (Fin k) ℂ) : signBlockDeterminant (sgnP p) true κ = detPos p κ := by
  unfold signBlockDeterminant detPos
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (fun a : Fin k => (by simp [sgnP] : sgnP p a = true ↔ a.val < p)))]
  rfl

theorem signBlockDeterminant_negative_eq {k p : ℕ} (κ : Matrix (Fin k) (Fin k) ℂ) : signBlockDeterminant (sgnP p) false κ = detNeg p κ := by
  unfold signBlockDeterminant detNeg
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (fun a : Fin k => (by simp [sgnP] : sgnP p a = false ↔ ¬ a.val < p)))]
  rfl

theorem detPlus_onb : ∀ {n m : ℕ} (GS sS BS κS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT κT : Matrix (Fin m) (Fin m) ℂ)
    (pS pT : ℕ), pS ≤ n → pT ≤ m → IsONBasis GS sS BS pS → IsONBasis GT sT BT pT → IsKMat pS κS → IsKMat pT κT →
    GlobalTheory.WeilParts.detPlus sS sT (BS * κS * BS⁻¹)⁻¹ (BT * κT * BT⁻¹) =
      detPos pT κT ^ pS * detNeg pT κT ^ (n - pS) * (detPos pS κS ^ pT)⁻¹ * (detNeg pS κS ^ (m - pT))⁻¹ := by
  intro n m GS sS BS κS GT sT BT κT pS pT hpS hpT hBS hBT hκS hκT
  obtain ⟨h1S, h2S, hsS⟩ := onb_facts hBS
  obtain ⟨h1T, h2T, hsT⟩ := onb_facts hBT
  have hu : κS * κSᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκS.1
  have hinv : (BS * κS * BS⁻¹)⁻¹ = BS * κSᴴ * BS⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    calc BS * κS * BS⁻¹ * (BS * κSᴴ * BS⁻¹) = BS * (κS * (BS⁻¹ * BS) * κSᴴ) * BS⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2S, Matrix.mul_one, hu, Matrix.mul_one, h1S]
  rw [hinv, hsS, hsT, detPlus_conj h2S h2T]
  have bS := isBlock_of_isKMat hκS
  have bT := isBlock_of_isKMat hκT
  have bS' : IsBlock (sgnP pS) κSᴴ := fun i j e => by
    rw [Matrix.conjTranspose_apply, bS j i (Ne.symm e), star_zero]
  rw [detPlus_block bS' bT, prod_bool _ fun e => signBlockDeterminant (sgnP pS) e κSᴴ,
    prod_bool _ fun e => signBlockDeterminant (sgnP pT) e κT, card_sgnP hpT, card_sgnP hpT, card_sgnP hpS, card_sgnP hpS]
  have ih := fun e => signBlockDeterminant_mul_eq_one_of_mul_eq_one e bS hu
  rw [eq_inv_of_mul_eq_one_right (ih true), eq_inv_of_mul_eq_one_right (ih false)]
  simp only [if_true, Bool.false_eq_true, if_false, signBlockDeterminant_positive_eq, signBlockDeterminant_negative_eq, inv_pow]
  ring

end GlobalTheory.PlusDetONB
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowUnf

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem frameMat_isom (d : HermitianOrthogonalExtensionData A B c ε) : (frameMat B A d.ι)ᴴ * B.gram * frameMat B A d.ι = A.gram :=
  GlobalTheory.ChiGrid.SumDual.gram_isom A B d.ι d.isom

theorem perp_sub (d : HermitianOrthogonalExtensionData A B c ε) {k : ℕ} (f : Fin k → Fin c) :
    (frameMat B A d.ι)ᴴ * B.gram * d.a.submatrix id f = 0 := by
  refine Matrix.ext fun i j => ?_
  exact congrFun (congrFun d.perp i) (f j)

theorem gram_sub' (d : HermitianOrthogonalExtensionData A B c ε) {k l : ℕ} (f : Fin k → Fin c) (g : Fin l → Fin c) :
    (d.a.submatrix id f)ᴴ * B.gram * d.a.submatrix id g = (antiDiagonalSignGramMatrix c ε).submatrix f g :=
  d.gram_sub f g

def jacDec {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ) : HypDec B A σ where
  e := d.iso σ (by omega)
  e' := d.a.submatrix id fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev
  i₀ := frameMat B A d.ι
  ee := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e' := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hj : (j : ℕ) + 1 ≤ c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hsub : c - ((i : ℕ) + 1) + (i : ℕ) + 1 = c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  iso := frameMat_isom d
  i₀e := perp_sub d _
  i₀e' := perp_sub d _
  rank_add := by have := d.rank; omega

def midCol {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) : Matrix (Fin B.rank) (Fin 1) D.host.E :=
  d.a.submatrix id fun _ : Fin 1 => (⟨σ, by omega⟩ : Fin c)

def coreMat {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) :
    Matrix (Fin B.rank) (Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank) D.host.E :=
  (Matrix.fromCols (frameMat B A d.ι) (midCol d h)).submatrix id finSumFinEquiv.symm

theorem nLine_gram (i j : Fin 1) : (GlobalTheory.SeeSaw.Model.nLine D).gram i j = -1 := by
  show -((Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram i j) = -1
  rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
  simp [Examples₂.sgn]

theorem perp_sub' (d : HermitianOrthogonalExtensionData A B c ε) {k : ℕ} (f : Fin k → Fin c) :
    (d.a.submatrix id f)ᴴ * B.gram * frameMat B A d.ι = 0 := by
  have h := congrArg conjTranspose (perp_sub d f)
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at h

theorem coreMat_gram {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    (coreMat d h)ᴴ * B.gram * coreMat d h = (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).gram := by
  have hNN : (midCol d h)ᴴ * B.gram * midCol d h = (GlobalTheory.SeeSaw.Model.nLine D).gram := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => (?_ : _ = (-1 : D.host.E)).trans (nLine_gram i j).symm)
    simp only [submatrix_apply, antiDiagonalSignGramMatrix]
    rw [if_pos (by omega), if_true]
  have key : (Matrix.fromCols (frameMat B A d.ι) (midCol d h))ᴴ * B.gram * Matrix.fromCols (frameMat B A d.ι) (midCol d h) =
      Matrix.fromBlocks A.gram 0 0 (GlobalTheory.SeeSaw.Model.nLine D).gram := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, frameMat_isom,
      hNN]
    rw [show (frameMat B A d.ι)ᴴ * B.gram * midCol d h = 0 from perp_sub d _,
      show (midCol d h)ᴴ * B.gram * frameMat B A d.ι = 0 from perp_sub' d _]
    rfl
  refine Matrix.ext fun i j => ?_
  rw [GlobalTheory.Doubling.gram_hsum]
  exact congrFun (congrFun key _) _

theorem coreMat_perp {σ k : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) (f : Fin k → Fin c) (hf : ∀ i, (f i).1 + σ + 1 ≠ c) :
    (coreMat d h)ᴴ * B.gram * d.a.submatrix id f = 0 := by
  have key : (Matrix.fromCols (frameMat B A d.ι) (midCol d h))ᴴ * B.gram * d.a.submatrix id f = 0 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul, perp_sub]
    rw [show (midCol d h)ᴴ * B.gram * d.a.submatrix id f = 0 from (gram_sub' d _ _).trans (Matrix.ext fun i j => by
      simp only [submatrix_apply, antiDiagonalSignGramMatrix, Matrix.zero_apply]
      rw [if_neg (by have := hf j; omega)])]
    exact fromRows_zero
  refine Matrix.ext fun i j => ?_
  exact congrFun (congrFun key _) j

def besDec {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) : HypDec B (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)) σ where
  e := d.iso σ (by omega)
  e' := d.a.submatrix id fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev
  i₀ := coreMat d h
  ee := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e' := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hj : (j : ℕ) + 1 ≤ c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hsub : c - ((i : ℕ) + 1) + (i : ℕ) + 1 = c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  iso := coreMat_gram d h
  i₀e := coreMat_perp d h _ fun i => by have := i.2; simp only [Fin.val_castLE]; omega
  i₀e' := coreMat_perp d h (fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev) fun i => by
    have := i.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  rank_add := by have := d.rank; show A.rank + 1 + 2 * σ = B.rank; omega

section Grid

open GlobalTheory.FunObj

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem cocpt_top {j : ℕ} (hj : j ≤ D.R.m) : CoCpt (G.V (.top j)) := by
  have h := G.isV (X := .top j) hj fun i e => by cases e
  refine GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite h.sigOK fun τ => Or.inl ?_
  rw [h.sig τ, h.rank]
  simp [Node.neg]

def rowBes (j : ℕ) (hj : j < D.R.m) (σ : ℕ) (h : D.R.m - 1 - j = 2 * σ + 1) :
    HypDec (G.V (.grid D.R.m j)) (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ :=
  besDec (G.rowDec j hj) h

def rowJac (j : ℕ) (hj : j < D.R.m) (σ : ℕ) (h : D.R.m - 1 - j = 2 * σ) : HypDec (G.V (.grid D.R.m j)) (G.V (.top j)) σ :=
  jacDec (G.rowDec j hj) h

def topVolN (M : Vol G) (hM : M.IsRow) (hj : 0 < D.R.m) (h : D.R.m - 1 - 0 = 2 * ((D.R.m - 2) / 2) + 1) :
    VolN (rowBes G 0 hj ((D.R.m - 2) / 2) h) :=
  ⟨M.νN, M.fdN, hM.unip⟩

end Grid

end GlobalTheory.RowUnf
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vacuum_fixed_nonsplit_place_of_characterFrame : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε := by
  first | exact @GlobalTheory.StepLaw.fixesVacAt_nonsplit_of_charFrame | exact GlobalTheory.StepLaw.fixesVacAt_nonsplit_of_charFrame | (intros; apply GlobalTheory.StepLaw.fixesVacAt_nonsplit_of_charFrame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.OrbitAny

open GlobalTheory.FinPl.SplitOrbit

theorem orbitAny : ∀ (D : D7) (V₀ A L : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (L₀ : Lat V₀) (LA : Lat A) (LL : Lat L) (v : GlobalTheory.FinPl.Pl D), IsSelfDualC V₀ L₀ → IsSelfDualC A LA → IsSelfDualC L LL → OrthAt o L₀ LA LL v → ∀ γ ∈ grpAt V₀ (· = v), (∀ a : AE D, a • ratV (vecB o ζ) ∈ latA V₀ L₀ (· = v) → mt V₀ γ⁻¹ *ᵥ (a • ratV (vecB o ζ)) ∈ latA V₀ L₀ (· = v)) → ∃ a ∈ grpAt A (· = v), ∃ κ, InK V₀ L₀ (· = v) κ ∧ γ = o.emb (a, 1) * κ := by
  intro D V₀ A L o ζ hζ L₀ LA LL v hL₀ hLA hLL hO γ hγ hz
  have hT := GlobalTheory.FinPl.TamePlaces.tame D v
  have hM := isSDAt_pre_unitary (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D V₀ L₀ v hL₀) γ⁻¹
  obtain ⟨hA, hsplit⟩ := split_of_le o hM (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D L LL v hLL) (line_le o hζ hO _ hz)
  obtain ⟨a, ha, hmv⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D A v _ _ hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D A LA v hLA) hA
  exact ⟨a, ha, (o.emb (a, 1))⁻¹ * γ, ⟨mul_mem (inv_mem (emb_mem_grpAt o ha)) hγ,
    moves_of_split o hO γ a hsplit hmv⟩, (mul_inv_cancel_left _ _).symm⟩

end GlobalTheory.AscFin.OrbitAny

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.ConjPlaceLat



theorem cA_mul_mem_latV_smul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w →
  ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (𝔪 : Ideal (𝓞 D.host.E)), (∃ m ∈ 𝔪, m ∉ (Formalism.DivisionValues.conjPl w).asIdeal) →
  ∀ z : Fin S.rank → AE D, z ∈ latV S L (· = p.v) → (fun i => cA D p.e * z i) ∈ latV S (𝔪 • L) (· = p.v) := by
  intro D k _ _ _ _ p w hw S L 𝔪 hm z hz
  obtain ⟨m, hm𝔪, hmw⟩ := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmw (Ideal.zero_mem _)
  have hmE : (m : D.host.E) ≠ 0 := by exact_mod_cast hm0
  have hc := GlobalTheory.SplitHeckeAdj.idem_conj S hw
  have hu : finPart D (cA D p.e * incA D ((m : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hmw ((hc.2 m hm0).2 h)
  have h1 : ∀ y ∈ latV S L (· = p.v), (fun i => incA D (m : D.host.E) * y i) ∈ latV S (𝔪 • L) (· = p.v) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      refine AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, m • x, Submodule.smul_mem_smul hm𝔪 hx, ?_⟩
      funext i
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (m : D.host.E) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul, Pi.smul_apply, Algebra.smul_def]
    | zero =>
      convert zero_mem (latV S (𝔪 • L) (· = p.v)) using 1
      funext i
      simp
    | add y y' _ _ h h' =>
      convert add_mem h h' using 1
      funext i
      simp [mul_add]
    | neg y _ h =>
      convert neg_mem h using 1
      funext i
      simp
  have key : (fun i => cA D p.e * z i) =
      fun i => cA D p.e * incA D ((m : D.host.E)⁻¹) * (incA D (m : D.host.E) * z i) := by
    funext i
    rw [mul_assoc, ← mul_assoc (incA D _), ← map_mul, inv_mul_cancel₀ hmE, map_one, one_mul]
  rw [key]
  exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hu (h1 z hz)

end GlobalTheory.ConjPlaceLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  first | exact @GlobalTheory.CenAvgOne.exists_central_average_one | exact GlobalTheory.CenAvgOne.exists_central_average_one | (intros; apply GlobalTheory.CenAvgOne.exists_central_average_one <;> assumption)
end
