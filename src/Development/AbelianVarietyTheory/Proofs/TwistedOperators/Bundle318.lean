module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle352
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle300
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexLevelSelfDualStabilizerEqProdLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle052
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubBoth

open GlobalTheory.FockSubst GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex

theorem unitMap_mul_both {m n : ℕ} (B k : Matrix (Fin n) (Fin n) ℂ) (B' k' : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (c : Fin n) : unitMap (B * k) (B' * k') a c =
      ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • unitMap B B' b.1 b.2 := by
  unfold unitMap
  rw [Matrix.mul_inv_rev]
  have key : k' * single a c (1 : ℂ) * k⁻¹ = ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • single b.1 b.2 (1 : ℂ) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq,
      Finset.sum_ite_eq', ite_mul, zero_mul]
  calc B' * k' * single a c (1 : ℂ) * (k⁻¹ * B⁻¹) = B' * (k' * single a c (1 : ℂ) * k⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]

theorem onb_sign {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsUnit B.det ∧ s * B = B * Matrix.diagonal (fun a : Fin k => if a.val < p then (1 : ℂ) else -1) := by
  obtain ⟨ε, hε, hG, hs⟩ := h
  have hdiag : (diagonal fun a => ((ε a : _) : ℂ)) = diagonal fun a : Fin k => if a.val < p then (1 : ℂ) else -1 := by
    congr 1
    funext a
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · simp [h1, not_lt.mpr h2]
  refine ⟨?_, hs.trans (by rw [hdiag])⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, h0, mul_zero, hdiag, Matrix.det_diagonal] at hd
  have : ∀ a ∈ (Finset.univ : Finset (Fin k)), (if a.val < p then (1 : ℂ) else -1) ≠ 0 := by
    intro a _
    split_ifs <;> norm_num
  exact (Finset.prod_ne_zero_iff.mpr this) hd.symm

theorem cplxO_unitMap_both {m n : ℕ} {G s B : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} (h : IsONBasis G s B p)
    {G' s' B' : Matrix (Fin m) (Fin m) ℂ} {p' : ℕ} (h' : IsONBasis G' s' B' p') (i : Fin m) (j : Fin n) :
    cplxO s s' (unitMap B B' i j) =
      ((if decide (i.val < p' ↔ j.val < p) then 1 else -1 : ℂ) * I) • unitMap B B' i j := by
  obtain ⟨hB, hs⟩ := onb_sign h
  obtain ⟨-, hs'⟩ := onb_sign h'
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hBi : B⁻¹ * s = diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * s * (B * B⁻¹) := by rw [hBB, Matrix.mul_one]
      _ = B⁻¹ * (s * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹ := by rw [hs]
      _ = _ := by rw [← Matrix.mul_assoc B⁻¹, hinv, Matrix.one_mul]
  have e1 : s' * (B' * single i j (1 : ℂ) * B⁻¹) * s =
      B' * (diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) *
        diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹ := by
    calc s' * (B' * single i j (1 : ℂ) * B⁻¹) * s = (s' * B') * single i j (1 : ℂ) * (B⁻¹ * s) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hs', hBi]; simp only [Matrix.mul_assoc]
  have e2 : diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) *
      diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) =
      ((if i.val < p' then (1 : ℂ) else -1) * (if j.val < p then (1 : ℂ) else -1)) • single i j (1 : ℂ) := by
    ext x y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hxy : i = x ∧ j = y
    · rw [if_pos hxy]
      obtain ⟨rfl, rfl⟩ := hxy
      ring
    · rw [if_neg hxy]
      ring
  unfold cplxO unitMap
  rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  by_cases hi : i.val < p' <;> by_cases hj : j.val < p <;> simp [hi, hj]

theorem isKMat_inv_zero {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) {i j : Fin k}
    (hij : ¬ (i.val < p ↔ j.val < p)) : κ⁻¹ i j = 0 := by
  obtain ⟨hu, hz⟩ := h
  have hinv : κ⁻¹ = star κ := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  rw [hinv, Matrix.star_apply, hz j i (fun h' => hij h'.symm), star_zero]

theorem pureTensorO_fockSub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), BS' τ = BS τ * κS → BT' τ = BT τ * κT → (∀ ρ, ρ ≠ τ → BS' ρ = BS ρ ∧ BT' ρ = BT ρ) → ∀ P, pureTensorO ψ θ S T sS sT BS' BT' f P = pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  intro D ψ θ S T hψ hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hkS hkT BS' BT' hS hT hne P
  classical
  obtain ⟨-, hkTz⟩ := hkT
  have hτ : ∀ (i : Fin T.rank) (j : Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS' τ) (BT' τ) i j) g =
      ∑ b : Fin T.rank × Fin S.rank, (if (i.val < pT τ ↔ j.val < pS τ) then κT b.1 i * κS⁻¹ j b.2
          else starRingEnd ℂ (κT b.1 i * κS⁻¹ j b.2)) •
        aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS τ) (BT τ) b.1 b.2) g := by
    intro i j g hg
    rw [hS, hT, unitMap_mul_both, GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hg (decide (b.1.val < pT τ ↔ b.2.val < pS τ)) _
      (cplxO_unitMap_both (hoS τ) (hoT τ) b.1 b.2)]
    congr 1
    by_cases hw : κT b.1 i * κS⁻¹ j b.2 = 0
    · rw [hw]
      simp
    · have h1 : (b.1.val < pT τ ↔ i.val < pT τ) := by
        by_contra hc
        exact hw (by rw [hkTz b.1 i hc, zero_mul])
      have h2 : (j.val < pS τ ↔ b.2.val < pS τ) := by
        by_contra hc
        exact hw (by rw [isKMat_inv_zero hkS hc, mul_zero])
      by_cases hc : (i.val < pT τ ↔ j.val < pS τ)
      · have hd : decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true := by
          rw [decide_eq_true_iff, h1, ← h2]
          exact hc
        rw [if_pos hd, if_pos hc]
      · have hd : ¬ decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true := by
          rw [decide_eq_true_iff, h1, ← h2]
          exact hc
        rw [if_neg hd, if_neg hc]
  have key := GlobalTheory.FockSubst.pure_subst (ι := FVar D T.rank S.rank) (X := WO S T) (κ := Fin T.rank × Fin S.rank)
    (A := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2))
    (A' := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS' k.1) (BT' k.1) k.2.1 k.2.2))
    (P := IsThetaFunO ψ S T)
    (fun g g' hg hg' => GlobalTheory.OrientedHeis.theta_add hg hg')
    (fun a g hg => GlobalTheory.OrientedHeis.theta_smul a hg)
    (fun k g hg => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ hg)
    (fun k l g hg => GlobalTheory.FockSubst.aPlus_comm hψ hθ _ _ hcS hcT _ _ hg)
    (fun k g g' hg hg' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ hg hg')
    (fun k a g hg => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a hg)
    (fun k g hg => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ hg)
    (fun k l g hg => GlobalTheory.FockSubst.aPlus_comm hψ hθ _ _ hcS hcT _ _ hg)
    (fun k g g' hg hg' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ hg hg')
    (fun k a g hg => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a hg)
    (fun v b => if v.1 = τ then
        (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2
          else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2))
        else (if b = (v.2.1, v.2.2) then 1 else 0))
    (fun v b => (v.1, b.1, b.2))
    (by
      rintro ⟨ρ, i, j⟩ g hg
      dsimp only
      by_cases hρ : ρ = τ
      · subst hρ
        simp only [if_true]
        exact hτ i j g hg
      · obtain ⟨h1, h2⟩ := hne ρ hρ
        simp [hρ, h1, h2, ite_smul])
    hf P
  have hsub : (MvPolynomial.aeval fun v : FVar D T.rank S.rank => ∑ b : Fin T.rank × Fin S.rank,
      (if v.1 = τ then
        (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2
          else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2))
        else (if b = (v.2.1, v.2.2) then 1 else 0)) •
        (MvPolynomial.X (v.1, b.1, b.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P =
      fockSub τ (pS τ) (pT τ) κS κT P := by
    unfold fockSub
    congr 2
    funext y
    obtain ⟨ρ, i, j⟩ := y
    by_cases hρ : ρ = τ
    · subst hρ
      simp only [if_true, Fintype.sum_prod_type, MvPolynomial.smul_eq_C_mul]
    · simp [hρ, ite_smul]
  unfold pureTensorO aPlusAll
  beta_reduce
  rw [key, hsub]

end GlobalTheory.FockSubBoth
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

variable {D : D7}

section Rescale

variable {S S₀ : HSp D} {ρ : ℕ}

theorem sandwich {m n : ℕ} (A : Matrix (Fin S.rank) (Fin m) D.host.E) (B : Matrix (Fin S.rank) (Fin n) D.host.E)
    (P : Matrix (Fin m) (Fin m) D.host.E) (Q : Matrix (Fin n) (Fin n) D.host.E) :
    (A * P)ᴴ * S.gram * (B * Q) = Pᴴ * (Aᴴ * S.gram * B) * Q := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def diagDec (d : HypDec S S₀ ρ) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) : HypDec S S₀ ρ where
  e := d.e * diagonal l
  e' := d.e' * diagonal fun a => (star (l a))⁻¹
  i₀ := d.i₀
  ee := by rw [sandwich, d.ee, Matrix.mul_zero, Matrix.zero_mul]
  e'e' := by rw [sandwich, d.e'e', Matrix.mul_zero, Matrix.zero_mul]
  e'e := by
    rw [sandwich, d.e'e, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one, Matrix.diagonal_eq_diagonal_iff]
    intro a
    simpa only [Pi.star_apply, star_inv₀, star_star] using inv_mul_cancel₀ (hl a)
  iso := d.iso
  i₀e := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
  i₀e' := by rw [← Matrix.mul_assoc, d.i₀e', Matrix.zero_mul]
  rank_add := d.rank_add

theorem perp_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0)
    (x : Fin S.rank → D.host.E) (hx : ((e * diagonal l)ᴴ * S.gram).mulVec x = 0) : (eᴴ * S.gram).mulVec x = 0 := by
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← mulVec_mulVec] at hx
  funext j
  have := congrFun hx j
  rw [mulVec_diagonal] at this
  simp only [Pi.zero_apply, Pi.star_apply, mul_eq_zero, star_eq_zero] at this
  rcases this with h | h
  · exact absurd h (hl j)
  · exact h

theorem flagGen_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) (g : GA D S)
    (hg : (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => e k i) = (e.map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = (e.map (incA D)).mulVec a) :
    (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => (e * diagonal l) k i) = ((e * diagonal l).map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = ((e * diagonal l).map (incA D)).mulVec a := by
  have hmv : ∀ a : Fin ρ → AE D, ((e * diagonal l).map (incA D)).mulVec (fun j => incA D (l j)⁻¹ * a j) =
      (e.map (incA D)).mulVec a := fun a => by
    funext k
    simp only [mulVec, dotProduct, Matrix.map_apply, mul_diagonal]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc, ← mul_assoc (incA D (l j)), ← map_mul, mul_inv_cancel₀ (hl j), map_one, one_mul]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := hg.1 i
    refine ⟨fun j => incA D (l j)⁻¹ * (incA D (l i) * a j), fun j hj => ?_, ?_⟩
    · show incA D (l j)⁻¹ * (incA D (l i) * a j) = 0
      rw [ha0 j hj, mul_zero, mul_zero]
    have hcol : (ratV fun k => (e * diagonal l) k i) = incA D (l i) • ratV fun k => e k i := by
      funext k
      show incA D ((e * diagonal l) k i) = incA D (l i) * incA D (e k i)
      rw [mul_diagonal, map_mul, mul_comm]
    rw [hcol, mulVec_smul, ha, ← mulVec_smul, ← hmv]
    rfl
  · have h1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) = (e * diagonal l)ᴴ := rfl
    have h2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e = eᴴ := rfl
    rw [h1] at hx
    obtain ⟨a, ha⟩ := hg.2 x (by rw [h2]; exact perp_diag l hl x hx)
    exact ⟨_, ha.trans (hmv a).symm⟩

theorem nFlag_diag (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) :
    NFlag S (e * diagonal l) = NFlag S e := by
  have hl' : ∀ a, (l a)⁻¹ ≠ 0 := fun a => inv_ne_zero (hl a)
  have e0 : diagonal l * diagonal (fun a => (l a)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (hl a)
  have e1 : e * diagonal l * diagonal (fun a => (l a)⁻¹) = e := by
    rw [Matrix.mul_assoc, e0, Matrix.mul_one]
  unfold NFlag
  congr 1
  ext g
  refine ⟨fun h => ?_, fun h => flagGen_diag l hl g h⟩
  have := flagGen_diag (e := e * diagonal l) (fun a => (l a)⁻¹) hl' g h
  rwa [e1] at this

def trMeas {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) : Measure N' := h ▸ ν

def trSet {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (𝓝 : Set N) : Set N' := h ▸ 𝓝

theorem isUnit_trans {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) (𝓝 : Set N)
    (hu : ν.IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν ∧ ν 𝓝 = 1) :
    (trMeas h ν).IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N') (trSet h 𝓝) (trMeas h ν) ∧
      trMeas h ν (trSet h 𝓝) = 1 := by
  subst h
  exact hu

def volNOf {S₀' : HSp D} {ρ' : ℕ} {d : HypDec S S₀ ρ} {d' : HypDec S S₀' ρ'} (h : NFlag S d.e = NFlag S d'.e)
    (v : VolN d) : VolN d' :=
  ⟨trMeas h v.ν, trSet h v.𝓝, isUnit_trans h v.ν v.𝓝 v.unit⟩

end Rescale

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj

variable {T : Type}

noncomputable def splitFam {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z), (p.comp q).Fam S → p.Fam S × q.Fam S
  | _, .nil, d => (d, ())
  | _, .snoc _ q, d => ((splitFam q d.1).1, ((splitFam q d.1).2, d.2))

theorem all_splitFam {S : Arrow T → Type} (P : ∀ a, S a → Prop) {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : (p.comp q).Fam S), Path.Fam.All P d →
      Path.Fam.All P (splitFam q d).1 ∧ Path.Fam.All P (splitFam q d).2
  | _, .nil, _, h => ⟨h, trivial⟩
  | _, .snoc _ q, d, h => ⟨(all_splitFam P q d.1 h.1).1, (all_splitFam P q d.1 h.1).2, h.2⟩

noncomputable def getD {S : Arrow T → Type} (t : T) (i : ℕ) : ∀ (n : ℕ), (downPath t i n).Fam S → ∀ j, j < n → S (.down t i j)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, j, h =>
    if hj : j < n then getD t i n (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).2 j hj
    else (show n = j by omega) ▸ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1.2

theorem getD_all {S : Arrow T → Type} (P : ∀ a, S a → Prop) (t : T) (i : ℕ) :
    ∀ (n : ℕ) (d : (downPath t i n).Fam S), Path.Fam.All P d → ∀ j (h : j < n), P (.down t i j) (getD t i n d j h)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, hd, j, h => by
    have hs := all_splitFam P (p := Path.one (.down t i n)) (downPath t i n) d hd
    unfold getD
    split_ifs with hj
    · exact getD_all P t i n _ hs.2 j hj
    · have hnj : n = j := by omega
      subst j
      change P (.down t i n) (splitFam (downPath t i n) d).1.2
      exact hs.1.2

end GlobalTheory.RowChain
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.exists_int_level_schwartzBruhat_finiteAdelic : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x u : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) v ∈ v.adicCompletionIntegers F) →
      g (x + u) = g x := by
  first | exact @GlobalTheory.SBLevel.exists_int_level | exact GlobalTheory.SBLevel.exists_int_level | (intros; apply GlobalTheory.SBLevel.exists_int_level <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)


theorem _root_.GlobalTheory.T.relIndex_level_selfDual_stabilizer_eq_prod_local : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), GlobalTheory.Hk3.Core R F → P = LevelP.ofLocal Hl cl → (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) = (∏ PP ∈ R.Pg.attach, (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / ((Nat.card (Hl PP) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP.1)) : ℝ) * (Nat.card (kP PP.1) : ℝ) ^ (D.R.r * D.R.t))) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) := by
  first | exact @GlobalTheory.ParIndex.relIndex_levV_latLev | exact GlobalTheory.ParIndex.relIndex_levV_latLev | (intros; apply GlobalTheory.ParIndex.relIndex_levV_latLev <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOpFace

theorem heckeOp_face_to_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (b : Bool) (i : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (B : Finset (GA D (Wc D i))), Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) SF P d B → Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF b i P d B hB
  have hS : OffS D SF P := by
    obtain ⟨_, _, _, _, hS, -⟩ := hB
    exact hS
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.1 SF hSF P).1 hS
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hPP : ∀ L : LevelP R.Pg D.R.r ℂ, ∀ PP, PP ∈ (R.datWp i L).Pg ∨ PP ∈ (R.datWp i L).Q →
      PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := fun L PP h =>
    hG PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  have h1 := ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n)
    (R.datWp i (R.levL F b (sg0 D A))) hβ P hN (hPP _)).2.1 SF d B).1 hB
  exact ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P hN (hPP _)).2.1 SF d B).2 h1

end GlobalTheory.LevOpFace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ThInv

theorem fvec_val_inv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (h : GA D S) (B : C.Bas), C.IsB B → ∀ u : WO S T → ℂ, C.IsTh u → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, (∀ γ ∈ GQ T, ∀ g, om (h, γ * g) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) ∧ ((∀ k, C.LevK Lv k 1 → om (1, k) u = u) → ∀ k, C.LevK Lv k 1 → ∀ g, om (h, g * k) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) := by
  intro D S T C om hW Lv h B hB u hu Q
  have hth : C.IsTh (C.fvec B u Q) := (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u hu Q).1
  refine ⟨fun γ hγ g => ?_, fun hk k hkL g => ?_⟩
  · have p : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [p, map_mul, Module.End.mul_apply]
    exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hth)
  · have p : ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) := by
      rw [Prod.mk_mul_mk, mul_one]
    have hmv := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.2.2.2.2 k
    rw [p, map_mul, Module.End.mul_apply, GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) k u hu B hB Q,
      hmv.2.2.1 hkL.1, hk k hkL]

end GlobalTheory.Ker.ThInv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_realPoint_standardSource_unitaryComponents : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (v : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (v τ)ᴴ * v τ = 1) → ∃ h ∈ GinfC S, ∀ τ, compAt C.θ τ (mt S h) = v τ := by
  first | exact @GlobalTheory.StdRealLift.exists_real_point | exact GlobalTheory.StdRealLift.exists_real_point | (intros; apply GlobalTheory.StdRealLift.exists_real_point <;> assumption)
end
