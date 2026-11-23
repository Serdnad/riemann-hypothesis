module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle161
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelHeight
open GlobalTheory.HolDict.ShortVec (intRing finPr)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (finCoord)

theorem openSub (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
      (∀ i j k, a i j k ∈ intRing D.host.F) →
      (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
        Module.finBasis D.host.F D.host.E k : WO V W) ∈ U :=
  GlobalTheory.T.exists_natMul_integralMatrices_subset_openAddSubgroup D V W U hU

theorem eq_sum_of_infPart (D : D7) (z : AE D) (hz : infPart D z = 0) :
    z = ∑ k, pairA D.host.F 0 (finCoord D (finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k :=
  GlobalTheory.T.eq_sum_finiteCoords_of_infinitePart_zero D z hz

theorem exists_denom_mul (D : D7) : ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
    (∀ k, (e₁ : Af D.host.F) * finCoord D a k ∈ intRing D.host.F) →
    (∀ k, (e₂ : Af D.host.F) * finCoord D b k ∈ intRing D.host.F) →
    ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * finCoord D (a * b) k ∈ intRing D.host.F :=
  GlobalTheory.T.finiteAdeleTensorCoords_mul_denominator_bound D

theorem exists_denom_integral (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x →
    ∀ k, (d : Af D.host.F) * finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ intRing D.host.F :=
  GlobalTheory.T.exists_fixed_denominator_finiteCoords_integral D

theorem infPart_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) : (finLift z).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i j) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] z i j := rfl
  simp only [finLift, Matrix.map_apply, Matrix.zero_apply]
  rw [h1, TensorProduct.zero_tmul]

theorem finPr_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) :
    (finLift z).map (finPr D) = z.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  ext i j
  rfl

theorem tmul_natCast_mul {D : D7} (N : ℕ) (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finPr_Y {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (N : ℕ)
    (x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) : WO V W).map (finPr D) =
      ((N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e)) *
        P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  have e1 : ((N : D.host.E) • x).map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j
    exact tmul_natCast_mul N (x i j)
  have e2 : (P.map (incA D)).map (finPr D) = P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j; rfl
  rw [Matrix.map_mul, finPr_finLift, e1, e2]

theorem finPr_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W).map (finPr D) =
      Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * Y.map (finPr D) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem infPart_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (z : Matrix (Fin W.rank) (Fin r) D.host.E)
    (g : GA D V) (h : GA D W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) (HMul.hMul (finLift z) (P.map (incA D)) : WO V W))
      (Formalism.L2.Theta.mt V g) : WO V W).map (infPart D) = 0 := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, infPart_finLift]
  simp

theorem actO_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    actO V W g h (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W) = Y := by
  have e1 : Formalism.L2.Theta.mt W h * Formalism.L2.Theta.mt W h⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  simp only [actO, ← Matrix.mul_assoc]
  rw [e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]

theorem entry_of_map_eq {m n : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Matrix (Fin m) (Fin n) R)
    (c : S) (w : Matrix (Fin m) (Fin n) S) (h : u.map f = c • w) (i : Fin m) (j : Fin n) : f (u i j) = c * w i j := by
  have := congrFun (congrFun h i) j
  simpa using this

theorem openSubY (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U := by
  obtain ⟨M₀, hM₀, hsub⟩ := openSub D V W U hU
  refine ⟨M₀, hM₀, fun y hy hc => ?_⟩
  choose b hb hbe using hc
  convert hsub b hb using 1
  ext i j
  rw [Matrix.of_apply, eq_sum_of_infPart D (y i j) (by simpa using congrFun (congrFun hy i) j)]
  exact Finset.sum_congr rfl fun k _ => by rw [hbe]

def Den (D : D7) (e : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : Prop :=
  ∀ k, (e : Af D.host.F) * finCoord D z k ∈ intRing D.host.F

theorem den_sum {D : D7} {e : ℕ} {ι : Type} (s : Finset ι) (f : ι → Af D.host.F ⊗[D.host.F] D.host.E)
    (h : ∀ i ∈ s, Den D e (f i)) : Den D e (∑ i ∈ s, f i) := fun k => by
  unfold finCoord

  rw [map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  exact (intRing D.host.F).sum_mem fun i hi => h i hi k

theorem den_matMul {D : D7} {c : ℕ} (hc : ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
      Den D e₁ a → Den D e₂ b → Den D (c * e₁ * e₂) (a * b)) {m n p : ℕ} {e₁ e₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (B : Matrix (Fin n) (Fin p) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hA : ∀ i j, Den D e₁ (A i j)) (hB : ∀ i j, Den D e₂ (B i j)) : ∀ i j, Den D (c * e₁ * e₂) ((A * B) i j) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact den_sum _ _ fun l _ => hc e₁ e₂ _ _ (hA i l) (hB l j)

theorem finCoord_natCast_mul (D : D7) (N : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) (k) :
    finCoord D ((N : Af D.host.F ⊗[D.host.F] D.host.E) * z) k = (N : Af D.host.F) * finCoord D z k := by
  unfold finCoord
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem exists_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (U : AddSubgroup (WO V W))
    {M₀ : ℕ} (hsub : ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U)
    (D' : ℕ) (g : GA D V) (h : GA D W) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    (hden : ∀ i j, Den D D' ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) i j)) :
    ∃ u ∈ U, u.map (infPart D) = 0 ∧
      actO V W g h u = HMul.hMul (finLift (((M₀ * D' : ℕ) : D.host.E) • x)) (P.map (incA D)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = M₀ * D' := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨wf, hwf⟩ : ∃ wf : Matrix (Fin W.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E),
    wf = Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := ⟨_, rfl⟩
  rw [← hwf] at hden
  obtain ⟨Y, hY⟩ : ∃ Y : WO V W, Y = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : WO V W, u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) := ⟨_, rfl⟩
  have hinf : u.map (infPart D) = 0 := by
    rw [hu, hY]; exact infPart_u P _ g h
  have hfin : u.map (finPr D) = (N : Af D.host.F ⊗[D.host.F] D.host.E) • wf := by
    rw [hu, finPr_u, hY, finPr_Y, hwf]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  refine ⟨u, ?_, hinf, ?_⟩
  · refine hsub u hinf fun i j k => ⟨_, hden i j k, ?_⟩
    rw [entry_of_map_eq (finPr D) u _ wf hfin i j, finCoord_natCast_mul, hN, Nat.cast_mul, mul_assoc]
  · rw [hu, actO_u]
    exact hY

theorem levelheight : ∀ (D : D7) (V W : HSp D) (r : ℕ) (P : Matrix (Fin r) (Fin V.rank) D.host.E), ∃ e : ℕ,
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W),
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧
    ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ u ∈ U,
      u.map (infPart D) = 0 ∧ actO V W g h u = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := by
  intro D V W r P
  refine ⟨1, fun U hU => ?_⟩
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).1
  obtain ⟨CV, hCV, hcV⟩ := GlobalTheory.Grow.height_comparison V hθ
  obtain ⟨CW, hCW, hcW⟩ := GlobalTheory.Grow.height_comparison W hθ
  obtain ⟨M₀, hM₀, hsub⟩ := openSubY D V W U hU
  obtain ⟨c, hc0, hc⟩ := exists_denom_mul D
  obtain ⟨dx, hdx, hx⟩ := exists_denom_integral D
  obtain ⟨dP, hdP, hP⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (intRing D.host.F)
    (fun q : Fin r × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] P q.1 q.2.1) q.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  set nV := ⌈CV⌉₊ with hnV
  set nW := ⌈CW⌉₊ with hnW
  have hnV0 : 0 < nV := Nat.ceil_pos.2 hCV
  have hnW0 : 0 < nW := Nat.ceil_pos.2 hCW
  refine ⟨M₀ * c ^ 3 * dx * dP * nW * nV, by positivity, fun g h => ?_⟩
  obtain ⟨dh, hdh0, hdhH, hdh⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := W) h⁻¹
  obtain ⟨dg, hdg0, hdgH, hdg⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := V) g
  set D' := c * (c * (c * dh * dx) * dP) * dg with hD'
  refine ⟨M₀ * D', by positivity, ?_, fun x hxi => ?_⟩
  ·
    have h1 : (dh : ℝ) ≤ nW * GlobalTheory.Grow.height W h := by
      have := (hcW h⁻¹).1
      rw [GlobalTheory.Grow.height_inv] at this
      exact hdhH.trans (this.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _)
        (GlobalTheory.Grow.height_pos W h).le))
    have h2 : (dg : ℝ) ≤ nV * GlobalTheory.Grow.height V g :=
      hdgH.trans ((hcV g).1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (GlobalTheory.Grow.height_pos V g).le))
    rw [pow_one, hD']
    push_cast
    have hpos : (0 : ℝ) ≤ M₀ * c ^ 3 * dx * dP := by positivity
    calc (M₀ : ℝ) * (c * (c * (c * dh * dx) * dP) * dg) = (M₀ * c ^ 3 * dx * dP) * (dh * dg) := by ring
      _ ≤ (M₀ * c ^ 3 * dx * dP) * ((nW * GlobalTheory.Grow.height W h) * (nV * GlobalTheory.Grow.height V g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (mul_nonneg (by positivity) (GlobalTheory.Grow.height_pos W h).le)) hpos
      _ = _ := by ring
  · exact exists_u P U hsub _ g h x (by
      rw [hD']
      refine den_matMul hc _ _ (den_matMul hc _ _ (den_matMul hc _ _ (fun i j => hdh i j) ?_) ?_) (fun i j => hdg i j)
      · intro i j; exact hx _ (hxi i j)
      · intro i j k; exact hP (i, j, k))
end GlobalTheory.LevelHeight
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSplitChars
open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem twVal_of_unit (χ : HChar E) (w : ℝ) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) (hk : P.valuation E (k : E) = 1) :
    twVal χ w P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  have h0 : Formalism.L2.Host.ordF P k = 0 := by simp [Formalism.L2.Host.ordF, hk]
  simp [twVal, h0]

theorem isClopen_oneUnits (P : HeightOneSpectrum (𝓞 E)) :
    IsClopen {x : (P.adicCompletion E)ˣ | Valued.v ((x : P.adicCompletion E) - 1) < 1} := by
  have := (Valued.isClopen_ball (P.adicCompletion E) (r := 1)).preimage
      (f := fun x : (P.adicCompletion E)ˣ => (x : P.adicCompletion E) - 1)
      ((Units.continuous_val (M := P.adicCompletion E)).sub continuous_const)
  convert this using 1
  ext x
  simp

theorem tameAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E ((u : E) - 1) < 1 → χ.locK P u = 1) : χ.TameAt P := by
  have key : ∀ x : (P.adicCompletion E)ˣ, Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1 := by
    intro x
    refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on
      (p := fun x => Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1) x ?_ fun k hk => h k ?_
    · exact isClosed_imp (isClopen_oneUnits P).2
        (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)
    · have e : ((atFin P k : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1 =
          algebraMap E (P.adicCompletion E) ((k : E) - 1) := by
        rw [map_sub, map_one]; rfl
      rwa [e, Formalism.UG.P.levelaf_valued_algebraMap] at hk
  intro x _ hx
  refine key x (lt_of_le_of_lt hx ?_)
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 (by norm_num)

theorem locK_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ)
    (hk : P.valuation E (k : E) = 1) : ((χ'.locK P k : ℂˣ) : ℂ) = s ((χ.locK P k : ℂˣ) : ℂ) := by
  have := h P k
  rwa [twVal_of_unit _ _ _ _ hk, twVal_of_unit _ _ _ _ hk] at this

theorem unrAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (hu : χ.UnrAt P) : χ'.UnrAt P :=
  GlobalTheory.EtaConjType.unrAt_of_locK χ' P fun u hu' => Units.ext (by
    rw [locK_conj h P u hu', GlobalTheory.NormOneUnit.locK_unr hu hu', Units.val_one, map_one])

theorem tameAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (ht : χ.TameAt P) : χ'.TameAt P := by
  refine tameAt_of_locK χ' P fun u hu => Units.ext ?_
  have h1 : P.valuation E ((1 : Eˣ) : E) = 1 := by simp
  have hu1 : P.valuation E (u : E) = 1 := by
    have := Valuation.map_eq_of_sub_lt (P.valuation E) (x := 1) (y := (u : E)) (by rwa [map_one])
    rwa [map_one] at this
  rw [locK_conj h P u hu1, GlobalTheory.NormOneUnit.locK_tame ht h1 (by simpa using hu), map_one, Units.val_one, map_one]


open Classical in
theorem conj_chars_res : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ i t s cμ cη m, IsConjChars R i t s cμ cη m → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP)) ∧ (∀ Z : Finset (Pl D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ Z) → GlobalTheory.StepLaw.UnrOff cμ Z ∧ GlobalTheory.StepLaw.UnrOff (cμ * cη⁻¹) Z) ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ finS R t → UnrAt cμ w ∧ UnrAt (cμ * cη⁻¹) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t s cμ cη m hc
  obtain ⟨μ', η', hμ, hη, ecμ, ecη, hres⟩ := hc
  obtain ⟨-, p1, p2, p3⟩ := GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t
  have uη : ∀ P, η'.UnrAt P := fun P => unrAt_conj hη (R.C.isEta.unr P)
  have uμ : ∀ P : Pl D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) →
      μ'.UnrAt P := fun P hP => unrAt_conj hμ (((p3 P hP).2 i).mul (p3 P hP).1)
  have tμ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → μ'.TameAt PP := by
    intro PP hPP
    refine tameAt_conj hμ ?_
    rcases hPP with hP | hP
    · exact ((R.C.isMu0 i).tame PP).mul ((p1 PP hP).levelLe 1)
    · exact ((p2 PP hP i).levelLe 1).mul (hL.xi_tame t PP)
  have rη : ∀ PP, GlobalTheory.StepLaw.ResAt cη⁻¹ PP 1 := fun PP => by
    have := ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cη η' ecη PP).2 (uη PP)).inv
    rwa [inv_one] at this
  have uoη : ∀ Z, GlobalTheory.StepLaw.UnrOff cη Z := fun Z v ε hε _ =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cη η' ecη v ε hε fun P _ => uη P
  refine ⟨fun PP hPP => ?_, fun Z hZ => ?_, fun w hw => ?_⟩
  · have h1 := (GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cμ μ' ecμ PP).1 (m PP) (tμ PP hPP) (hres PP hPP)
    refine ⟨h1, ?_⟩
    have := h1.mul (rη PP)
    rwa [mul_one] at this
  · have h1 : GlobalTheory.StepLaw.UnrOff cμ Z := fun v ε hε hv =>
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cμ μ' ecμ v ε hε fun P hP => uμ P fun PP hPP => hP ▸ hv PP (hZ PP hPP)
    exact ⟨h1, h1.mul (uoη Z).inv⟩
  · have hw' : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ w.under (𝓞 D.host.F) := fun PP hPP he =>
      hw (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, he⟩)
    have h1 : UnrAt cμ w := (unrAt_iff_of_chrEq ecμ w).2 (uμ w hw')
    exact ⟨h1, h1.mul ((unrAt_iff_of_chrEq ecη w).2 (uη w)).inv⟩

end GlobalTheory.ConjSplitChars

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealAct

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

def ActsLin (θ : InfFam D) (M : DSModel V S) (k : GA D V) : Prop :=
  ∃ φ : Module.End ℂ (MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ),
    ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T)

theorem actsLin_one (M : DSModel V S) : ActsLin θ M 1 := by
  refine ⟨LinearMap.id, ?_⟩
  intro J χ T _ g
  rw [mul_one]
  rfl

theorem actsLin_mul {M : DSModel V S} {a b : GA D V} (ha : ActsLin θ M a) (hb : ActsLin θ M b) :
    ActsLin θ M (a * b) := by
  obtain ⟨φa, hφa⟩ := ha
  obtain ⟨φb, hφb⟩ := hb
  refine ⟨φb ∘ₗ φa, fun J χ T hT g => ?_⟩
  calc evAt M (g * (a * b)) T = evAt M ((g * a) * b) T := by rw [mul_assoc]
    _ = φb (evAt M (g * a) T) := hφb J χ T hT (g * a)
    _ = φb (φa (evAt M g T)) := by rw [hφa J χ T hT g]

theorem actsLin_atTau {M : DSModel V S} (hM : AllPlus M) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ActsLin θ M (atTau θ V τ u) := by
  classical
  have htop : M.sm τ = ⊤ := (AllPlus.finite_smooth_irreducible _ V S M hM τ).2.1
  let A : M.sm τ →ₗ[ℂ] M.sm τ :=
    (M.rep τ u).toLinearMap.restrict (fun x _ => by rw [htop]; exact Submodule.mem_top)
  let F : ∀ i, M.sm i →ₗ[ℂ] M.sm i := Function.update (fun i => (LinearMap.id : M.sm i →ₗ[ℂ] M.sm i)) τ A
  refine ⟨MultilinearMap.compLinearMapₗ F, ?_⟩
  intro J χ T hT g
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ θ V S M J χ T).1 hT
  ext v
  have hv : (fun i => F i (v i)) = Function.update v τ (A (v τ)) := by
    funext i
    by_cases h : i = τ
    · subst h
      simp [F]
    · simp [F, h]
  have hw : ((A (v τ) : M.sm τ) : M.H τ) = M.rep τ u (v τ) := rfl
  have key := congrFun (hmap.equiv τ u hu v (A (v τ)) hw) g
  rw [evAt_apply]
  simp only [MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]
  rw [evAt_apply, hv, key]
  rfl

theorem real_acts : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  intro D θ V S M hθ hM k hk
  classical
  obtain ⟨L, -, hLmul, -, hLarch, hLinv, hLat, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨a, hUa, hkL⟩ : ∃ a, a ∈ GlobalTheory.HolDict.UG (gramAt D V) ∧ L a = k := ⟨_, hLarch k, hLinv k hk⟩
  have haU : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := hUa
  have h1U : ∀ τ, (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    intro τ
    simp [Formalism.QuantumDeterminants.UH]
  have hL1 : L 1 = 1 := by
    have h := hLmul 1 (fun τ => h1U τ) 1 (fun τ => h1U τ)
    rw [mul_one] at h
    calc L 1 = (L 1)⁻¹ * (L 1 * L 1) := by group
      _ = (L 1)⁻¹ * L 1 := by rw [← h]
      _ = 1 := inv_mul_cancel _
  have hpart : ∀ s : Finset D.what₂.Tau,
      ActsLin θ M (L fun τ => if τ ∈ s then a τ else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun τ : D.what₂.Tau => if τ ∈ (∅ : Finset D.what₂.Tau) then a τ else 1) = 1 := by
        funext τ
        simp
      rw [he, hL1]
      exact actsLin_one M
    | insert x s hx ih =>
      have hs : (fun τ => if τ ∈ s then a τ else 1) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ ∈ s
        · simpa [h] using haU τ
        · simpa [h] using h1U τ
      have hsing : Pi.mulSingle x (a x) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ = x
        · subst h
          simpa using haU τ
        · simpa [Pi.mulSingle_apply, h] using h1U τ
      have hsplit : (fun τ => if τ ∈ insert x s then a τ else 1)
          = Pi.mulSingle x (a x) * fun τ => if τ ∈ s then a τ else 1 := by
        funext τ
        by_cases h : τ = x
        · subst h
          simp [hx]
        · simp [h, Pi.mulSingle_apply]
      rw [hsplit, hLmul _ hsing _ hs, ← hLat x (a x) (haU x)]
      exact actsLin_mul (actsLin_atTau hM x (haU x)) ih
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset D.what₂.Tau) then a τ else 1) = a := by
    funext τ
    simp
  have := hpart Finset.univ
  rw [hall, hkL] at this
  exact this

end GlobalTheory.RealAct

end
end
