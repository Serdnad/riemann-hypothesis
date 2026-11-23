module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle468
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitAdjBound

variable {D : D7}

theorem cA_tmul_pair (α : Af D.host.F) (m : D.host.E) :
    cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star m := rfl

theorem tmul_eq_mul (x : AF D.host.F) (m : D.host.E) :
    (x ⊗ₜ[D.host.F] m : AE D) = algebraMap (AF D.host.F) (AE D) x * incA D m := by
  change _ = (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] m)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gen_conj {v : FinPl D} (π : AE D →+* Fv D.host.F v)
    (hA : ∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y))
    (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    ((Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) :
        Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose.map π =
      (evalV D.host.F v α * π (incA D (star a))) •
        ((S.gram.map fun x => π (incA D x)) * vecMulVec (fun k => π (incA D (s k))) (fun l => π (incA D (star (t l))))) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, cA_tmul_pair]
  rw [tmul_eq_mul]

  simp only [map_mul, hA, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, vecMulVec_apply, star_mul', star_sum,
  star_star, GlobalTheory.LatVac.gram_star, map_sum]
  rw [show sndA D.host.F (pairA D.host.F 0 α) = α from rfl]
  simp only [Matrix.map_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem adjCo_gen {v : FinPl D} (φ : SplitProj D v)
    (hA : ∀ y : AF D.host.F, rdA φ (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v (sndA D.host.F y))
    (hQ : ∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x)
    (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v))
    (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (i : Fin S.rank)
    (j : Fin T.rank) :
    adjCo φ S T BS BT (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j))
        i j =
      evalV D.host.F v α * rdQ φ (star a) * (((BS⁻¹).1 *ᵥ fun k => rdQ φ (s k)) i) *
        (((fun l => rdQ φ (star (t l))) ᵥ* (T.gram.map (rdQ φ) * BT.1)) j) := by
  set f : D.host.E →+* Fv D.host.F v := (rdA φ).comp (incA D) with hf
  have hGi : (S.gram⁻¹.map (incA D)).map (rdA φ) * S.gram.map (fun x => rdA φ (incA D x)) = 1 := by
    rw [Matrix.map_map]
    change S.gram⁻¹.map f * S.gram.map f = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  have hmid : ∀ (c : Fv D.host.F v) (V : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)),
      (S.gram⁻¹.map (incA D)).map (rdA φ) * (c • (S.gram.map (fun x => rdA φ (incA D x)) * V)) = c • V := by
    intro c V
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hT : (T.gram.map (incA D)).map (rdA φ) = T.gram.map (rdQ φ) := by
    rw [Matrix.map_map]; exact congrArg _ (funext hQ)
  unfold adjCo
  rw [Matrix.map_mul, Matrix.map_mul, gen_conj (rdA φ) hA, hmid, hT]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, hQ, Matrix.vecMul_vecMul, mul_assoc]

section Lin

variable {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
  (BT : GL (Fin T.rank) (Fv D.host.F v))

theorem adjCo_add (x y : WO S T) : adjCo φ S T BS BT (x + y) = adjCo φ S T BS BT x + adjCo φ S T BS BT y := by
  unfold adjCo
  rw [show ((x + y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) + (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) from rfl,
    Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _),
    Matrix.mul_add, Matrix.add_mul]

theorem adjCo_neg (x : WO S T) : adjCo φ S T BS BT (-x) = -adjCo φ S T BS BT x := by
  unfold adjCo
  rw [show ((-x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      -(x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) from rfl,
    Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.map_neg _ (map_neg _),
    Matrix.mul_neg, Matrix.neg_mul]

theorem adjCo_zero : adjCo φ S T BS BT 0 = 0 := by
  unfold adjCo
  rw [show ((0 : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = 0 from rfl,
    Matrix.map_zero _ (map_zero _), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _),
    Matrix.mul_zero, Matrix.zero_mul]

end Lin

theorem mul_latHat_mem {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {w : Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ intAE D) {y : Fin n → D.host.E} (hy : y ∈ Λ) :
    (fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] y i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β, hβ, o • y, Λ.smul_mem o hy, ?_⟩
    funext i
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => simp only [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => simp only [add_mul]; exact add_mem hx hz
  | neg x _ hx => simp only [neg_mul]; exact neg_mem hx

theorem adjCo_bound : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ (star a')) ≤ Valued.v (rdQ φ (star a))) → ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ∀ i j, Valued.v (adjCo φ S T (frCo φ βS) (frCo φ βT) u i j) ≤ Valued.v (rdQ φ (star a)) := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a hmax u hu
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a', ha', s, hs, t, ht, rfl⟩ := hw
    intro i j
    rw [adjCo_gen φ hπ.2.2.1 hQ]
    have h1 := (GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D S ΛS βS hS hfS v φ e he fun k => incA D (s k)).1 (by
      simp only [GlobalTheory.SplitHomLattice.finPart_mul_incA]
      exact mul_latHat_mem ΛS (GlobalTheory.SplitHomLattice.idem_int he.1) hs) i
    have h2 := (GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D T ΛT βT hT hfT v φ e he fun k => incA D (t k)).1 (by
      simp only [GlobalTheory.SplitHomLattice.finPart_mul_incA]
      exact mul_latHat_mem ΛT (GlobalTheory.SplitHomLattice.idem_int (GlobalTheory.SplitScalar.isSplitIdem_conj he.1)) ht) j
    simp only [hQ] at h1
    simp only [GlobalTheory.SplitDualLat.cA_incA, hQ] at h2
    have h3 := hmax a' ha'
    have h4 : Valued.v (evalV D.host.F v α) ≤ 1 := by
      have := hα v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_mul]
    calc _ ≤ 1 * Valued.v (rdQ φ (star a)) * 1 * 1 := mul_le_mul' (mul_le_mul' (mul_le_mul' h4 (hmax a' ha')) h1) h2
      _ = _ := by rw [one_mul, mul_one, mul_one]
  | zero =>
    intro i j
    rw [adjCo_zero, Matrix.zero_apply, map_zero]
    exact zero_le'
  | add x y _ _ hx hy =>
    intro i j
    rw [adjCo_add, Matrix.add_apply]
    exact Valuation.map_add_le _ (hx i j) (hy i j)
  | neg x _ hx =>
    intro i j
    rw [adjCo_neg, Matrix.neg_apply, Valuation.map_neg]
    exact hx i j

end GlobalTheory.SplitAdjBound
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.SplitHomBound

variable {D : D7}

theorem mul_mem_latHat {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) {x : Fin n → D.host.E} (hx : x ∈ Λ) :
    (fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) ∈
      Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
  unfold Formalism.MainNotions.StandardLattice.latHat
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, o, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨b, hb, o • x, Λ.smul_mem o hx, ?_⟩
    funext i
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, Algebra.smul_def]
  | zero =>
    have h0 : (fun i => (0 : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) = 0 := by
      funext i; simp
    rw [h0]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ =>
    have h3 : (fun i => (w₁ + w₂) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) =
        (fun i => w₁ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) + (fun i => w₂ * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) := by
      funext i; simp [add_mul]
    rw [h3]; exact add_mem h₁ h₂
  | neg w _ h =>
    have h3 : (fun i => (-w) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) =
        -(fun i => w * ((1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) := by
      funext i; simp [neg_mul]
    rw [h3]; exact neg_mem h

theorem rdA_pairA_tmul {v : FinPl D} (φ : SplitProj D v) (α : Af D.host.F) (m : D.host.E) :
    rdA φ (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = evalV D.host.F v α * rdQ φ m := by
  simp only [rdA, rdQ, GlobalTheory.AdelicU.compFin, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hev : GlobalTheory.AdelicU.evFin D.host.F v (pairA D.host.F 0 α) = evalV D.host.F v α := by
    simp only [GlobalTheory.AdelicU.evFin, pairA, sndA, ]
    rfl
  have hsm : (evalV D.host.F v α ⊗ₜ[D.host.F] m : Fv D.host.F v ⊗[D.host.F] D.host.E) =
      evalV D.host.F v α • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hev, hsm, map_smul, smul_eq_mul]

theorem mapCo_gen {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    mapCo φ S T BS BT (Matrix.of fun (i : Fin T.rank) (j : Fin S.rank) =>
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) i j =
      evalV D.host.F v α * rdQ φ a * (((BT⁻¹).1 *ᵥ fun k => rdQ φ (t k)) i) *
        (((fun k => rdQ φ (star (s k))) ᵥ* ((S.gram.map (rdQ φ)) * BS.1)) j) := by
  have hq : ∀ x y : D.host.E, rdQ φ (x * y) = rdQ φ x * rdQ φ y := by
    intro x y; simp only [← GlobalTheory.SplitProjChart.emb_apply, map_mul]
  have hqs : ∀ (f : Fin S.rank → D.host.E), rdQ φ (∑ k, f k) = ∑ k, rdQ φ (f k) := by
    intro f; simp only [← GlobalTheory.SplitProjChart.emb_apply, map_sum]
  simp only [mapCo, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, rdA_pairA_tmul, hq, hqs,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hbound : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, (∀ a' : D.host.E, a' ∈ D.host.AA → Valued.v (rdQ φ a') ≤ Valued.v (rdQ φ a)) → ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ∀ i j, Valued.v (mapCo φ S T (frCo φ βS) (frCo φ βT) u i j) ≤ Valued.v (rdQ φ a) := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a ha u hu
  obtain ⟨hch, -, hrdinc, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hfi : ∀ x : D.host.E, finPart D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
    intro x
    simp [finPart, incA, inclR]
  have he1 : finPart D e ∈ intAE D := by
    have h1 := (hch.2.2.2 1).2 ⟨1, by simp⟩
    simpa using h1
  have he2 : finPart D (cA D e) ∈ intAE D := by
    obtain ⟨-, -, w, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := he.1
    have hce : cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) - e := by
      rw [← hsum]; ring
    have hαint : α ∈ intAf D.host.F := by
      intro v'
      by_cases h : v' = w
      · subst h; rw [hα1]; exact one_mem _
      · rw [hα0 v' h]; exact zero_mem _
    have hfa : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
        α ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E) := by
      rw [show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]
      simp only [finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rfl
    rw [hce, map_sub, hfa]
    exact sub_mem (AddSubgroup.subset_closure ⟨α, hαint, 1, rfl⟩) he1
  have hcainc : ∀ x : D.host.E, cA D (incA D x) = incA D (star x) := by
    intro x
    rfl
  have h3 : ∀ t ∈ ΛT, ∀ i, Valued.v ((((frCo φ βT)⁻¹ : GL (Fin T.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdQ φ (t k)) i) ≤ 1 := by
    intro t ht i
    have hm : (fun k => finPart D (e * incA D (t k))) ∈
        Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) := by
      simpa only [map_mul, hfi] using mul_mem_latHat ΛT he1 ht
    simpa only [hrdinc] using (GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D T ΛT βT hT hfT v φ e he (fun k => incA D (t k))).1 hm i
  have h4 : ∀ s ∈ ΛS, ∀ j, Valued.v (((fun k => rdQ φ (star (s k))) ᵥ* ((S.gram.map (rdQ φ)) * (frCo φ βS).1)) j) ≤ 1 := by
    intro s hs j
    have hm : (fun k => finPart D (cA D e * incA D (s k))) ∈
        Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) := by
      simpa only [map_mul, hfi] using mul_mem_latHat ΛS he2 hs
    simpa only [hcainc, hrdinc] using (GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D S ΛS βS hS hfS v φ e he (fun k => incA D (s k))).1 hm j
  unfold latO at hu
  simp only [not_true_eq_false, false_implies, implies_true, true_and] at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, c, hc, s, hs, t, ht, rfl⟩ := hw
    intro i j
    rw [mapCo_gen, Valuation.map_mul, Valuation.map_mul, Valuation.map_mul]
    have h1 : Valued.v (evalV D.host.F v α) ≤ 1 := by
      have h0 := hα v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h0
    calc _ ≤ 1 * Valued.v (rdQ φ a) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' h1 (ha c hc)) (h3 t ht i)) (h4 s hs j)
      _ = Valued.v (rdQ φ a) := by rw [one_mul, mul_one, mul_one]
  | zero =>
    intro i j
    simp [mapCo]
  | add x y _ _ hx hy =>
    intro i j
    have hxy : mapCo φ S T (frCo φ βS) (frCo φ βT) (x + y) =
        mapCo φ S T (frCo φ βS) (frCo φ βT) x + mapCo φ S T (frCo φ βS) (frCo φ βT) y := by
      simp [mapCo, Matrix.map_add (f := _), Matrix.mul_add, Matrix.add_mul]
    rw [hxy, Matrix.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (hx i j) (hy i j))
  | neg x _ hx =>
    intro i j
    have hxn : mapCo φ S T (frCo φ βS) (frCo φ βT) (-x) = -mapCo φ S T (frCo φ βS) (frCo φ βT) x := by
      simp [mapCo, Matrix.map_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [hxn, Matrix.neg_apply, Valuation.map_neg]
    exact hx i j

end GlobalTheory.SplitHomBound

end
end

section

open GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.linearMapChainComposite_update_smul : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n := by
  first | exact @GlobalTheory.ChainSmul.chainTo_update_smul | exact GlobalTheory.ChainSmul.chainTo_update_smul | (intros; apply GlobalTheory.ChainSmul.chainTo_update_smul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.right_derivative_rightConvolution_eq_test_function : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  first | exact @GlobalTheory.ConvRDeriv.Rder_convR | exact GlobalTheory.ConvRDeriv.Rder_convR | (intros; apply GlobalTheory.ConvRDeriv.Rder_convR <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftGram

theorem inner_eq_sum_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ z₁ z₂ : H.H,
    (∀ h w, inner ℂ (c.ext (H.e z₁) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₁ fun ρ => v ρ) h) →
    (∀ h w, inner ℂ (c.ext (H.e z₂) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₂ fun ρ => v ρ) h) →
    ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ c.W),
      inner ℂ z₁ z₂ = ∑ k, GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₂ fun ρ => v ρ)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hirr hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν hy hH v hv U₁ hU₁ U₂ hU₂
    z₁ z₂ h₁ h₂ ι _ b
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  refine (GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)).elim fun μ h0 => h0.elim fun 𝓧 hμ => ?_
  have h5 := (hd.1.models.νW i).1.2.2 R.θ hd.1.models.inf
  refine h5.1.elim fun Fr hFr => (h5.2 Fr hFr).1.elim fun mR hmR => ?_
  have hint : ∀ k, IntegrableOn (fun h =>
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h)) (R.fdV i A.μ0) (R.νV i A.μ0) := fun k =>
    (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hd _ _ hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v v
      (io (PiTensorProduct.tprod ℂ v) (b k)) (io (PiTensorProduct.tprod ℂ v) (b k))).2.1
  have hx := fun z => (SetLike.ext_iff.mp hH.2.1 _).mp (LinearMap.mem_range_self H.e z)
  have e1 := GlobalTheory.AdelicScalar.integral_eq_classSum (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m) hν hy
    (fun h => inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h)) fun γ hγ k hk x =>
      (congrArg₂ (inner ℂ) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₁) hγ k hk x) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₂) hγ k hk x)).trans
        (GlobalTheory.AdelicScalar.inner_law c.ρ hc.2.1 (GlobalTheory.AdelicScalar.norm_levChi _ _ k) _ _ _)
  simp only [GlobalTheory.AdelicScalar.ext_finLift c hc] at e1
  rw [hH.2.2 z₁ z₂]
  unfold Bridge.adInner
  rw [← e1]
  have e2 : ∀ h, inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h) = ∑ k,
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h) := fun h =>
    (b.sum_inner_mul_inner _ _).symm.trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) (h₁ h (b k))
      ((inner_conj_symm _ _).symm.trans (congrArg (starRingEnd ℂ) (h₂ h (b k)))))
  refine (congrArg (fun F => ∫ h in R.fdV i A.μ0, F h ∂(R.νV i A.μ0)) (funext e2)).trans ?_
  exact integral_finsetSum _ fun k _ => hint k

end GlobalTheory.LiftGram

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus.RowMat

theorem map_coord_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (f : V → V) (hf : Measurable f)
    (hfH : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map f = μ) (ρ : ℕ)
    [inst : MeasurableSpace (Fin ρ → V)] [hB : BorelSpace (Fin ρ → V)]
    (lam : Measure (Fin ρ → V)) [hlam : lam.IsAddHaarMeasure] :
    lam.map (fun b i => f (b i)) = lam := by
  have e : inst = MeasurableSpace.pi :=
    hB.measurable_eq.trans (@BorelSpace.measurable_eq (Fin ρ → V) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have hp : MeasurePreserving f (Measure.addHaar : Measure V) Measure.addHaar :=
    ⟨hf, hfH _ inferInstance⟩
  have hpi := measurePreserving_pi (fun _ : Fin ρ => (Measure.addHaar : Measure V))
    (fun _ => Measure.addHaar) (fun _ => hp)
  rw [Measure.isAddLeftInvariant_eq_smul lam (Measure.pi fun _ : Fin ρ => (Measure.addHaar : Measure V)),
    Measure.map_smul _ hpi.measurable.aemeasurable]
  congr 1
  exact (measurePreserving_pi (fun _ : Fin ρ => (Measure.addHaar : Measure V))
    (fun _ => Measure.addHaar) (fun _ => hp)).map_eq

theorem map_mul_mt_eq : ∀ (D : D7) (S₀ : HSp D) (ρ : ℕ) (lam : Measure (Mx D ρ S₀.rank)),
    lam.IsAddHaarMeasure → ∀ h : GA D S₀,
      lam.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) = lam := by
  intro D S₀ ρ lam hlam h
  have h1 : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  have h2 : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have h3 : LocallyCompactSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.1
  have h4 : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  have h5 : BorelSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.2
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hrow := GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm.1 S₀.rank S₀.gram
    (hcm.2 S₀) h
  have e : (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h) =
      fun b i => Matrix.vecMul (b i) (mt S₀ h) := by
    funext b i j
    rfl
  rw [e]
  have hm : Measurable (fun x : Fin S₀.rank → AE D => Matrix.vecMul x (mt S₀ h)) :=
    (Continuous.matrix_vecMul continuous_id continuous_const).measurable
  exact map_coord_eq (V := Fin S₀.rank → AE D) (f := fun x => Matrix.vecMul x (mt S₀ h)) (hf := hm)
    (hfH := fun μ hμ => hrow μ hμ) (ρ := ρ) (inst := measMx ρ S₀.rank)
    (hB := @BorelSpace.mk _ _ (measMx ρ S₀.rank) rfl) (lam := lam) (hlam := hlam)

end GlobalTheory.AdelicModulus.RowMat
end
