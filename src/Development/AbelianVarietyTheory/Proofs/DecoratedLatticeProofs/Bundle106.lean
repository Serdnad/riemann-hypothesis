module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle038
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowestKType_mem_discreteSeriesKFiniteVectors : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (v : lowT M τ), ((v : M.sm τ) : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ := by
  first | exact @GlobalTheory.LowKFin.lowT_mem_kfin | exact GlobalTheory.LowKFin.lowT_mem_kfin | (intros; apply GlobalTheory.LowKFin.lowT_mem_kfin <;> assumption)
end

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalUnique

theorem genVal_top_ne_zero (q N : ℕ) (α : Fin N → ℂˣ) : genVal q 0 N (Finset.univ.val.map α) N ≠ 0 := by
  simp only [genVal, Nat.sub_self, mul_zero, zero_mul, add_zero, pow_zero, one_mul, Multiset.map_map]
  have e : (Multiset.map ((fun b : ℂˣ => (b : ℂ)) ∘ α) Finset.univ.val).esymm N = ∏ i, (α i : ℂ) := by
    rw [Finset.esymm_map_val]
    have : (Finset.univ : Finset (Fin N)).powersetCard N = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin N))
    rw [this, Finset.sum_singleton]; rfl
  rw [e, Finset.prod_ne_zero_iff]
  exact fun i _ => (α i).ne_zero

theorem eq_mul_zonalInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ α : Fin N → ℂˣ, ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ ∧ ∀ f : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * f m) → ∀ m, f m = f 1 * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ϖ hϖ α
  have hq : (1 : ℕ) < resCard k := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have hγ : ∀ i, borelParam (resCard k) α i ≠ 0 := by
    intro i
    unfold borelParam
    refine mul_ne_zero (α i).ne_zero ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by exact_mod_cast (show resCard k ≠ 0 by omega) (by exact_mod_cast h.1)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_borelSphericalFunction k N _ hγ
  refine ⟨ψ, hψ, fun f hf he m => ?_⟩
  have hr : ∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g := hψ.1
  have hωb := GlobalTheory.T.zonalInt_mul_KO_invariant k N μK hK ψ hr
  have hω1 := GlobalTheory.T.zonalInt_one_eq_one_of_isBorelSph k N μK hK _ ψ hψ
  have hωe : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, zonalInt μK ψ (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * zonalInt μK ψ m := by
    intro s R hR
    refine GlobalTheory.T.sum_zonalInt_mul_eq_of_eigen k N μK hK ψ hr R _ fun m => ?_
    rw [GlobalTheory.T.sum_borelSpherical_doubleCosetReps_mul k N _ ψ hψ hγ _ R hR m, GlobalTheory.T.sum_borelSpherical_over_diagonalDoubleCosetReps k N ϖ hϖ _ ψ hψ hγ s R hR,
      GlobalTheory.T.sum_powersetCard_borelParam_eq_genVal (resCard k) N (by omega) α s.card, mul_comm]
  have hcN : genVal (resCard k) 0 N (Finset.univ.val.map α) N ≠ 0 := genVal_top_ne_zero _ N α
  have key := GlobalTheory.T.cartan_decomposition_dominance_order k N ϖ (fun n => genVal (resCard k) 0 N (Finset.univ.val.map α) n) hcN
    (GlobalTheory.T.exists_antitone_cartan_decomposition k N ϖ hϖ) (GlobalTheory.T.cartan_decomposition_dominance_local_field k N ϖ hϖ) (fun g => (GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k Unit (Fin N)).2 g)
    (fun m => f m - f 1 * zonalInt μK ψ m)
    (fun κ hκ m => ⟨by rw [(hf κ hκ m).1, (hωb κ hκ m).1], by rw [(hf κ hκ m).2, (hωb κ hκ m).2]⟩)
    (fun s R hR m => by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, he s R hR m, hωe s R hR m]
      ring)
    (by simp [hω1]) m
  exact sub_eq_zero.1 key

end GlobalTheory.ZonalUnique

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspGeo

open Formalism.IndefR.Eqv

theorem norm_mul_mul_apply_le {n : ℕ} (P A Q : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hA : ∀ k l, ‖A k l‖ ≤ c)
    (i j : Fin n) : ‖(P * A * Q) i j‖ ≤ (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
  simp only [Matrix.mul_apply]
  calc ‖∑ l, (∑ k, P i k * A k l) * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * c * ‖Q l j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, ← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hA k l) (norm_nonneg _)
    _ = (∑ k, ∑ l, ‖P i k‖ * ‖Q l j‖) * c := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem norm_uMat_inv_apply {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat y⁻¹ i j‖ = ‖uMat y j i‖ := by
  have hy : (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y = Formalism.REAL.Jm ε := y.2
  have h1 : uMat y⁻¹ = Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε := by
    show (((y : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
    refine Units.inv_eq_of_mul_eq_one_left ?_
    calc Formalism.REAL.Jm ε * (uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y
        = Formalism.REAL.Jm ε * ((uMat y)ᴴ * Formalism.REAL.Jm ε * uMat y) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]
  rw [h1]
  by_cases hi : ε i <;> by_cases hj : ε j <;>
    simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hi, hj]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def frameBound (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : ℝ :=
  ∑ k, ∑ l, ‖fr.P (Formalism.L2.Host.tauPl D τ) i k‖ * ‖(fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ l j‖

theorem frameBound_nonneg (fr : UI.Frames D V) (τ : D.what₂.Tau) (i j : Fin V.rank) : 0 ≤ frameBound fr τ i j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

def brgFin (fr : UI.Frames D V) : (UI.instV fr).Gf →* GA D V :=
  (UI.brg fr : (UI.instV fr).GA →* GA D V).comp (MonoidHom.inr _ _)

theorem brgFin_apply (fr : UI.Frames D V) (k : (UI.instV fr).Gf) : brgFin fr k = UI.brg fr (1, k) := rfl

theorem continuous_brgFin (fr : UI.Frames D V) : Continuous (brgFin fr) :=
  (UI.brg fr).continuous.comp (continuous_const.prodMk continuous_id)

theorem brg_entry_bounds (fr : UI.Frames D V)
    (h2 : ∀ (x : (UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr x) =
        fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (y : (UI.instV fr).Ginf) (c : ℝ),
      ((∀ v i j, ‖uMat (y v) i j‖ ≤ c) → normInf θ V (UI.brg fr (y, 1)) ≤ S * c) ∧
      ((∀ v i j, ‖(uMat (y v) - 1) i j‖ ≤ c) →
        ∀ τ i j, ‖(infMat D.sp.cm.sig V.gram (θ τ) (UI.brg fr (y, 1)) - 1) i j‖ ≤ S * c) := by
  have hle : ∀ τ i j, frameBound fr τ i j ≤ ∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j := fun τ i j => by
    have h0 := frameBound_nonneg fr
    calc frameBound fr τ i j ≤ 2 * frameBound fr τ i j := by linarith [h0 τ i j]
      _ ≤ ∑ j', 2 * frameBound fr τ i j' :=
          Finset.single_le_sum (f := fun j' => 2 * frameBound fr τ i j') (fun j' _ => by linarith [h0 τ i j'])
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', 2 * frameBound fr τ i' j' :=
          Finset.single_le_sum (f := fun i' => ∑ j', 2 * frameBound fr τ i' j')
            (fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ i' j']) (Finset.mem_univ i)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', 2 * frameBound fr τ' i' j')
            (fun τ' _ => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => by linarith [h0 τ' i' j'])
            (Finset.mem_univ τ)
  refine ⟨∑ τ, ∑ i, ∑ j, 2 * frameBound fr τ i j,
    Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg zero_le_two (frameBound_nonneg fr τ i j), fun y c => ⟨fun hc => ?_, fun hc τ i j => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have e1 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c (fun k l => hc (Formalism.L2.Host.tauPl D τ) k l) i j
    have e2 := norm_mul_mul_apply_le (fr.P (Formalism.L2.Host.tauPl D τ))
      (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ c
      (fun k l => (norm_uMat_inv_apply _ k l).trans_le (hc _ l k)) i j
    rw [← map_inv, h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl,
      h2 _ τ (uMat ((y (Formalism.L2.Host.tauPl D τ))⁻¹) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    unfold frameBound
    linarith
  · have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc (Formalism.L2.Host.tauPl D τ) i j)
    have hdet : IsUnit (fr.P (Formalism.L2.Host.tauPl D τ)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit (Formalism.L2.Host.tauPl D τ))
    rw [h2 _ τ (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) rfl]
    have e : fr.P (Formalism.L2.Host.tauPl D τ) * (uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ - 1 = fr.P (Formalism.L2.Host.tauPl D τ) *
        ((uMat (y (Formalism.L2.Host.tauPl D τ)) : Matrix (Fin V.rank) (Fin V.rank) ℂ) - 1) *
        (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hdet]
    rw [e]
    exact (norm_mul_mul_apply_le _ _ _ c (hc _) i j).trans (mul_le_mul_of_nonneg_right (hle τ i j) hc0)

theorem near (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    Near θ V := by
  intro U hU
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.unitaryGroup_twoModels_rationalReal_unipotent_dictionary D θ hθ V (UI.framesV D V)
  obtain ⟨S, hS0, hS⟩ := brg_entry_bounds (θ := θ) (UI.framesV D V) h2
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow (θ := θ) V hθ
  have hKp : IsOpen ((U.comap (brgFin (UI.framesV D V)) : Subgroup _) : Set (UI.instV (UI.framesV D V)).Gf) :=
    hU.preimage (continuous_brgFin _)
  obtain ⟨b, C, δ₀, K, hδ₀, hK, hx⟩ := GlobalTheory.T.adelicPoint_nearCusp_scale (UI.instV (UI.framesV D V)) _ hKp
  obtain ⟨Ck, hCk⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V (hK.image (continuous_brgFin (UI.framesV D V)))
  refine ⟨b * d, max (Ck * (S * C) ^ d) (S * C), δ₀, hδ₀, fun g => ?_⟩
  set fr := UI.framesV D V with hfr
  set x := (UI.brg fr).symm g with hxdef
  have hgx : UI.brg fr x = g := (UI.brg fr).apply_symm_apply g
  obtain ⟨δ, hδ, hδ1, ⟨γ, hγ, hγK, hγb⟩, halt⟩ := hx x
  refine ⟨δ, hδ, hδ1, ?_, ?_⟩
  · have hsplit : γ * x = ((γ * x).1, 1) * (1, (γ * x).2) := Prod.ext (by simp) (by simp)
    have e : UI.brg fr γ * g = UI.brg fr ((γ * x).1, 1) * brgFin fr (γ * x).2 := by
      calc UI.brg fr γ * g = UI.brg fr (γ * x) := by rw [map_mul, hgx]
        _ = UI.brg fr (((γ * x).1, 1) * (1, (γ * x).2)) := congrArg _ hsplit
        _ = _ := map_mul _ _ _
    have hkb := hCk _ ⟨_, hγK, rfl⟩
    have hq : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck := by
      have := GlobalTheory.Grow.quotHeight_le V g ((h1 γ).2 hγ)
      rw [e] at this
      exact this.trans ((GlobalTheory.Grow.height_mul_le V _ _).trans
        (mul_le_mul_of_nonneg_left hkb (GlobalTheory.Grow.height_pos V _).le))
    have hy : ∀ v i j, ‖uMat ((γ * x).1 v) i j‖ ≤ C / δ ^ b := fun v i j =>
      (le_div_iff₀ (pow_pos hδ b)).2 (hγb v i j)
    have hN := (hS (γ * x).1 (C / δ ^ b)).1 hy
    have hN0 : 0 ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) := by unfold normInf; positivity
    have hNb : normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b ≤ S * C := by
      calc _ ≤ S * (C / δ ^ b) * δ ^ b := mul_le_mul_of_nonneg_right hN (pow_pos hδ b).le
        _ = S * C := by rw [mul_assoc, div_mul_cancel₀ _ (pow_pos hδ b).ne']
    have hH := hd _ ((brg_mem_GinfC fr ((γ * x).1, 1)).2 rfl)
    have hHb : GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d) ≤ (S * C) ^ d := by
      rw [pow_mul]
      calc _ ≤ normInf θ V (UI.brg fr ((γ * x).1, 1)) ^ d * (δ ^ b) ^ d :=
            mul_le_mul_of_nonneg_right hH (by positivity)
        _ = (normInf θ V (UI.brg fr ((γ * x).1, 1)) * δ ^ b) ^ d := (mul_pow _ _ _).symm
        _ ≤ (S * C) ^ d := pow_le_pow_left₀ (by positivity) hNb d
    have hCk0 : 0 ≤ Ck := zero_le_one.trans ((GlobalTheory.Grow.one_le_height V _).trans hkb)
    calc GlobalTheory.Grow.quotHeight V g * δ ^ (b * d)
        ≤ GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * Ck * δ ^ (b * d) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = Ck * (GlobalTheory.Grow.height V (UI.brg fr ((γ * x).1, 1)) * δ ^ (b * d)) := by ring
      _ ≤ Ck * (S * C) ^ d := mul_le_mul_of_nonneg_left hHb hCk0
      _ ≤ _ := le_max_left _ _
  · rcases halt with h | ⟨W, hW, hWm⟩
    · exact Or.inl h
    · obtain ⟨r, C₀, hC₀, hNI⟩ := h3 W hW
      refine Or.inr ⟨r, C₀, hC₀, fun m hm => ?_⟩
      have hm' : (UI.brg fr).symm m ∈ (UI.instV fr).NA W :=
        hNI _ (by rwa [(UI.brg fr).apply_symm_apply])
      obtain ⟨γ', hγ', u, k, hk, he, hu⟩ := hWm _ hm'
      refine ⟨UI.brg fr γ', (h1 γ').2 hγ', UI.brg fr (u, 1), brgFin fr k,
        ⟨(brg_mem_GinfC fr (u, 1)).2 rfl, fun τ i j => ?_⟩, hk, (brg_mem_GfC fr (1, k)).2 rfl, ?_⟩
      · calc _ ≤ S * (C * δ) := (hS u (C * δ)).2 hu τ i j
          _ ≤ max (Ck * (S * C) ^ d) (S * C) * δ := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
      · calc m * g = UI.brg fr ((UI.brg fr).symm m * x) := by rw [map_mul, (UI.brg fr).apply_symm_apply, hgx]
          _ = UI.brg fr (γ' * x * ((u, 1) * (1, k))) := by
            rw [he]; exact congrArg (fun z => UI.brg fr (γ' * x * z)) (Prod.ext (by simp) (by simp))
          _ = UI.brg fr γ' * g * UI.brg fr (u, 1) * brgFin fr k := by
            rw [map_mul, map_mul, map_mul, hgx, ← mul_assoc]; rfl

end GlobalTheory.CuspGeo
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

namespace GlobalTheory.Core.Rk.HdGap

theorem bOne_eq (D : D7) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    bOne D τ (j + 1) = (((D.hc τ).b ⟨j, hj⟩ : ℚ) : ℝ) := by
  unfold bOne
  rw [dite_eq_left (by omega)]
  rfl

theorem gap_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := H
  have h := hg τ (j + 1) (by omega) (by omega)
  rwa [bOne_eq D τ (j + 1) hj, bOne_eq D τ j (by omega)] at h

theorem scale_of {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (hCl : 1801 ≤ Cl)
    (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT) :
    1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ∧ 1801 ≤ D.R.r := by
  obtain ⟨hL, -, hmf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩ := H
  have hm : 1801 ≤ D.R.m := by exact_mod_cast hCl.trans hClm
  have hk := D.R.m_add_three_le_k
  refine ⟨?_, by unfold Ranks.r; omega⟩
  have hf1 : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf1
  have hr : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have h1 : 1 ≤ (D.R.f : ℝ) ^ 5 * L := by nlinarith
  calc 1801 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    _ = Cl * (D.R.r : ℝ) ^ 19 * 1 := by ring
    _ ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * L) := by
        apply mul_le_mul_of_nonneg_left h1; nlinarith
    _ = _ := by ring

end GlobalTheory.Core.Rk.HdGap
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem rowColumnShape_of_windowData_width_ge_one : ∀ (D : D7) (C0 : ℝ), 1 ≤ C0 → StandingNumericalData D C0 → DataNW D := by
  intro D C0 hC0 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, h11, h12, h13, h14⟩
  intro u
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hC : 0 < C0 := lt_of_lt_of_le one_pos hC0
  have hpos : 0 < (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 := by positivity
  have : (0 : ℝ) < (D.duS u : ℝ) := lt_of_lt_of_le hpos (h10 u).1
  exact_mod_cast this

end GlobalTheory.Core.Deg
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjResidueSurj
open GlobalTheory.IdemSupport

theorem sigInt_oToS {D : D7} (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem exists_res_and_conj (D : D7) (Pg : Finset (Pl D.host.E))
    (h : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (u u' : ∀ PP : Pl D.host.E, kP PP) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ Pg,
      resS D.host.F PP s = u PP ∧ resS D.host.F PP (sigInt (instOf D) s) = u' PP := by
  classical
  choose a ha using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u PP)
  choose a' ha' using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u' PP)
  have hout : ∀ PP ∈ Pg, cP PP ∉ Pg := fun PP hPP h' =>
    h PP hPP _ h' ((isConjPl_iff _ _).2 rfl)
  let T : Finset (Pl D.host.E) := Pg ∪ Pg.image cP
  let x : Pl D.host.E → 𝓞 D.host.E := fun Q => if Q ∈ Pg then a Q else cO D (a' (cP Q))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun Q : Pl D.host.E => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun Q _ Q' _ hne e => hne (HeightOneSpectrum.ext e)) (fun Q => x Q.1)
  refine ⟨oToS D.host.F D.host.E y, fun PP hPP => ⟨?_, ?_⟩⟩
  · have h1 := hy PP (Finset.mem_union_left _ hPP)
    rw [pow_one] at h1
    have h2 : x PP = a PP := if_pos hPP
    rw [resS_oToS, ← ha PP, ← h2]
    exact Ideal.Quotient.eq.2 h1
  · have h1 := hy (cP PP) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
    rw [pow_one] at h1
    have h2 : x (cP PP) = cO D (a' PP) := by
      have : x (cP PP) = cO D (a' (cP (cP PP))) := if_neg (hout PP hPP)
      rw [this, GlobalTheory.StdFrames.cP_cP]
    have h3 : y - cO D (a' PP) ∈ (cP PP).asIdeal := h2 ▸ h1
    rw [mem_cP, map_sub, cO_cO] at h3
    rw [sigInt_oToS, resS_oToS, ← ha' PP]
    exact Ideal.Quotient.eq.2 h3

end GlobalTheory.ConjResidueSurj
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar → ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → HasTypes R (blockPar P e) := by
  first | exact @GlobalTheory.CoverDS.hasTypes_of_factors | exact GlobalTheory.CoverDS.hasTypes_of_factors | (intros; apply GlobalTheory.CoverDS.hasTypes_of_factors <;> assumption)
end
