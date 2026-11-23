module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul (S : HSp D) (g g' : GA D S) : mt S (g * g') = mt S g * mt S g' := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem eq_of_parts {A : Type*} [CommRing A] {e f m m' o : A} (k1 : (e + f) * (m - o) = m - o)
    (k2 : (e + f) * (m' - o) = m' - o) (k3 : e * m = e * m') (k4 : f * m' = f * m) : m = m' := by
  linear_combination (-1 : A) * k1 + k2 + k3 - k4

theorem mt_unit (S : HSp D) (g : GA D S) :
    ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g = (HSpace.gram S).map (incA D) := g.2

theorem gram_mul_conj_inv (S : HSp D) (e : AE D) (g : GA D S) :
    (HSpace.gram S).map (incA D) * (cA D e • mt S g⁻¹) =
      ((e • mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
  have hu := mt_unit S g
  have h1 : mt S g * mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hmap : (e • mt S g).map (cA D) = cA D e • (mt S g).map (cA D) := by
    ext i j; simp [Matrix.map_apply, map_mul]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  calc (HSpace.gram S).map (incA D) * mt S g⁻¹
      = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g * mt S g⁻¹ := by rw [hu]
    _ = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
        rw [Matrix.mul_assoc _ (mt S g), h1, Matrix.mul_one]

theorem eq_of_split_part : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h →
    SuppAt e S h' → (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  intro D S e h h' _ hs hs' hee
  have hJu : IsUnit ((HSpace.gram S).map (incA D)).det := by
    have hd : ((HSpace.gram S).map (incA D)).det = incA D (HSpace.gram S).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]; exact (gram_isUnit_det S).map _
  have hE : e • mt S h = e • mt S h' := by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul]; exact hee i j
  have hN : cA D e • mt S h⁻¹ = cA D e • mt S h'⁻¹ := by
    have h2 := (gram_mul_conj_inv S e h).trans
      ((congrArg (fun X : Matrix (Fin S.rank) (Fin S.rank) (AE D) => (X.map (cA D)).transpose * (HSpace.gram S).map (incA D)) hE).trans
        (gram_mul_conj_inv S e h').symm)
    have h3 := congrArg (fun X => ((HSpace.gram S).map (incA D))⁻¹ * X) h2
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul] using h3
  have a1 : mt S h⁻¹ * mt S h = 1 := by rw [← mt_mul, inv_mul_cancel, mt_one]
  have a2 : mt S h' * mt S h'⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hM : cA D e • mt S h' = cA D e • mt S h := by
    calc cA D e • mt S h' = cA D e • (mt S h' * mt S h⁻¹ * mt S h) := by
          rw [Matrix.mul_assoc, a1, Matrix.mul_one]
      _ = mt S h' * (cA D e • mt S h⁻¹) * mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = mt S h' * (cA D e • mt S h'⁻¹) * mt S h := by rw [hN]
      _ = cA D e • mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, a2, Matrix.one_mul]
  have hMM : mt S h = mt S h' := by
    ext i j
    have k1 := hs i j
    have k2 := hs' i j
    have k3 := hee i j
    have k4 : cA D e * mt S h' i j = cA D e * mt S h i j := by
      have := congrFun (congrFun hM i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at this; exact this
    simp only [Matrix.sub_apply] at k1 k2
    exact eq_of_parts k1 k2 k3 k4
  exact Subtype.ext (Units.ext hMM)

end GlobalTheory.UnitSplit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChrMatch

variable {D : D7}

theorem suppAt_conj (e : AE D) (V : HSp D) (a n : GA D V) (hn : Formalism.L2.Theta.SuppAt e V n) :
    Formalism.L2.Theta.SuppAt e V (a * n * a⁻¹) := by
  have h1 : Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 =
      Formalism.L2.Theta.mt V a * (Formalism.L2.Theta.mt V n - 1) * Formalism.L2.Theta.mt V a⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have h2 : (e + cA D e) • (Formalism.L2.Theta.mt V n - 1) = Formalism.L2.Theta.mt V n - 1 := by
    ext i j; exact hn i j
  intro i j
  have h3 : (e + cA D e) • (Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1) = Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 := by
    rw [h1, ← Matrix.smul_mul, ← Matrix.mul_smul, h2]
  exact congrFun (congrFun h3 i) j

theorem levChi_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ levS V β L) (hk' : k' ∈ levS V β L) : levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have := (levChar D.sp.cm V.gram β L).map_mul ⟨finE V k, hk.2⟩ ⟨finE V k', hk'.2⟩
  unfold levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg Units.val this

theorem levChi_of_red_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0)
    (hQ : L.Q = ∅) {k : GA D V} (hk : ∀ PP ∈ L.Pg, redFn β PP (finE V k) = 1) : levChi V β L k = 1 := by
  have h1 : rTup β L (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, hs, hQ]
  simp

end GlobalTheory.ChrMatch

end
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem concK_of_finX : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  intro hWu D large₂ C' Cl Cg cb Cu cT CT S hC' hCl hFX hL hTF hH
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties S.X
  exact ⟨Formalism.L2.SG.ThmSOwn.concKOf S ⟨hFX, hK, fun u => Formalism.L2.SG.Pf.RegroupPf.neatKu_K2Level D S.X S.Y u hK,
    (hWu D hG S.X).1, (hWu D hG S.X).2, hL, hTF⟩⟩

end GlobalTheory.Core.Diag
end
