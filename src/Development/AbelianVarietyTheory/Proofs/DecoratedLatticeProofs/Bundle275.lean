module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle388
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle235
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle255
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Matrix.ColumnRowPartitioned
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDensSup

theorem sup_le_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, ∀ w, ‖f w‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU
  haveI : LocallyCompactSpace (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.1
  obtain ⟨K₀, hK₀n, hK₀U, hK₀c⟩ := local_compact_nhds (hU.mem_nhds U.zero_mem)
  obtain ⟨C, hC⟩ := GlobalTheory.LevelSupBound.pointwise (S := S) (T := T) hψ hθ hK₀n hK₀c
  refine ⟨Module.finrank ℝ (GlobalTheory.FockCompare.RW T S), C, fun f hf w => ?_⟩
  have h := hC μ 𝓕 hm 1 one_pos f hf.1 (fun u hu hinf => by rw [one_smul]; exact hf.2 u (hK₀U hu) hinf) w
  refine h.trans (le_of_eq ?_)
  congr 1
  simp

end GlobalTheory.ThetaDensSup
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitLeviDet

theorem smul_iff {R : Type*} [CommRing R] {m n : Type*} (ε : R) (N : Matrix m n R) :
    ε • N = N ↔ ∀ i j, ε * N i j = N i j :=
  ⟨fun h i j => congrFun (congrFun h i) j, fun h => by ext i j; exact h i j⟩

theorem smul_sandwich {R : Type*} [CommRing R] {k l m n : Type*} [Fintype l] [Fintype m] (ε : R)
    (P : Matrix k l R) (N : Matrix l m R) (Q : Matrix m n R) (hN : ε • N = N) : ε • (P * N * Q) = P * N * Q := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hN]

theorem det_supp {R : Type*} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (M : Matrix (Fin n) (Fin n) R)
    (hM : ε • (M - 1) = M - 1) : (1 - ε) * M.det = 1 - ε := by
  have hid : IsIdempotentElem (1 - ε) := by unfold IsIdempotentElem; linear_combination hε
  have hf : (1 - ε) • M = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    have h0 : (1 - ε) • (M - 1) = 0 := by rw [sub_smul, one_smul, hM, sub_self]
    rw [smul_sub, sub_eq_zero] at h0
    exact h0
  have key := congrArg Matrix.det hf
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at key
  cases n with
  | zero => rw [Matrix.det_isEmpty, mul_one]
  | succ k => rw [hid.pow_succ_eq] at key; exact key

variable {D : D7}

def locU (e : AE D) (h : e * e = e) (t : (AE D)ˣ) : (AE D)ˣ where
  val := e * t + (1 - e)
  inv := e * ↑t⁻¹ + (1 - e)
  val_inv := by
    have htu : (t : AE D) * ↑t⁻¹ = 1 := t.mul_inv
    linear_combination e * htu + ((t : AE D) * ↑t⁻¹ - t - ↑t⁻¹ + 1) * h
  inv_val := by
    have htu : (↑t⁻¹ : AE D) * t = 1 := t.inv_mul
    linear_combination e * htu + ((↑t⁻¹ : AE D) * t - ↑t⁻¹ - t + 1) * h

theorem locU_val (e : AE D) (h : e * e = e) (t : (AE D)ˣ) : (locU e h t : AE D) = e * t + (1 - e) := rfl

def detU (V : HSp D) (g : GA D V) : (AE D)ˣ where
  val := (mt V g).det
  inv := (mt V g⁻¹).det
  val_inv := by rw [← Matrix.det_mul, GlobalTheory.MixModel.mt_mul_inv, Matrix.det_one]
  inv_val := by rw [← Matrix.det_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.det_one]

theorem detU_val (V : HSp D) (g : GA D V) : (detU V g : AE D) = (mt V g).det := rfl

theorem det_adj {n : ℕ} (y : Mx D n n) : (adj y).det = cA D y.det := by
  rw [adj, Matrix.det_transpose]; exact (RingHom.map_det (cA D) y).symm

theorem one_add_sub {n : ℕ} (M : Mx D n n) : 1 + (M - 1) = M := by abel

end GlobalTheory.SplitLeviDet

open GlobalTheory.SplitLeviDet

theorem GlobalTheory.SplitLeviDet.emb0Part : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) := by
  intro D S S₀ ρ d e he
  obtain ⟨h1, h2, -⟩ := he
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hεε : (e + cA D e) * (e + cA D e) = e + cA D e := by linear_combination h1 + 2 * h2 + hce
  have hcε : cA D (e + cA D e) = e + cA D e := by rw [map_add (f := _), hcc, add_comm]
  intro g hg
  have hN : (e + cA D e) • (mt S₀ g - 1) = mt S₀ g - 1 := (smul_iff _ _).2 hg
  have hm : mt S (d.emb0 g) = (1 : Mx D S.rank S.rank) + d.j0 ⬝ (mt S₀ g - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding]; conv_rhs => rw [← d.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  have hdet : (mt S (d.emb0 g)).det = (mt S₀ g).det := by
    rw [hm, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one, one_add_sub]
  refine ⟨?_, locU e h1 (detU S₀ g), ?_, ?_⟩
  · intro i j
    rw [hm, add_sub_cancel_left]
    exact (smul_iff _ _).1 (smul_sandwich _ _ _ _ hN) i j
  · rw [IsDetAt, locU_val, detU_val]
  · rw [IsDetAt, locU_val, detU_val, hdet]


theorem GlobalTheory.SplitLeviDet.leviPart : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := by
  intro D S S₀ ρ d e he
  obtain ⟨h1, h2, -⟩ := he
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hεε : (e + cA D e) * (e + cA D e) = e + cA D e := by linear_combination h1 + 2 * h2 + hce
  have hcε : cA D (e + cA D e) = e + cA D e := by rw [map_add (f := _), hcc, add_comm]
  intro χ n hχ hR a ha
  have hA : (e + cA D e) • (a.1 - 1 : Mx D ρ ρ) = (a.1 - 1 : Mx D ρ ρ) := by
    ext i j
    exact ha i j
  have hI : (e + cA D e) • ((a⁻¹).1 - 1 : Mx D ρ ρ) = ((a⁻¹).1 - 1 : Mx D ρ ρ) := by
    have hinv : ((a⁻¹).1 - 1 : Mx D ρ ρ) = -((a⁻¹).1 ⬝ (a.1 - 1 : Mx D ρ ρ)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Units.inv_mul, neg_sub]
    rw [hinv, smul_neg, ← Matrix.mul_smul, hA]
  have hB : (e + cA D e) • (adj (a⁻¹).1 - 1 : Mx D ρ ρ) = (adj (a⁻¹).1 - 1 : Mx D ρ ρ) := by
    have h' : (adj (a⁻¹).1 - 1 : Mx D ρ ρ) = adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [adj_sub, adj_one]
    rw [h']
    calc (e + cA D e) • adj ((a⁻¹).1 - 1 : Mx D ρ ρ) = cA D (e + cA D e) • adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [hcε]
      _ = adj ((e + cA D e) • ((a⁻¹).1 - 1 : Mx D ρ ρ)) := (adj_smul _ _).symm
      _ = adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [hI]
  have hm : mt S (d.levi a) = (1 : Mx D S.rank S.rank) + (d.jX ⬝ (a.1 - 1 : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY) := by
    rw [d.mt_levi a]; conv_rhs => rw [← d.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  have hdet : (mt S (d.levi a)).det = a.1.det * cA D (a⁻¹).1.det := by
    have h' : d.jX ⬝ (a.1 - 1 : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY =
        Matrix.fromCols d.jX d.jY ⬝ Matrix.fromRows ((a.1 - 1 : Mx D ρ ρ) ⬝ d.pX) ((adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY) := by
      rw [Matrix.fromCols_mul_fromRows, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hm, h', Matrix.det_one_add_mul_comm, Matrix.fromRows_mul_fromCols]
    simp only [Matrix.mul_assoc, d.pX_jX, d.pX_jY, d.pY_jX, d.pY_jY, Matrix.mul_one, Matrix.mul_zero]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp only [add_zero, one_add_sub]
    rw [Matrix.det_fromBlocks_zero₂₁, det_adj]
  have hs : (1 - (e + cA D e)) * a.1.det = 1 - (e + cA D e) := det_supp _ hεε _ hA
  set t := Matrix.GeneralLinearGroup.det a with ht
  have ht1 : (t : AE D) = a.1.det := rfl
  have ht2 : ((t⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det := by rw [ht, ← map_inv]; rfl
  refine ⟨?_, locU e h1 (t * Units.map (cA D).toMonoidHom t⁻¹), ?_, ?_⟩
  · have X : (e + cA D e) • (mt S (d.levi a) - 1) = mt S (d.levi a) - 1 := by
      rw [hm, add_sub_cancel_left, smul_add, smul_sandwich _ _ _ _ hA, smul_sandwich _ _ _ _ hB]
    intro i j
    exact congrFun (congrFun X i) j
  · rw [IsDetAt, locU_val, hdet, Units.val_mul, Units.coe_map, ht1, ht2]; rfl
  · set w := locU (cA D e) hce t with hw
    have hdc : cA D ((t⁻¹ : (AE D)ˣ) : AE D) * cA D (t : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hs' : (1 - (e + cA D e)) * (t : AE D) = 1 - (e + cA D e) := by rw [ht1]; exact hs
    have key : t = locU e h1 (t * Units.map (cA D).toMonoidHom t⁻¹) * (w * Units.map (cA D).toMonoidHom w) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.coe_map, locU_val, Units.val_mul, Units.coe_map, hw, locU_val]
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_add (f := _), map_mul, map_sub, map_one, hcc]
      linear_combination (-((e * t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) + 1 - e) * (t * cA D (t : AE D) - t - cA D (t : AE D) + 1) +
          ((t : AE D) ^ 2 * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - t + 1))) * h2 -
        ((t : AE D) * cA D ((t⁻¹ : (AE D)ˣ) : AE D) * cA D (t : AE D) - t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - cA D (t : AE D) + 1) * h1 -
        e * t * hdc + hs'
    conv_rhs => rw [key]
    rw [map_mul, map_mul, GlobalTheory.ConjAdjWeil.chi_conj hR w, mul_inv_cancel, mul_one]

theorem GlobalTheory.splitLeviDet : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) ∧ ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := fun D S S₀ ρ d e he =>
  ⟨GlobalTheory.SplitLeviDet.emb0Part D S S₀ ρ d e he, GlobalTheory.SplitLeviDet.leviPart D S S₀ ρ d e he⟩
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrCombAny

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem real_part {S T : HSp D} (x : WO S T) : (GlobalTheory.FinTranslate.eInf D • x : WO S T).map (finPart D) = 0 := by
  ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (x i j)

theorem fin_part {S T : HSp D} (x : WO S T) : ((1 - GlobalTheory.FinTranslate.eInf D) • x : WO S T).map (infPart D) = 0 := by
  ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (x i j)

theorem psi_fin_eq {S T : HSp D} {w : WO S T} (hw : w.map (infPart D) = 0) (x : WO S T) :
    ψ (symplOH S T w x) = ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) := by
  have hx : x = GlobalTheory.FinTranslate.eInf D • x + (1 - GlobalTheory.FinTranslate.eInf D) • x := by
    rw [← add_smul, add_sub_cancel, one_smul]
  conv_lhs => rw [hx]
  rw [GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_fin_real hw (real_part x), zero_add]

theorem exists_orth_any {S T : HSp D} (hψ : IsStdChar D ψ (-1)) (s : Finset (WO S T)) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ w ∈ U, w.map (infPart D) = 0 → ∀ x ∈ s, ψ (symplOH S T w x) = 1 := by
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∀ x ∈ s, ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1}
      zero_mem' := fun x _ => by rw [GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb x hx => by
        rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
      neg_mem' := fun {a} ha x hx => by
        have := AddChar.map_add_eq_mul ψ (symplOH S T a ((1 - GlobalTheory.FinTranslate.eInf D) • x))
          (symplOH S T (-a) ((1 - GlobalTheory.FinTranslate.eInf D) • x))
        rw [← GlobalTheory.FinTranslate.symplOH_add_left, add_neg_cancel, GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one,
          ha x hx, one_mul] at this
        exact this.symm }
  refine ⟨U, ?_, fun w hw hw' x hx => (psi_fin_eq hw' x).trans (hw x hx)⟩
  have e : (U : Set (WO S T)) = ⋂ x ∈ s, {w | ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1} := by
    ext w
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  exact isOpen_biInter_finset fun x _ => GlobalTheory.FrComb.isOpen_ker hψ (fin_part x)

theorem contDiff_psi {S T : HSp D} (hψ : IsStdChar D ψ (-1)) {n : ℕ} {L : (Fin n → ℝ) →+ WO S T} (hL : Continuous L)
    (hLf : ∀ t, (L t).map (finPart D) = 0) (x : WO S T) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => ψ (symplOH S T (L t) x) := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  let φ : (Fin n → ℝ) →+ ℂ :=
    { toFun := fun t => lam (symplOH S T (L t) x)
      map_zero' := by rw [map_zero L, GlobalTheory.FinTranslate.symplOH_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L, GlobalTheory.FinTranslate.symplOH_add_left, map_add (f := _)] }
  have hφ := GlobalTheory.WeilVacMove.contDiff_additive φ (hl.comp ((GlobalTheory.FinTranslate.continuous_symplOH S T x).comp hL))
  have e : (fun t => ψ (symplOH S T (L t) x)) = fun t => Complex.exp (φ t) :=
    funext fun t => hlam _ (GlobalTheory.WeilVacMove.snd_symplOH S T (L t) x (Or.inl (hLf t)))
  rw [e]
  exact hφ.cexp

theorem biTheta_combL {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) (c : WO A S →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => K u' v) u) := by
  have e : (fun u v => comb ψ A S c (fun u' => K u' v) u) =
      fun u v => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * K (u + x) v) := by
    funext u v; exact GlobalTheory.FrComb.comb_apply c _ u
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply]
    exact continuous_finsetSum _ fun x _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH A S x).comp continuous_fst)).mul
        (hK.cont.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S (u + L t) x) * K (u + L t + x) (v + L' t))) =
        fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * (ψ (symplOH A S (L t) x) * K (u + x + L t) (v + L' t))) := by
      funext t
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_const.mul
      ((contDiff_psi hψ hL hLf x).mul (hK.smooth n L L' hL hL' hLf hL'f (u + x) v)))
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc, hK.quasiL, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH A S (ratW S A γ) x + symplOH A S u x) * ψ (-(symplOH A S (ratW S A γ) u + symplOH A S (ratW S A γ) x)) =
        ψ (-(symplOH A S (ratW S A γ) u)) * ψ (symplOH A S u x) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c x * K (u + x) v) * key
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hK.quasiR]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    obtain ⟨V, hV, hVf⟩ := exists_orth_any hψ c.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' v)
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    refine ⟨U, hU, fun a ha ha' u => ?_⟩
    funext v
    simp only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e3 := congrFun (hUf a ha ha' (u + x)) v
    simp only [heisO] at e3
    rw [← e3]
    ring

theorem biTheta_combR {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) (c : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (K u) v) := by
  have e : (fun u v => comb ψ S A' c (K u) v) =
      fun u v => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * K u (v + y)) := by
    funext u v; exact GlobalTheory.FrComb.comb_apply c _ v
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply]
    exact continuous_finsetSum _ fun y _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH S A' y).comp continuous_snd)).mul
        (hK.cont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' (v + L' t) y) * K (u + L t) (v + L' t + y))) =
        fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * (ψ (symplOH S A' (L' t) y) * K (u + L t) (v + y + L' t))) := by
      funext t
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm v, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun y _ => contDiff_const.mul (contDiff_const.mul
      ((contDiff_psi hψ hL' hL'f y).mul (hK.smooth n L L' hL hL' hLf hL'f u (v + y))))
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hK.quasiL]
    ring
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [add_assoc, hK.quasiR, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH S A' (ratW A' S γ) y + symplOH S A' v y) * ψ (-(symplOH S A' (ratW A' S γ) v + symplOH S A' (ratW A' S γ) y)) =
        ψ (-(symplOH S A' (ratW A' S γ) v)) * ψ (symplOH S A' v y) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c y * K u (v + y)) * key
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    refine ⟨U, hU, fun a ha ha' v => ?_⟩
    funext u
    simp only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e3 := congrFun (hUf a ha ha' (v + y)) u
    simp only [heisO] at e3
    rw [← e3]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    obtain ⟨V, hV, hVf⟩ := exists_orth_any hψ c.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' u)

theorem biTheta_biComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (C : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' C → ∀ (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ), IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) := by
  intro D ψ hψ A S A' C hC c c'
  exact biTheta_combL hψ (biTheta_combR hψ hC c') c

end GlobalTheory.FrCombAny

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

theorem iwasawa_flag_move : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  intro D S S₀ ρ d L L₀ v hT hL hM h hh
  obtain ⟨⟨ε, hεε, hεc, hεI, hε, -⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hMsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v h⁻¹ (inv_mem hh) _ hL
  set M := (latV S L (· = v)).comap (Matrix.mulVecLin (mt S h⁻¹)).toAddMonoidHom with hMdef
  obtain ⟨b, hbu, hbI, hbM, c', hc'M, hpair⟩ := GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε hT M hMsd
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.exists_integral_trace_idempotent_at_tamePlace D v ε hεε hεc hεI hε hT
  obtain ⟨c'', hc''M, hpair', hiso⟩ := GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε M hMsd w hw hw1 b c' hbI hbM hc'M hpair
  obtain ⟨α, β, hα, hβ, hαβ, hX, hY⟩ := GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place D S S₀ ρ d L L₀ v ε hεε hεc hεI hε hL hM
  have hc''I : ∀ i j, c'' i j ∈ idAt D (· = v) := fun i j => hMsd.1 _ (hc''M j) i
  obtain ⟨q, hq, hqX, hqα, hqβ⟩ := GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames D S S₀ ρ d v ε hεε hεc hεI hε α β b c'' hα hβ hαβ hbI hc''I hpair' hiso
  have hNsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v q hq M hMsd
  obtain ⟨Λ₀, hΛ, hz⟩ := GlobalTheory.T.selfDualLatticeAtPlace_splits_hyperbolic_plus_core D S S₀ ρ d v ε hεε hεc hεI hε _ α β hNsd hα hβ hαβ
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jX i (α i) ∈ M
      rw [hqα]; exact hbM i)
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jY i (cA D (β i)) ∈ M
      rw [hqβ]; exact hc''M i)
  refine ⟨q, hq, ⟨b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ), fun i j hji => ?_, hqX⟩, Λ₀, hΛ, fun z hz' => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_diagonal, hbu i j hji, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  · have e1 : (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v)) ↔
        z ∈ (M.comap (Matrix.mulVecLin (mt S q)).toAddMonoidHom) := by
      rw [AddSubgroup.mem_comap, hMdef, AddSubgroup.mem_comap]
      change _ ↔ mt S h⁻¹ *ᵥ (mt S q *ᵥ z) ∈ _
      rw [Matrix.mulVec_mulVec, ← mt_mul]
    rw [e1, hz z hz']
    refine and_congr (forall_congr' fun i => (hX i _ (mulVec_mem_idAt _ hz' i)).symm)
      (and_congr (forall_congr' fun i => (hY i _ (mulVec_mem_idAt _ hz' i)).symm) Iff.rfl)

end GlobalTheory.IwaPlace

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

theorem _root_.GlobalTheory.T.twistPlaceChainStepDatum_mul_conj_eq_indicator : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v r mu x * (starRingEnd ℂ) (phiQ v r mu x) = (GlobalTheory.NrmVol.suppQ v r).indicator (fun _ => (1 : ℂ)) x := by
  first | exact @GlobalTheory.NrmVol.phiQ_mul_conj_eq_indicator | exact GlobalTheory.NrmVol.phiQ_mul_conj_eq_indicator | (intros; apply GlobalTheory.NrmVol.phiQ_mul_conj_eq_indicator <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extendByZero_source_tensor_column_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), extFun α₀ β (tensCol Ψ a) = o.boxS T (extFun α β Ψ) (GlobalTheory.FinPl.ExtZero.colFun β ζ a) := by
  exact @GlobalTheory.FinPl.ExtZero.extFun_tensCol_sum
end
