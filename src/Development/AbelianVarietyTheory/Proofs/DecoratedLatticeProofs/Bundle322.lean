module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle364
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle314
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvOfNear
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle309
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTrivialCharLevelEltRationalAtTwistPrimes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (c : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * c ∈ 𝒪[k] := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hp : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[k]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : b ∣ ((Nat.card 𝓀[k] ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[k] ^ m, pow_pos Nat.card_pos m, ?_⟩
  have hb' : (algebraMap 𝒪[k] k b) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0
  have : ((Nat.card 𝓀[k] ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) =
      algebraMap 𝒪[k] k (d * a) := by
    rw [← map_natCast (algebraMap 𝒪[k] k), hd, map_mul, map_mul]
    field_simp
  rw [this]
  exact (d * a).2

theorem exists_nat_mul_mem_fin {ι : Type} [Fintype ι] (c : ι → k) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * c i ∈ 𝒪[k] := by
  classical
  choose N hN h using fun i => exists_nat_mul_mem (c i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_mem {n n' m m' : Type} [Fintype n] [Fintype n'] {N : ℕ} (b : Matrix m n k) (b' : Matrix n' m' k)
    (hb : ∀ i a, (N : k) * b i a ∈ 𝒪[k]) (hb' : ∀ a j, (N : k) * b' a j ∈ 𝒪[k]) (x : Matrix n n' k)
    (hx : ∀ i j, x i j ∈ 𝒪[k]) (i : m) (j : m') : ((N * N : ℕ) : k) * (b * x * b') i j ∈ 𝒪[k] := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine sum_mem fun a _ => sum_mem fun c _ => ?_
  have : ((N * N : ℕ) : k) * (b i c * x c a * b' a j) = ((N : k) * b i c) * x c a * ((N : k) * b' a j) := by
    push_cast; ring
  rw [this]
  exact mul_mem (mul_mem (hb i c) (hx c a)) (hb' a j)

end GlobalTheory.FinPl.RdInt

theorem GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) → N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × n => β.b x.1 x.2) (fun x : n' × Fin S.rank => α.b' x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT)
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  refine ⟨K * (N₀ * N₀), Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀), fun t ht hrd => ?_⟩
  have hent := GlobalTheory.FinPl.RdInt.entry_mem β.b α.b' (fun i a => h₀ (Sum.inl (i, a))) (fun a j => h₀ (Sum.inr (a, j)))
    (rd α β t) hrd
  have htw := GlobalTheory.FinPl.HalfInd.wr_rd α β ht
  have hu : IsHalf p.e ((N₀ * N₀) • t) := (GlobalTheory.PlaceModel.isHalf_iff S T).2
    ((GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) _)
  have hui : ∀ i j, toEAf D (((N₀ * N₀) • t) i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j
    have h1 : ((N₀ * N₀) • t) i j = p.sec (((N₀ * N₀ : ℕ) : k) * (β.b * rd α β t * α.b') i j) := by
      rw [← nsmul_eq_mul, map_nsmul, ← GlobalTheory.FinPl.HalfInd.wr_apply, htw]
      rfl
    rw [h1]
    exact GlobalTheory.PlaceCoord.toEAf_mem ((p.int_iff _).1 (hent i j))
  have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) hu) hui
  have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h1).1
  have hh : K • (N₀ * N₀) • t ∈ GlobalTheory.PlaceModel.half S T p.e :=
    (GlobalTheory.PlaceModel.half S T p.e).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) _
  rw [(GlobalTheory.PlaceModel.mem_half S T).1 hh] at h2
  rwa [mul_nsmul']

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
namespace GlobalTheory.FinPl

theorem emb_map_eq_one {D : D7} {S A L : HSp D} (o : OrthDec S A L) {R : Type} [CommRing R] (f : AE D →+* R)
    {a : GA D A} (ha : (Formalism.L2.Theta.mt A a).map f = 1) : (Formalism.L2.Theta.mt S (o.emb (a, 1))).map f = 1 := by
  rw [OrthDec.mt_emb]
  have h1 : Formalism.L2.Theta.mt L (1 : GA D L) = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1]
  have hs := congrArg (fun M : Mx D S.rank S.rank => M.map f) o.sum_eq_one
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f)] at hs ⊢
  rw [ha, Matrix.mul_one, Matrix.mul_one, hs]

theorem emb_mem_grpAt {D : D7} {S A L : HSp D} (o : OrthDec S A L) (P : Pl D → Prop) {a : GA D A}
    (ha : a ∈ grpAt A P) : o.emb (a, 1) ∈ grpAt S P := by
  simp only [grpAt, congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at ha ⊢
  have ha' : (Formalism.L2.Theta.mt A a).map (Ideal.Quotient.mk (idAt D P)) = 1 := by
    have := congrArg Units.val ha
    simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using this
  have key := emb_map_eq_one o (Ideal.Quotient.mk (idAt D P)) ha'
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.map, Formalism.L2.Theta.mt] using key

end GlobalTheory.FinPl


open GlobalTheory.FinPl in
theorem GlobalTheory.FinPl.emb_gl_sumFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (σ : ℕ) (B : BesLev D σ) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)), IsSumFrame B.o B.ζ β β₀ → ∀ g : GL n k, B.o.emb (β.gl g, 1) = β₀.gl (embX 1 g) := by
  intro D k _ _ _ _ p n _ _ σ B β β₀ hsum g
  obtain ⟨hgrp, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨hgrpA, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p B.A n β
  have hmem : B.o.emb (β.gl g, 1) ∈ grpAt B.V₀ (· = p.v) := emb_mem_grpAt B.o _ ((hgrpA _).2 ⟨g, rfl⟩)
  obtain ⟨h, hh⟩ := (hgrp _).1 hmem
  rw [hh]
  congr 1
  set M := (Formalism.L2.Theta.mt B.V₀ (B.o.emb (β.gl g, 1))).map p.pr with hMdef
  have hM : M = β₀.b * h.val * β₀.b' := by rw [hMdef, hh, β₀.gl_mat]

  have hY : (replicateCol (Fin 1) fun i => p.pr (ratV (vecB B.o B.ζ) i)) =
      B.o.jB.map p.pr * replicateCol (Fin 1) fun j => p.pr (ratV B.ζ j) := by
    ext i j

    simp [Matrix.mul_apply, ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat, map_sum, map_mul]
  have hA : M * B.o.jA.map p.pr = B.o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : M * B.o.jB.map p.pr = B.o.jB.map p.pr := by
    have h1 : Formalism.L2.Theta.mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [hMdef, ← Matrix.map_mul, OrthDec.emb_jB, h1, Matrix.mul_one]
  have hemb : ((embX 1 g : GL (n ⊕ Fin 1) k) : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
  have key : M * β₀.b = β₀.b * (embX 1 g).val := by
    rw [hsum, hemb, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hY]
    congr 1
    · rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one,
        Matrix.mul_zero, add_zero, Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hB, Matrix.mul_zero, zero_add, Matrix.mul_one]
  apply Units.ext
  calc h.val = β₀.b' * (β₀.b * h.val * β₀.b') * β₀.b := by
        simp only [Matrix.mul_assoc, β₀.b'b, Matrix.mul_one]
        rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
    _ = β₀.b' * (M * β₀.b) := by rw [← hM, Matrix.mul_assoc]
    _ = β₀.b' * (β₀.b * (embX 1 g).val) := by rw [key]
    _ = (embX 1 g).val := by rw [← Matrix.mul_assoc, β₀.b'b, Matrix.one_mul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.DefCpt

theorem coCpt_X_zero : ∀ (D : D7), GlobalTheory.Unf.CoCpt (D.sp.X 0) := fun D =>
  GlobalTheory.Unf.Inhab.coCpt_of_isAniso
    (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite (D.sp.X 0) (D.sp.X_sig 0) (D.sp.X_def 0 (Nat.zero_le _)))

end GlobalTheory.Unf.DefCpt
end

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

namespace GlobalTheory.SobBaire

open Filter Topology
open scoped Uniformity

theorem exists_bound_of_complete {E : Type} [AddCommGroup E] [Module ℂ E] (p : ℕ → Seminorm ℂ E)
    (hmono : ∀ d x, p d x ≤ p (d + 1) x)
    (hcomp : ∀ u : ℕ → E, (∀ d, ∀ ε > 0, ∃ J, ∀ i ≥ J, ∀ j ≥ J, p d (u i - u j) < ε) →
      ∃ x, ∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0))
    (q : Seminorm ℂ E) (hq : ∀ (u : ℕ → E) (x : E), (∀ d, Tendsto (fun j => p d (u j - x)) atTop (𝓝 0)) →
      ∀ y : ℝ, (∀ j, q (u j) ≤ y) → q x ≤ y) :
    ∃ (d : ℕ) (C : ℝ≥0), ∀ x, q x ≤ C * p d x := by
  letI t : TopologicalSpace E := (SeminormFamily.moduleFilterBasis (𝕜 := ℂ) p).topology
  have hp : WithSeminorms p := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := hp.topologicalAddGroup
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : ContinuousSMul ℂ E := hp.continuousSMul
  haveI : FirstCountableTopology E := hp.firstCountableTopology
  haveI : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := by
    refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    obtain ⟨x, hx⟩ := hcomp u fun d ε hε => by
      have h := (hp.tendsto_nhds _ 0).1 hu d ε hε
      obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
      refine ⟨max N₁ N₂, fun i hi j hj => ?_⟩
      have := hN (j, i) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hj, le_of_max_le_right hi⟩)
      simpa using this
    refine ⟨x, (hp.tendsto_nhds u x).2 fun d ε hε => ?_⟩
    exact (hx d).eventually (gt_mem_nhds hε)
  haveI : BarrelledSpace ℂ E := inferInstance
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    refine IsSeqClosed.isClosed fun u x hu hx => ?_
    exact hq u x (fun d => by
      have := ((hp.continuous_seminorm d).tendsto 0).comp ((tendsto_sub_nhds_zero_iff).2 hx)
      simpa [Function.comp_def] using this) y hu
  have hc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous q hlsc
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous hp q hc
  have hmono' : ∀ d d' x, d ≤ d' → p d x ≤ p d' x := fun d d' x h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _ x)
  refine ⟨s.sup id, C, fun x => (hle x).trans ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ C.2
  exact Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => hmono' _ _ _ (Finset.le_sup (f := id) hi)

end GlobalTheory.SobBaire

namespace GlobalTheory.SobBaire

open Filter Topology

theorem le_mul_sobO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ N : (WO S T → ℂ) → ℝ≥0∞, (∀ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, ∀ g ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, N (f + g) ≤ N f + N g) → (∀ (c : ℂ), ∀ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, N (c • f) = ‖c‖ₑ * N f) → (∀ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, N f ≠ ⊤) → (∀ (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U) → ∀ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, (∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0)) → N f ≤ Filter.liminf (fun j => N (u j)) Filter.atTop) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U, N f ≤ C * sobO ψ θ μ 𝓕 d f := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU N hadd hsmul hfin hlsc
  have hB := GlobalTheory.T.thetaFunctions_open_level_complete_sobolev D ψ hψ θ hθ S T μ 𝓕 hm U hU
  let E := _root_.GlobalTheory.Size.thetaLevel ψ S T U
  have hsf : ∀ d (f : E), sobO ψ θ μ 𝓕 d (f : WO S T → ℂ) ≠ ⊤ := fun d f =>
    GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 f.2.1 d
  let p : ℕ → Seminorm ℂ E := fun d => Seminorm.of (fun f => (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hsf d f) (hsf d g)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsf d f, hsf d g⟩)
        (GlobalTheory.Size.sobO_add_le hψ hθ f.2.1 g.2.1 d))
    (fun c f => by
      show (sobO ψ θ μ 𝓕 d (c • (f : WO S T → ℂ))).toReal = _
      rw [GlobalTheory.Size.sobO_smul, ENNReal.toReal_mul, toReal_enorm])
  have hp : ∀ d (f : E), p d f = (sobO ψ θ μ 𝓕 d (f : WO S T → ℂ)).toReal := fun _ _ => rfl
  let q : Seminorm ℂ E := Seminorm.of (fun f => (N f).toReal)
    (fun f g => by
      rw [← ENNReal.toReal_add (hfin f f.2) (hfin g g.2)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin f f.2, hfin g g.2⟩) (hadd f f.2 g g.2))
    (fun c f => by
      show (N (c • (f : WO S T → ℂ))).toReal = _
      rw [hsmul c f f.2, ENNReal.toReal_mul, toReal_enorm])
  have hq : ∀ f : E, q f = (N f).toReal := fun _ => rfl
  obtain ⟨d, C, hC⟩ := exists_bound_of_complete p
    (fun d f => by
      rw [hp, hp]
      exact ENNReal.toReal_mono (hsf _ f) (GlobalTheory.Size.sobO_mono (Nat.le_succ d)))
    (fun u hu => by
      obtain ⟨f, hf, hlim⟩ := hB (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) fun d ε hε => by
        rcases eq_or_ne ε ⊤ with rfl | hεt
        · exact ⟨0, fun i _ j _ => lt_top_iff_ne_top.2 (hsf d (u i - u j))⟩
        obtain ⟨J, hJ⟩ := hu d ε.toReal (ENNReal.toReal_pos hε.ne' hεt)
        refine ⟨J, fun i hi j hj => ?_⟩
        have := hJ i hi j hj
        rw [hp] at this
        exact (ENNReal.toReal_lt_toReal (hsf d (u i - u j)) hεt).1 this
      refine ⟨⟨f, hf⟩, fun d => ?_⟩
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim d)
      simpa [hp, Function.comp_def] using this)
    q (fun u x hux y hy => by
      have hy0 : 0 ≤ y := (apply_nonneg q (u 0)).trans (hy 0)
      have hconv : ∀ d, Tendsto (fun j => sobO ψ θ μ 𝓕 d ((u j : WO S T → ℂ) - x)) atTop (𝓝 0) := fun d => by
        have h1 := hux d
        simp only [hp] at h1
        rw [← ENNReal.toReal_zero] at h1
        exact (ENNReal.tendsto_toReal_iff (fun j => hsf d (u j - x)) ENNReal.zero_ne_top).1 h1
      have h2 := hlsc (fun j => (u j : WO S T → ℂ)) (fun j => (u j).2) x x.2 hconv
      have h3 : Filter.liminf (fun j => N (u j : WO S T → ℂ)) atTop ≤ ENNReal.ofReal y :=
        Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => by
          rw [← ENNReal.ofReal_toReal (hfin _ (u j).2)]
          exact ENNReal.ofReal_le_ofReal ((hq _).symm.trans_le (hy j) |>.trans_eq' rfl))
      rw [hq]
      exact ENNReal.toReal_le_of_le_ofReal hy0 (h2.trans h3))
  refine ⟨d, C, fun f hf => ?_⟩
  have h := hC ⟨f, hf⟩
  rw [hq, hp] at h
  calc N f = ENNReal.ofReal (N f).toReal := (ENNReal.ofReal_toReal (hfin f hf)).symm
    _ ≤ ENNReal.ofReal (C * (sobO ψ θ μ 𝓕 d f).toReal) := ENNReal.ofReal_le_ofReal h
    _ = C * sobO ψ θ μ 𝓕 d f := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal (GlobalTheory.Size.sobO_ne_top hψ hθ hm.1 hm.2.1 hf.1 d)]

end GlobalTheory.SobBaire
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.EntryAny

open GlobalTheory.Transport.Entry

theorem entry_transport_any : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 < B.R.m) (al : (I.idx a).β i) (be : (I.idx a).β (i + 1)) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀) =
        Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) := by
  intro B X I hI l u a i hm al be P p q p' q' k y k' y' hp hpN hp' hpN' hq hq'
  have hX := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hL := hI.idx_ok a
  have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.Transport.Entry.qOf_pos P.1).ne'
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · obtain ⟨M, hM, H⟩ := exists_modulus hp hp' hq hq' ⟨P.1, hP⟩ (pow_ne_zero (I.cst a).B hq0)
    refine ⟨M, hM, fun M₀ hM₀ x x₀ hx => ?_⟩
    obtain ⟨U, U', hU, hU', h⟩ := H M₀ hM₀ x x₀ hx
    have hu := exp_le_val_qOf (GlobalTheory.UnfoldTwoSided.degOne_bad hX.ok l.pr hI.sel_ok P)
    unfold Formalism.L2.Col.frsF
    simp only [dif_pos hP]
    refine (eq_of_near (P := P.1) _ hq0 (val_qOf_lt_one P.1) (pow_ne_zero (I.cst a).B hq0) (fun κ κ' hκ hκ' z => ?_)
      (hL.xiInv i (by omega) al be P) _ _ U U' (hU.mono hu) (hU'.mono hu) h).symm
    refine xiAt_inFr hX l.pr hI.ch_ok hI.sel_ok hL (by omega) al be P κ κ' ?_ ?_ z
    · rw [hL.depthG P hP, pow_one]
      exact hκ
    · rw [hL.depthG P hP, pow_one]
      exact hκ'
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    refine ⟨Formalism.L2.Col.qOf P.1 ^ (I.cst a).B, pow_pos (GlobalTheory.Transport.Entry.qOf_pos P.1) _, fun M₀ hM₀ x x₀ hx => ?_⟩
    have hd := GlobalTheory.Transport.TwistRead.qread I u a i P hQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I hI l a) p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hx
    set z₀ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ with hz₀
    set z₁ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x with hz₁
    have hMv : P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) ≤
        P.1.valuation B.fields.E (((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).B) := by
      obtain ⟨c, rfl⟩ := hM₀
      rw [Nat.cast_mul, map_mul, Nat.cast_pow]
      refine mul_le_of_le_one_right' ?_
      simpa using P.1.valuation_le_one (K := B.fields.E) (c : 𝓞 B.fields.E)
    have e : z₁ = z₀ + (z₁ - z₀) := by abel
    rw [e]
    refine (hL.xiInv i (by omega) al be P z₀ (z₁ - z₀) fun s l => ?_).symm
    refine intAt_inv_mul (pow_ne_zero _ hq0) ?_
    have e2 : (z₁ - z₀) (Pi.single s 1) l = (LinearMap.toMatrix' z₁ - LinearMap.toMatrix' z₀) l s := by
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, LinearMap.sub_apply, Pi.sub_apply]
    rw [e2]
    exact (hd l s).trans hMv

end GlobalTheory.Transport.EntryAny
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z S → ∀ (N : ℕ) (g : TC.GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P (((g * (show TC.GA B (B.R.N i) from z.1) : TC.GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin (B.R.N i)), Valued.v (adAt B.host.F P (((show TC.GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s - (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s)) ≤ WithZero.exp (-(N : ℤ)) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all | exact GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all | (intros; apply GlobalTheory.Mem.Col2.AdT.LevelAll.exists_level_elt_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology


theorem _root_.GlobalTheory.T.levelCharacter_eq_one_of_deep_at_splitBadPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (n : ℕ), 0 < n → (∀ κ : S.U, S.chi κ ^ n = 1) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x.1 = 1) → ∀ w : GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N w → bc (prV (E := (I.rec7 l Z).host.E) v) x.1 = bc (prV (E := (I.rec7 l Z).host.E) v) w → S.chi x = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep | exact GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep | (intros; apply GlobalTheory.Mem.Col2.AdT.SplitChi.chi_eq_one_of_deep <;> assumption)
end
