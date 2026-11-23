module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsometryVacuumScalarGaussSumIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

open scoped ComplexOrder

namespace GlobalTheory.DefiniteFrame

theorem cT_conj_eq {m p : Type} (M : Matrix m p ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) M = M.conjTranspose := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem Jpq_zero (n : ℕ) : Formalism.UG.Jpq n 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem posSemidef_of_hasSignature {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature G n 0) : G.PosSemidef := by
  obtain ⟨e, P, hP⟩ := h
  rw [cT_conj_eq, Jpq_zero] at hP
  set Q : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ := P.inv
  have hPQ : P.val * Q = 1 := by
    exact P.val_inv
  have hR : G.reindex e e = Q.conjTranspose * 1 * Q := by
    rw [← hP]
    calc G.reindex e e = (P.val * Q).conjTranspose * G.reindex e e * (P.val * Q) := by
          rw [hPQ]; simp
      _ = Q.conjTranspose * (P.val.conjTranspose * G.reindex e e * P.val) * Q := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hpsd : (G.reindex e e).PosSemidef := by
    rw [hR]; exact Matrix.PosSemidef.one.conjTranspose_mul_mul_same Q
  have h2 := hpsd.submatrix e
  have : (G.reindex e e).submatrix e e = G := by
    ext i j; simp
  rwa [this] at h2

end GlobalTheory.DefiniteFrame


open Matrix in
theorem GlobalTheory.DefiniteFrame.frame_signs_pos : ∀ (D : D7) (V : HSp D) (F : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau),
    Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 → ∀ j, F.ε τ j = true := by
  intro D V F τ hs j
  have hG := GlobalTheory.DefiniteFrame.posSemidef_of_hasSignature hs
  have hu : IsUnit (F.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (F.fr_unit τ)
  have hJ : Formalism.REAL.Jm (F.ε τ) = ((F.fr τ)⁻¹).conjTranspose * gramAt D V τ * (F.fr τ)⁻¹ := by
    rw [← F.fr_gram τ, Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul (F.fr τ)ᴴ (by rw [Matrix.det_conjTranspose]; exact hu.star), Matrix.one_mul]
  have hpsd : (Formalism.REAL.Jm (F.ε τ)).PosSemidef := by
    rw [hJ]; exact hG.conjTranspose_mul_mul_same _
  have hd := hpsd.diag_nonneg (i := j)
  by_contra hne
  simp only [Bool.not_eq_true] at hne
  simp [Formalism.REAL.Jm, hne] at hd
  norm_num at hd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.StabMove

theorem mul_entries_mem {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) (hN : ∀ i j, N i j ∈ R) :
    ∀ i j, (M * N) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem R fun k _ => R.mul_mem (hM i k) (hN k j)

def lift {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ⟨M i j, hM i j⟩

theorem lift_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ R) :
    (lift R M hM).map R.subtype = M := by
  ext i j; rfl

def liftGL {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) : GL (Fin n) R where
  val := lift R u.val hu
  inv := lift R (u⁻¹).val hu'
  val_inv := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := R.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul (f := R.subtype), lift_map, lift_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact u.inv_mul

theorem liftGL_map {A : Type} [CommRing A] (R : Subring A) {n : ℕ} (u : GL (Fin n) A)
    (hu : ∀ i j, u.val i j ∈ R) (hu' : ∀ i j, (u⁻¹).val i j ∈ R) :
    Formalism.UG.bc R.subtype (liftGL R u hu hu') = u := by
  ext i j; rfl

end GlobalTheory.StabMove

open GlobalTheory.StabMove in
theorem GlobalTheory.StabMove.finE_mem_St : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  intro D V g β₀ β₁ h₀ h₁ ε φ hε hφ hg hg'
  set R := Formalism.L2.Herm.intAf D.host.F D.host.E with hR
  have hcF : ∀ M : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D), (∀ i j, M i j ∈ R) →
      ∀ i j, ((M.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro M hM i j
    exact GlobalTheory.LevSplit.sigR_int (hM j i)
  have hshape : ∀ (a b : GL (Fin V.rank) (Lev.EAf D)), (∀ i j, a.val i j ∈ R ∧ (a⁻¹).val i j ∈ R) →
      (∀ i j, b.val i j ∈ R ∧ (b⁻¹).val i j ∈ R) →
      ∀ i j, ((1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
        ε • (a * b⁻¹).val + φ • ((b * a⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose) i j ∈ R := by
    intro a b ha hb i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine R.add_mem (R.add_mem (R.mul_mem ?_ ?_) (R.mul_mem hε ?_)) (R.mul_mem hφ ?_)
    · exact R.sub_mem (R.sub_mem R.one_mem hε) hφ
    · rw [Matrix.one_apply]; split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).2) i j
    · apply hcF
      rw [Units.val_mul]
      exact mul_entries_mem R _ _ (fun i j => (hb i j).1) (fun i j => (ha i j).2)
  have hE : ∀ i j, (Formalism.IndefR.Lev.finE V g).val i j ∈ R := by
    have : (Formalism.IndefR.Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl
    rw [this, hg]; exact hshape β₁ β₀ h₁ h₀
  have hE' : ∀ i j, ((Formalism.IndefR.Lev.finE V g)⁻¹).val i j ∈ R := by
    have : ((Formalism.IndefR.Lev.finE V g)⁻¹).val = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
      rw [← map_inv]; rfl
    rw [this, hg']; exact hshape β₀ β₁ h₀ h₁
  set u := β₁⁻¹ * Formalism.IndefR.Lev.finE V g * β₁ with hu
  have hu1 : ∀ i j, u.val i j ∈ R := by
    intro i j
    simp only [hu, Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE) (fun i j => (h₁ i j).1) i j
  have hu2 : ∀ i j, (u⁻¹).val i j ∈ R := by
    intro i j
    have : u⁻¹ = β₁⁻¹ * (Formalism.IndefR.Lev.finE V g)⁻¹ * β₁ := by
      simp only [hu, mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    simp only [Units.val_mul]
    exact mul_entries_mem R _ _ (mul_entries_mem R _ _ (fun i j => (h₁ i j).2) hE') (fun i j => (h₁ i j).1) i j
  refine ⟨liftGL R u hu1 hu2, ?_⟩
  show MulAut.conj β₁ (Formalism.UG.bc R.subtype (liftGL R u hu1 hu2)) = _
  rw [liftGL_map, MulAut.conj_apply, hu]
  group
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrTestVec

theorem exists_fixed_of_subgroup {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] {κ : Type} [Fintype κ] (ψ : AddChar K ℂ) (U₀ : Set K) (hU₀ : IsOpen U₀) (h0 : (0 : K) ∈ U₀)
    (hψ : ∀ t ∈ U₀, ψ t = 1) (B : AddSubgroup (κ → K)) (hBo : IsOpen (B : Set (κ → K)))
    (hBc : IsCompact (B : Set (κ → K))) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → K), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → K) × (κ → K)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  refine ⟨(B : Set (κ → K)).indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (B : Set (κ → K))
    · filter_upwards [hBo.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _
  · intro h
    have := congrFun h 0
    rw [Set.indicator_of_mem (show (0 : κ → K) ∈ (B : Set (κ → K)) from B.zero_mem)] at this
    exact one_ne_zero this
  · have hc : Continuous fun z : ((κ → K) × (κ → K)) × (κ → K) =>
        z.2 ⬝ᵥ z.1.2 + ⅟(2 : K) * (z.1.1 ⬝ᵥ z.1.2) :=
      (continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
    have h1 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, ∀ x ∈ (B : Set (κ → K)),
        x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀ := by
      refine hBc.eventually_forall_of_forall_eventually
        (P := fun (w : (κ → K) × (κ → K)) (x : κ → K) => x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀) fun x _ => ?_
      refine (hU₀.preimage hc).mem_nhds ?_
      simpa using h0
    have h2 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, w.1 ∈ (B : Set (κ → K)) :=
      (hBo.preimage continuous_fst).mem_nhds B.zero_mem
    refine ⟨_, h1.and h2, fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := hw
    funext x
    show ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * (B : Set (κ → K)).indicator (fun _ => (1 : ℂ)) (x + w.1) = _
    by_cases hx : x ∈ (B : Set (κ → K))
    · rw [hψ _ (hw1 x hx), one_mul, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x + w.1 ∈ (B : Set (κ → K)) from B.add_mem hx hw2)]
    · have hx' : x + w.1 ∉ (B : Set (κ → K)) := fun h => hx (by simpa using B.sub_mem h hw2)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]

theorem exists_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  intro F _ _ v ψ hψ κ _
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  refine exists_fixed_of_subgroup ψ U₀ U₀.isOpen U₀.zero_mem hU₀
    (AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup) ?_ ?_
  · exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  · exact isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

end GlobalTheory.SchrTestVec
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrSBFin

theorem isLocallyConstant_addChar {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [U₀.mem_nhds_zero] with s hs
  rw [AddChar.map_add_eq_mul, hU₀ s hs, mul_one]

theorem schr_mem_SB_of {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (ψ : AddChar K ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (w : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → K)) :
    GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → K) := by
  obtain ⟨hlc, hcs⟩ := hφ
  have h1 : IsLocallyConstant fun x : κ → K => ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) :=
    (isLocallyConstant_addChar ψ hψ).comp_continuous
      ((continuous_id.dotProduct continuous_const).add continuous_const)
  have h2 : IsLocallyConstant fun x : κ → K => φ (x + w.1) := hlc.comp_continuous (continuous_id.add continuous_const)
  have h3 : HasCompactSupport fun x : κ → K => φ (x + w.1) := hcs.comp_homeomorph (Homeomorph.addRight w.1)
  exact ⟨h1.mul h2, h3.mul_left⟩

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v ψ hψ κ _ w φ hφ
  exact schr_mem_SB_of ψ hψ w φ hφ

end GlobalTheory.SchrSBFin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.heisenbergLatticeVacuumFn_hasCompactSupport : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)))
    (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    IsCompact (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) → HasCompactSupport (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  first | exact @GlobalTheory.HeisLatVac.vacFn_hasCompactSupport_of_isCompact | exact GlobalTheory.HeisLatVac.vacFn_hasCompactSupport_of_isCompact | (intros; apply GlobalTheory.HeisLatVac.vacFn_hasCompactSupport_of_isCompact <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.isLocallyConstant_heisenberg_lattice_vacuum_function : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, χ (u + u) = 1) → IsLocallyConstant (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  first | exact @GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place | exact GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place | (intros; apply GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteWeilRep_eq_latticeIntertwiner_mul_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (χS χT : (AE D)ˣ →* Circle) (nS nT : ℕ), IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS nS → ResEta D χT nT → ∀ of : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsFinWeil ψ S T ΛS ΛT χS χT of → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)), IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε, IsHalfIdem D ε → ∀ (g : GA D S) (h : GA D T) (x y : (AE D)ˣ), (x : AE D) = ε * (Formalism.L2.Theta.mt S g).det + (1 - ε) → (y : AE D) = ε * (Formalism.L2.Theta.mt T h).det + (1 - ε) → ∀ f : thetaSub ψ S T, of (g, h) f = ((((χT x)⁻¹ * χS y : Circle) : ℂ)) • (Om (g, h) f : WO S T → ℂ) := by
  first | exact @GlobalTheory.FinWeilForm.finWeil_eq | exact GlobalTheory.FinWeilForm.finWeil_eq | (intros; apply GlobalTheory.FinWeilForm.finWeil_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalIsometry_vacuumScalar_gaussSum_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → Function.Bijective (fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) → Integrable (gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ))) volume → ∀ κ : ℂ, (∀ f : thetaSub ψ S T, Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x, (f : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x) = κ * ((sumOp (opF hψ.1 S T w) (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) f : thetaSub ψ S T) : WO S T → ℂ) x) → ∀ (n : ℕ) (t : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E), (∀ k, b * t k * a - t k ∈ latQ S T ΛS ΛT) → (∀ y, b * y * a - y ∈ latQ S T ΛS ΛT → ∃! k, y - t k ∈ latQ S T ΛS ΛT) → ∃ r : ℝ, 0 < r ∧ (∑ k, gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * t k * a - t k)) (t k)) * ∫ v, gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v = r * κ := by
  first | exact @GlobalTheory.RatTrace.gauss_mul_integral | exact GlobalTheory.RatTrace.gauss_mul_integral | (intros; apply GlobalTheory.RatTrace.gauss_mul_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  first | exact @GlobalTheory.BCT.TrKer.hop_phiFun_comm | exact GlobalTheory.BCT.TrKer.hop_phiFun_comm | (intros; apply GlobalTheory.BCT.TrKer.hop_phiFun_comm <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.definiteUnitaryRationalPoint_split_finite_infinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n, ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧ ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := by
  first | exact @GlobalTheory.BCT.RatSplit.ratU_split | exact GlobalTheory.BCT.RatSplit.ratU_split | (intros; apply GlobalTheory.BCT.RatSplit.ratU_split <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_definiteUnitaryRationalPoint_finite_and_infinite_parts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), ∃ r ∈ ratU E n, splitFin E n r = finPt γ ∧ ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ.1 := by
  exact @GlobalTheory.BCT.RatPt.ratPt
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → (∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) → ∃ T : Wsp lam →ₗ[ℂ] (UA E n → ℂ), T ≠ 0 ∧ (∀ w, T w ∈ π) ∧ ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w) := by
  first | exact @GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining | exact GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining | (intros; apply GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining <;> assumption)
end
