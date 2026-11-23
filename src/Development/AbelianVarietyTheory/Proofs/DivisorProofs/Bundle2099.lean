module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormProdSignMulDetSubmatrixSubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel


theorem _root_.GlobalTheory.T.exists_ne_zero_primitiveFrameDatum_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  first | exact @GlobalTheory.ColumnRenumber.phiA_renumber | exact GlobalTheory.ColumnRenumber.phiA_renumber | (intros; apply GlobalTheory.ColumnRenumber.phiA_renumber <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.OneSquareZeta
open ValuativeRel GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isPrimFrame_mul_iff {a : ℕ} {C : Type} [Fintype C] [DecidableEq C] {Λ : Submodule 𝒪[k] (C → k)}
    {X : Matrix (Fin a) C k} {g₀ : GL (Fin a) k} (h₀ : IsPrimFrame Λ (g₀.val * X)) (g : GL (Fin a) k) :
    IsPrimFrame Λ (g.val * X) ↔ g * g₀⁻¹ ∈ KO k (Fin a) := by
  rw [isPrimFrame_iff] at h₀ ⊢
  have hrow : ∀ (M : Matrix (Fin a) (Fin a) k) (Y : Matrix (Fin a) C k) i, (M * Y).row i = M.row i ᵥ* Y :=
    fun M Y i => by funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  have hgX : g.val * X = (g * g₀⁻¹).val * (g₀.val * X) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_assoc g.val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  have hg0X : g₀.val * X = ((g * g₀⁻¹)⁻¹).val * (g.val * X) := by
    rw [hgX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [mem_KO_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h₀.2 ((g * g₀⁻¹).val.row i) (by rw [← hrow, ← hgX]; exact h1 i) j
    · exact h2 (((g * g₀⁻¹)⁻¹).val.row i) (by rw [← hrow, ← hg0X]; exact h₀.1 i) j
  · rintro ⟨hu1, hu2⟩
    refine ⟨fun i => ?_, fun c hc i => ?_⟩
    · show (g.val * X).row i ∈ Λ
      rw [hgX, hrow]; exact vecMul_mem_of_int h₀.1 (fun j => hu1 i j)
    · have h3 := h₀.2 (c ᵥ* (g * g₀⁻¹).val) (by rw [vecMul_vecMul, ← hgX]; exact hc)
      have hc' : c = (c ᵥ* (g * g₀⁻¹).val) ᵥ* ((g * g₀⁻¹)⁻¹).val := by
        rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
      rw [hc']
      change (∑ l, (c ᵥ* (g * g₀⁻¹).val) l * ((g * g₀⁻¹)⁻¹).val l i) ∈ 𝒪[k]
      exact Subring.sum_mem _ fun l _ => mul_mem (h3 l) (hu2 l i)

theorem fFun_mul_left {a : ℕ} {A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    [MeasurableSpace k] [BorelSpace k] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : Fin a ⊕ A' ≃ C)
    (ν : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) (g : GL (Fin a) k) (h : GL C k) :
    fFun μ σ ν Ψ (g.val * (X0 k σ * (invT h).val)) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  exact @GlobalTheory.T.mirabolic_schwartzFunction_left_GL_equivariance k _ _ _ _ _ _ a A' C _ _ _ _
    μ (‹μ.IsHaarMeasure›) σ ν Ψ g h

theorem exists_primFrame {a : ℕ} {C : Type} [Fintype C] [DecidableEq C] (d : C → kˣ)
    (X : Matrix (Fin a) C k) (hX : X.rank = a) : ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  exact GlobalTheory.T.exists_GL_mul_isPrimitiveFrame_diagonalLattice k a C d X hX

theorem exists_unique_shell {ϖ : kˣ} (hϖ : IsUnif ϖ) {a : ℕ} (g : GL (Fin a) k) :
    ∃! m : {m : Fin a → ℤ // Antitone m}, g ∈ shellSet ϖ m.1 := by
  obtain ⟨m, hm, x, hx, y, hy, e⟩ := GlobalTheory.SortedCartan.cartan_antitone k a ϖ hϖ g
  have ht : ∀ m : Fin a → ℤ, GLDoubling.torusElt k (Fin a) ϖ m = diagGL fun i => ϖ ^ m i :=
    fun m => Units.ext (by rw [GLDoubling.val_torusElt, diagGL_val]; simp [Units.val_zpow_eq_zpow_val])
  refine ⟨⟨m, hm⟩, mem_shellSet.2 ⟨x, hx, y, hy, by rw [e, ht]⟩, ?_⟩
  rintro ⟨m', hm'⟩ hmem
  obtain ⟨x', hx', y', hy', e'⟩ := mem_shellSet.1 hmem
  have E : (x'⁻¹ * x) * diagGL (fun i => ϖ ^ m i) * (y * y'⁻¹) = diagGL fun i => ϖ ^ m' i := by
    have h1 : x * diagGL (fun i => ϖ ^ m i) * y = x' * diagGL (fun i => ϖ ^ m' i) * y' := by
      rw [← ht, ← e]; exact e'
    calc _ = x'⁻¹ * (x * diagGL (fun i => ϖ ^ m i) * y) * y'⁻¹ := by group
      _ = _ := by rw [h1]; group
  have E' := congrArg Units.val E
  simp only [Units.val_mul, diagGL_val, Units.val_zpow_eq_zpow_val] at E'
  exact Subtype.ext (Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
    (hϖ ▸ uniformizer_lt_one) m m' hm hm' (x'⁻¹ * x) (mul_mem (inv_mem hx') hx) (y * y'⁻¹)
    (mul_mem hy (inv_mem hy')) (by simpa only [Units.val_mul] using E')).symm

variable [MeasurableSpace k] [BorelSpace k]

theorem bigF_phiA {a : ℕ} {A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ)
    (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (hϖ : IsUnif ϖ) (h : GL C k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (phiA μ σ ν ϖ n (diagLat c) Ψ) (X0 k σ * (invT h).val) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  set X := X0 k σ * (invT h).val with hXdef
  have hΛ : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) := by
    rw [latA, dualLat_diagLat, smul_diagLat]
  have hrank : X.rank = a := by
    have := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 ⟨h, rfl⟩; simpa using this
  obtain ⟨g₀, hg₀⟩ := exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) X hrank
  rw [← hΛ] at hg₀
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := exists_unique_shell hϖ g₀
  set S : Set (GL (Fin a) k) := (fun g => g * g₀⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, phiA μ σ ν ϖ n (diagLat c) Ψ (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card C : ℂ) / 2) = S.indicator (fun _ => fFun μ σ ν Ψ X) g := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, phiA, if_pos ((isPrimFrame_mul_iff hg₀ g).2 hg)]
      exact fFun_mul_left μ σ ν Ψ g h
    · rw [Set.indicator_of_notMem hg, phiA, if_neg (fun h' => hg ((isPrimFrame_mul_iff hg₀ g).1 h')),
        zero_mul, zero_mul]
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν
      ((Fintype.card C : ℂ) / 2) (fun M => phiA μ σ ν ϖ n (diagLat c) Ψ (M * X)) m.1 =
      (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • fFun μ σ ν Ψ X := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => fFun μ σ ν Ψ X) hSm
    rw [e1, setIntegral_const]
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₀⁻¹ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₀⁻¹ * g₀ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₀⁻¹)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₀ = (g * g₀⁻¹)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

end GlobalTheory.OneSquareZeta


open GlobalTheory.OneSquareZeta in
theorem GlobalTheory.OneSquareZeta.bigZeta_phiA_eq_smallZeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ), IsUnif ϖ →
    bigP (haarVol (KO k (Fin a))) ϖ σ ν β (phiA μ σ ν ϖ n (diagLat c) Ψ) = smallP μ σ ν (ν * β) Ψ := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν β ϖ n c Ψ hϖ
  funext h
  rw [bigZetaIntegral_eq, bigF_phiA μ σ ν ϖ n c Ψ hϖ h, splitTheta_fFun_frameFirstBlock_mul, smallP]
  have hC : (Fintype.card C : ℂ) = a + Fintype.card A' := by
    rw [← Fintype.card_congr σ, Fintype.card_sum, Fintype.card_fin]; push_cast; ring
  have e : apow (gdet h) (-(a : ℂ) / 2) * apow (gdet h) ((Fintype.card C : ℂ) / 2) =
      apow (gdet h) ((Fintype.card A' : ℂ) / 2) := by
    rw [← apow_add, hC]; congr 1; ring
  simp only [MonoidHom.mul_apply, Units.val_mul]
  linear_combination (β (gdet h) * ν (gdet h) * smallF μ ν Ψ (Y0 k σ * h.val) : ℂ) * e
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

namespace GlobalTheory.KerConjMean

theorem pow_le_exp_posLog (x : ℝ) (g : ℕ) : x ^ g ≤ Real.exp (g * Real.posLog x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases g with _ | g
    · simp
    · rw [zero_pow (Nat.succ_ne_zero g)]; exact (Real.exp_pos _).le
  · calc x ^ g ≤ |x ^ g| := le_abs_self _
      _ = |x| ^ g := abs_pow x g
      _ = Real.exp (g * Real.log |x|) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos (abs_pos.2 hx) g)]
      _ ≤ Real.exp (g * Real.posLog x) := by
          gcongr
          rw [Real.log_abs]; unfold Real.posLog; exact le_max_right _ _

theorem max_pow_le_exp_posLog (A : ℝ) (hA : 0 < A) (d : ℕ) :
    max 1 A⁻¹ ^ d ≤ Real.exp (d * Real.posLog A⁻¹) := by
  have h1 : max 1 A⁻¹ ≤ Real.exp (Real.posLog A⁻¹) := by
    refine max_le ?_ ?_
    · exact Real.one_le_exp (by unfold Real.posLog; exact le_max_left _ _)
    · calc A⁻¹ = Real.exp (Real.log A⁻¹) := (Real.exp_log (inv_pos.2 hA)).symm
        _ ≤ Real.exp (Real.posLog A⁻¹) := by gcongr; unfold Real.posLog; exact le_max_right _ _
  calc max 1 A⁻¹ ^ d ≤ Real.exp (Real.posLog A⁻¹) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = Real.exp (d * Real.posLog A⁻¹) := (Real.exp_natCast_mul d _).symm

theorem size_bound (K f N b rd Kx W1 W2 a bb c : ℝ) (g : ℕ) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hcf : c ≤ f) (hb3 : 3 ≤ b) (hN1 : 1 ≤ N) (hNb : N ≤ b)
    (hf1 : 1 ≤ f) (hfb : f ≤ b) (hrd0 : 0 ≤ rd) (hrd : rd ≤ b) (ha0 : 0 ≤ a) (haN : a ≤ N) (hbb0 : 0 ≤ bb)
    (hbN : bb ≤ N) (hW1 : W1 ≤ f * N * (8 * b)) (hW2 : W2 ≤ f * N * (8 * b)) (hW10 : 0 ≤ W1) (hW20 : 0 ≤ W2)
    (hg : (g : ℝ) = f * a * bb) (hKx : 0 < Kx)
    (hlogKx : Real.log Kx ≤ K * (W1 + W2 + c * (a + bb) ^ 2 + 1) * Real.log (2 + W1 + W2 + a + bb + c)) :
    Real.log (3 * (2 * (g : ℝ) * rd + 1) ^ g * Kx) ≤ (6 + 126 * K) * f * N * b * Real.log b ∧
      (g : ℝ) ≤ f * N * b := by
  have hb0 : 0 < b := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hlogb : 1 ≤ Real.log b := by
    have : Real.exp 1 ≤ b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hfN1 : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf1 hN1
  have hfNb : 1 ≤ f * N * b := by nlinarith
  have hab : a * bb ≤ N * N := mul_le_mul haN hbN hbb0 hN0
  have hfNN : f * a * bb ≤ f * N * N := by
    have := mul_le_mul_of_nonneg_left hab hf0
    linarith
  have hNN : f * N * N ≤ f * N * b := mul_le_mul_of_nonneg_left hNb (by positivity)
  have hgG : (g : ℝ) ≤ f * N * b := by rw [hg]; linarith
  have hfNb3 : f * N * b ≤ b ^ 3 := by
    have h1 := mul_le_mul hfb hNb hN0 hb0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hb0.le
    calc f * N * b ≤ b * b * b := h2
      _ = _ := by ring
  have hg3 : (g : ℝ) ≤ b ^ 3 := hgG.trans hfNb3
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hrdpos : 0 < 2 * (g : ℝ) * rd + 1 := by have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith
  have hq : 2 * (g : ℝ) * rd + 1 ≤ 3 * b ^ 4 := by
    have h1 := mul_le_mul hg3 hrd hrd0 (by positivity)
    have h2 : (1 : ℝ) ≤ b ^ 4 := one_le_pow₀ (by linarith)
    have h3 : b ^ 3 * b = b ^ 4 := by ring
    linarith
  have hl3 : Real.log 3 ≤ Real.log b := Real.log_le_log (by norm_num) hb3
  have hlq : Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * Real.log b := by
    calc _ ≤ Real.log (3 * b ^ 4) := Real.log_le_log hrdpos hq
      _ = Real.log 3 + 4 * Real.log b := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by linarith
  have hlq0 : 0 ≤ Real.log (2 * (g : ℝ) * rd + 1) := Real.log_nonneg (by
    have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith)
  have hY0 : 0 ≤ f * N * b * Real.log b := by positivity
  have hgl : (g : ℝ) * Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * (f * N * b * Real.log b) := by
    have := mul_le_mul hgG hlq hlq0 (by positivity); linarith
  have hKb : Real.log Kx ≤ 126 * K * (f * N * b * Real.log b) := by
    have hsq : (a + bb) ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hab2 : c * (a + bb) ^ 2 ≤ 4 * (f * N * b) := by
      have := mul_le_mul hcf hsq (by positivity) hf0
      have e : f * (2 * N) ^ 2 = 4 * (f * N * N) := by ring
      linarith
    have hQ1 : W1 + W2 + c * (a + bb) ^ 2 + 1 ≤ 21 * (f * N * b) := by linarith
    have hQ1' : 0 ≤ W1 + W2 + c * (a + bb) ^ 2 + 1 := by positivity
    have hArg0 : 0 < 2 + W1 + W2 + a + bb + c := by linarith
    have hb27 : (27 : ℝ) ≤ b ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hb3 3; norm_num at this; linarith
    have hbb3 : b ≤ b ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have hArg : 2 + W1 + W2 + a + bb + c ≤ 27 * b ^ 3 := by linarith
    have hQ2 : Real.log (2 + W1 + W2 + a + bb + c) ≤ 6 * Real.log b := by
      calc _ ≤ Real.log (27 * b ^ 3) := Real.log_le_log hArg0 hArg
        _ = 3 * Real.log 3 + 3 * Real.log b := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
              show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
        _ ≤ _ := by linarith
    have hQ20 : 0 ≤ Real.log (2 + W1 + W2 + a + bb + c) := Real.log_nonneg (by linarith)
    have := mul_le_mul (mul_le_mul_of_nonneg_left hQ1 hK0) hQ2 hQ20 (by positivity)
    refine hlogKx.trans (this.trans (le_of_eq ?_))
    ring
  refine ⟨?_, hgG⟩
  rw [Real.log_mul (by positivity) hKx.ne', Real.log_mul (by norm_num) (pow_pos hrdpos g).ne', Real.log_pow]
  have hlY : Real.log b ≤ f * N * b * Real.log b := le_mul_of_one_le_left (by linarith) hfNb
  have e : (6 + 126 * K) * f * N * b * Real.log b =
      f * N * b * Real.log b + 5 * (f * N * b * Real.log b) + 126 * K * (f * N * b * Real.log b) := by ring
  rw [e]; linarith

end GlobalTheory.KerConjMean

end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PureTransc

theorem isDomain_tensor (k : Type) [Field k] (σ : Type) (A : Type) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] A) := by
  let P := MvPolynomial σ k
  let K := FractionRing P
  letI : Algebra (P ⊗[k] A) (K ⊗[k] A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)).toAlgebra
  haveI : IsScalarTower P (P ⊗[k] A) (K ⊗[k] A) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  let e : P ⊗[k] A ≃+* MvPolynomial σ A :=
    ((Algebra.TensorProduct.comm k P A).toRingEquiv.trans
      (MvPolynomial.scalarRTensorAlgEquiv).toRingEquiv)
  haveI : IsDomain (P ⊗[k] A) := e.toMulEquiv.isDomain
  have hinj : Function.Injective (algebraMap P (P ⊗[k] A)) :=
    Algebra.TensorProduct.includeLeft_injective (S := P) (algebraMap k A).injective
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[k] A)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] A) (nonZeroDivisors P)) ?_
  rintro _ ⟨p, hp, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero hp (hinj (h.trans (map_zero _).symm))

theorem isIntegral_of_isPullback : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X),
    IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) →
    IsIntegral X' := by
  intro k _ N X X' _ f f' π H

  have chart (x : X) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : IsDomain A)
      (j : Sp A ⟶ X) (_ : IsOpenImmersion j) (q : PrimeSpectrum A),
      j q = x ∧ j ≫ f = spMap (algebraMap k A) := by
    obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f x
    have : Nonempty (Spec (.of A)) := ⟨q⟩
    have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion j
    have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
    exact ⟨A, _, _, this, j, inferInstance, q, hq, hj⟩
  have lift {A : Type} [CommRing A] [Algebra k A] [IsDomain A] (j : Sp A ⟶ X) [IsOpenImmersion j]
      (hj : j ≫ f = spMap (algebraMap k A)) (x' : X') (hx : π x' ∈ Set.range j) :
      ∃ (j₀ : Sp (FractionRing (MvPolynomial (Fin N) k) ⊗[k] A) ⟶ X') (_ : IsOpenImmersion j₀),
        x' ∈ Set.range j₀ := by
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    refine ⟨j₀, hj₀, ?_⟩
    have hr : x' ∈ Set.range (Limits.pullback.fst π j) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨z, rfl⟩ := hr
    exact ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst]⟩
  have hflat : Flat π := by
    refine MorphismProperty.of_isPullback H.flip ?_
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact GlobalTheory.GeomIrr.flat_of_field _
  have : IsReduced X' := by
    have (x' : X') : _root_.IsReduced (X'.presheaf.stalk x') := by
      obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (π x')
      obtain ⟨j₀, _, z, rfl⟩ := lift j hj x' ⟨q, hq⟩
      have := isDomain_tensor k (Fin N) A
      exact isReduced_of_injective
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk X'
  have : IrreducibleSpace X' := by
    obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (genericPoint X)
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    have := isDomain_tensor k (Fin N) A
    have hirr : IsIrreducible (Set.range j₀) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ j₀.continuous.continuousOn
    have hdense : closure (Set.range j₀) = Set.univ := by
      refine Set.eq_univ_of_forall fun x' => ?_
      obtain ⟨y, hy, e⟩ := Flat.generalizingMap π (genericPoint_specializes (π x'))
      have hr : y ∈ Set.range (Limits.pullback.fst π j) := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact ⟨q, hq⟩
      obtain ⟨z, hz⟩ := hr
      have hy' : y ∈ Set.range j₀ :=
        ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst, hz]⟩
      exact closure_mono (Set.singleton_subset_iff.2 hy') (specializes_iff_mem_closure.1 hy)
    refine (irreducibleSpace_def X').2 ?_
    rw [Set.top_eq_univ, ← hdense]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X'

end GlobalTheory.PureTransc
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

namespace GlobalTheory.ChartDomain


open NumberField in
theorem _root_.GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := by
  intro E _ _ _ r X x z hx hz
  have hsmall : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 := by
    by_cases hr : (r : ℝ) = 0
    · simp [hr]
    · have hpos : 0 < (r : ℝ) ^ 2 := by positivity
      calc (r : ℝ) ^ 2 * ‖z‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hpos.le
        _ = 1 / 100 := by field_simp
  exact (_root_.GlobalTheory.dmin_rmul_near_one X x hx (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) (norm_nonneg z) hsmall
    (fun τ a b => _root_.GlobalTheory.ChartNearOne.nmat_entry_le X z τ a b)).1

end GlobalTheory.ChartDomain
end
