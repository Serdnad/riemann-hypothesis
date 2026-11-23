module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellLocalUnitaryDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle008
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196

@[expose] public section

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinEmbStd

variable {D : D7}

theorem eq_of_finHom (V : HSp D) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g' : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    g = g' := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [MonoidHom.mem_ker.1 hg, MonoidHom.mem_ker.1 hg']
  · exact Units.ext (Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective (h i j))

theorem toFinE_inc (e : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd ℚ D.host.E (1 ⊗ₜ[ℚ] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem finAdEquiv_inclR (e : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (inclR (F := D.host.F) (Af D.host.F) e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd D.host.F D.host.E (1 ⊗ₜ[D.host.F] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem toFinE_toAfE_symm (y : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toAfE D).symm y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
  simp [GlobalTheory.BotFormula.toAfE]

theorem finAdEquiv_finHom_rat (V : HSp D) (γ : GA D V) (u : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u = matHom V γ) (i j : Fin V.rank) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      algebraMap D.host.E _ ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
  have : ((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j =
      inclR (F := D.host.F) (Af D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (((matHom V γ : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) = _
    rw [← hγ]
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (inclR (F := D.host.F) (AF D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
    simp [inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rw [this, finAdEquiv_inclR]

theorem exists_std_of_GfC (V : HSp D) (hG : V.gram = 1) (g : GA D V) (hg : g ∈ GfC V) :
    ∃ x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, IsFinPt V g x := by
  let M : Matrix (Fin V.rank) (Fin V.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := (finHom V g).val
  have hM : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) M * M = 1 := by
    have h2 := GlobalTheory.UnitarySplit.finHom_mem V g
    change Formalism.UG.cT _ M * JR (Af D.host.F) V.gram * M = JR (Af D.host.F) V.gram at h2
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hu : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom = 1 := by
    refine GlobalTheory.DefU.ClassFin.unitary_map _ (sigR (Af D.host.F) D.sp.cm.sig) _ ?_ _ hM
    intro y
    apply (GlobalTheory.BotFormula.toAfE D).injective
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, GlobalTheory.BotFormula.toAfE_sgA]
  let x0 : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D) := Formalism.UG.bc (GlobalTheory.BotFormula.toAfE D).symm.toRingHom (finHom V g)
  have hx0 : x0 ∈ Formalism.MainNotions.StandardLatticesGL3.GA D V.rank := by
    change Formalism.UG.cT _ (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _ * (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact hu
  refine ⟨⟨x0, hx0⟩, hg, rfl, fun i j => ?_⟩
  exact (toFinE_toAfE_symm _).symm

theorem exists_GQ_of_rat (V : HSp D) (hG : V.gram = 1) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (hxr : x ∈ ratG D V.rank)
    (g : GA D V) (hg : ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    ∃ γ ∈ GQ V, finHom V γ = finHom V g := by
  rw [GlobalTheory.NormSum.ratG_eq_ratPts] at hxr
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hxr)
  let U : Matrix (Fin V.rank) (Fin V.rank) D.host.E := u.val
  have huV : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U * V.gram * U = V.gram := by
    have h : Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U * 1 * U = 1 := hu
    have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U = Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U := by
      exact Matrix.ext fun i j => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
    rw [hG, hc]; exact h
  have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U).map (inclR (F := D.host.F) (AF D.host.F)) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * U.map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [hcT, JR, ← Matrix.map_mul, ← Matrix.map_mul, huV]
  let γ : GA D V := ⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u, hmem⟩
  refine ⟨γ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨u, huV, rfl⟩), ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [finAdEquiv_finHom_rat V γ u rfl i j, hg i j, ← toFinE_inc]
  congr 1
  rw [← hu']
  rfl

theorem exists_finEmb : ∀ {D : D7} (V : HSp D) (n : ℕ), V.gram = 1 → V.rank = n → ∃ ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V,
    (∀ x, IsFinPt V (ι x) x) ∧ Function.Injective ι ∧ ι.range = GfC V ∧
      ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n := by
  intro D V n hG hr
  subst hr
  have key : ∀ (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank), IsFinPt V g x ↔ g ∈ GfC V ∧ ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) := by
    intro g x
    constructor
    · rintro ⟨h1, e, h2⟩
      exact ⟨h1, fun i j => by simpa using h2 i j⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, rfl, fun i j => by simpa using h2 i j⟩
  choose f hf using fun x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG x rfl
  have uniq : ∀ g x, IsFinPt V g x → g = f x := by
    intro g x hg
    obtain ⟨g1, g2⟩ := (key g x).1 hg
    obtain ⟨f1, f2⟩ := (key _ x).1 (hf x)
    exact eq_of_finHom V g1 f1 fun i j => (g2 i j).trans (f2 i j).symm
  have hfx : ∀ x, ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (((finHom V (f x) : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) :=
    fun x => ((key _ x).1 (hf x)).2
  let ι : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* GA D V :=
    { toFun := f
      map_one' := (uniq 1 1 ((key 1 1).2 ⟨one_mem _, fun i j => by
          simp [Matrix.one_apply, apply_ite]⟩)).symm
      map_mul' := fun x y => (uniq _ _ ((key _ _).2 ⟨mul_mem ((key _ x).1 (hf x)).1 ((key _ y).1 (hf y)).1, fun i j => by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, map_sum, hfx]⟩)).symm }
  refine ⟨ι, hf, ?_, ?_, ?_⟩
  · intro x y hxy
    change f x = f y at hxy
    apply Subtype.ext; apply Units.ext; ext i j
    apply (GlobalTheory.BotFormula.toFinE D).injective
    rw [← hfx x, ← hfx y, hxy]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ((key _ x).1 (hf x)).1
    · intro g hg
      obtain ⟨x, hx⟩ := exists_std_of_GfC V hG g hg
      exact ⟨x, (uniq g x hx).symm⟩
  · intro x
    constructor
    · rintro ⟨γ, hγ, he⟩
      change finHom V γ = finHom V (f x) at he
      obtain ⟨u, -, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
      rw [GlobalTheory.NormSum.mem_ratG]
      refine ⟨(u : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ?_⟩
      refine Matrix.ext fun i j => ?_
      apply (GlobalTheory.BotFormula.toFinE D).injective
      rw [Matrix.map_apply, toFinE_inc, ← hfx x, ← he, finAdEquiv_finHom_rat V γ u hu' i j]
    · intro hxr
      exact exists_GQ_of_rat V hG x hxr (f x) (hfx x)

end GlobalTheory.FinEmbStd
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_bigCell_local_unitary_decomposition : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {K : Type} [Field K] (O : ValuationSubring K) (c : K →+* K), (∀ x, c (c x) = x) → (∀ x ∈ O, c x ∈ O) → (2 : K)⁻¹ ∈ O → (2 : K) ≠ 0 →
  ∀ {d : ℕ} (J : Matrix (Fin d) (Fin d) K), Jᵀ = -J.map c →
  ∀ (b : GL (Fin d) K) (δ : K), c δ = δ →
  (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) i j ∈ O) →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det ≠ 0 →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det⁻¹ ∈ O →
  ∀ M M' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, M * M' = 1 → Mᵀ * dbl J * M.map c = dbl J →
  (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (M *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (M' *ᵥ z)) →
  ∃ P P' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, P * P' = 1 ∧ Pᵀ * dbl J * P.map c = dbl J ∧
    P * diagCols (Fin d) = diagCols (Fin d) ∧
    (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (P *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (P' *ᵥ z)) ∧
    ∃ N : Matrix (Fin d) (Fin d) K,
      N * ((2 : K)⁻¹ • ((P * M).toBlocks₁₁ + (P * M).toBlocks₁₂ + (P * M).toBlocks₂₁ + (P * M).toBlocks₂₂)) = 1 ∧
      ∀ u, GlobalTheory.InertBigCell.InLat O b u → GlobalTheory.InertBigCell.InLat O b (N *ᵥ u) := by
  first | exact @GlobalTheory.InertCellLocal.bigCell_local_step | exact GlobalTheory.InertCellLocal.bigCell_local_step | (intros; apply GlobalTheory.InertCellLocal.bigCell_local_step <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HypPairSelfDual

theorem exists_partner : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : S.V),
    IsSelfDualC S Λ → x ≠ 0 → S.hT x x = 0 →
    ∃ y : S.V, S.hT y y = 0 ∧ S.hT x y = 1 ∧
      ∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y) := by
  intro D S Λ x hΛ hx0 hxx
  set σ : D.host.E →ₐ[D.host.F] D.host.E := D.sp.cm.sig with hσdef
  have hσs : ∀ e : D.host.E, σ e = star e := fun _ => rfl
  have hσ : ∀ e, σ (σ e) = e := fun e => by rw [hσs, hσs, star_star]
  set J : Matrix (Fin S.rank) (Fin S.rank) D.host.E := Matrix.transpose (HSpace.gram S) with hJ
  set co : S.V ≃ₗ[D.host.E] (Fin S.rank → D.host.E) := S.frame.equivFun with hco

  have hform : ∀ a b : S.V, S.hT a b = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co b) (co a) := fun a b => by
    rw [GlobalTheory.RelFlag.hT_eq_form]
    simp only [GlobalTheory.SgAlg.form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.IntPair.co, dotProduct, Matrix.mulVec, hJ,
      Matrix.transpose_apply, hσs, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hco]; ring
  have hframe : ∀ i, co (S.frame i) = Pi.single i 1 := fun i => by
    ext j; simp [hco, Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hherm : ∀ i j, σ (J j i) = J i j := fun i j => by
    have h1 := S.herm.eq (S.frame i) (S.frame j)
    have e1 : S.hT (S.frame i) (S.frame j) = J j i := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    have e2 : S.hT (S.frame j) (S.frame i) = J i j := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [e1, e2] at h1
    rw [hσs]; simpa [starRingEnd_apply] using h1
  have hfg : Λ.FG := hΛ.1.fg
  have hdual : ∀ w, w ∈ Λ ↔ ∀ v ∈ Λ, IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v) := fun w => by
    rw [hΛ.2 w]
    refine forall₂_congr fun v _ => ?_
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v = ∑ i, ∑ j, star (v i) * S.gram i j * w j := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, hJ, Matrix.transpose_apply, hσs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← GlobalTheory.PlaneSplit.mem_range_iff]
    simp [RingHom.mem_range, eq_comm]
  have hfu : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := GlobalTheory.HeckeAdjoint.unramified_host D; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E σ
    (GlobalTheory.AdelicU.isCMExt_host D) hfu
  have hcx0 : co x ≠ 0 := fun h => hx0 (co.injective (by rw [h, map_zero]))
  have hcxx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co x) (co x) = 0 := by rw [← hform]; exact hxx
  obtain ⟨z0, hz0L, hz0⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing D.host.F D.host.E σ hσ S.rank J Λ hfg hherm hdual (co x) hcx0
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module D.host.F D.host.E σ S.rank J Λ hfg (co x) ⟨z0, hz0L, hz0⟩
  obtain ⟨y, hyy, hxy, hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice D.host.F D.host.E σ hσ S.rank J Λ hherm hdual θ hθ (co x) y₀ hcxx hy₀1 hy₀L
  have hconj : ∀ a b, σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun a b => by
    have hh' : ∀ i j, σ (J i j) = J j i := fun i j => hherm j i

    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hh']
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨co.symm y, ?_, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [hform, co.apply_symm_apply]; exact hyy
  · rw [hform, co.apply_symm_apply, ← hconj, hxy, map_one]
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform, co.apply_symm_apply]
    exact (hL _ hz).1
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform]
    change _ • co (co.symm y) ∈ Λ
    rw [co.apply_symm_apply]
    exact (hL _ hz).2

end GlobalTheory.HypPairSelfDual
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

open Matrix GlobalTheory.SmoothForms
open GlobalTheory.Orb (archMat)

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.LeviHC.LineLie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

section Chart

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def sigA (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := A⁻¹ * Xᴴ * A
  map_add' X Y := by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    change A⁻¹ * (c • X)ᴴ * A = c • (A⁻¹ * Xᴴ * A)
    rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]

abbrev LieL (A : Matrix (Fin n) (Fin n) ℂ) : Type := ↥(GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule

def jA (A : Matrix (Fin n) (Fin n) ℂ) : LieL A →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule.subtype


open Classical in
variable (σ J) in
def secA (τ : EmbOver E w) (u : Matrix (Fin n) (Fin n) ℂ) : GAd σ J :=
  if hu : ∃ y : GArch σ J w, archMat σ J τ y = u then embArch σ J w hu.choose else 1

theorem archMat_injective (h : IsCMExt F E σ) (τ : EmbOver E w) : Function.Injective (archMat σ J τ) := fun a b e => by
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
  exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))

theorem secA_archMat (h : IsCMExt F E σ) (τ : EmbOver E w) (y : GArch σ J w) :
    secA σ J τ (archMat σ J τ y) = embArch σ J w y := by
  have hu : ∃ y' : GArch σ J w, archMat σ J τ y' = archMat σ J τ y := ⟨y, rfl⟩
  rw [secA, dite_eq_left hu, archMat_injective h τ hu.choose_spec]

theorem exists_archMat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : sigA (J.map τ.1) u * u = 1) : ∃ y : GArch σ J w, archMat σ J τ y = u := by
  have hA := isUnit_det_map hJ τ.1
  have hu1 : (J.map τ.1)⁻¹ * uᴴ * J.map τ.1 * u = 1 := hu
  have hu2 : uᴴ * J.map τ.1 * u = J.map τ.1 := by
    have := congrArg (J.map τ.1 * ·) hu1
    simpa only [← Matrix.mul_assoc, mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_one] using this
  let v : GL (Fin n) ℂ := ⟨u, (J.map τ.1)⁻¹ * uᴴ * J.map τ.1, mul_eq_one_comm.1 hu1, hu1⟩
  refine ⟨(archEquiv J h τ).symm ⟨v, show _ * _ * _ = _ from hu2⟩, ?_⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]

theorem isLieData (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    IsLieData (sigA (J.map τ.1)) (jA (J.map τ.1)) (secA σ J τ) := by
  have hA := isUnit_det_map hJ τ.1
  have hAh := conjTranspose_map h hJ τ.1
  have anti : ∀ a b, sigA (J.map τ.1) (a * b) = sigA (J.map τ.1) b * sigA (J.map τ.1) a := fun a b => by
    change _ * (a * b)ᴴ * _ = (_ * bᴴ * _) * (_ * aᴴ * _)
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hA]
  refine ⟨anti, ?_, fun a => ?_, Subtype.val_injective, fun X => ⟨fun hX => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change (J.map τ.1)⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J.map τ.1 = 1
    rw [conjTranspose_one, Matrix.mul_one, nonsing_inv_mul _ hA]
  · change _ * (_ * aᴴ * _)ᴴ * _ = a
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hAh]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hA, nonsing_inv_mul _ hA, Matrix.mul_one]
  · refine ⟨⟨X, ?_⟩, rfl⟩
    have h1 : (J.map τ.1)⁻¹ * Xᴴ * J.map τ.1 = -X := hX
    change Xᴴ * J.map τ.1 + J.map τ.1 * X = 0
    rw [← mul_nonsing_inv_cancel_left _ (Xᴴ * J.map τ.1) hA, ← Matrix.mul_assoc (J.map τ.1)⁻¹, h1, Matrix.mul_neg,
      neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    change _ * Y.1ᴴ * _ = -Y.1
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h1, Matrix.mul_neg, nonsing_inv_mul_cancel_left _ _ hA]
  · have hab : sigA (J.map τ.1) (a * b) * (a * b) = 1 := by
      rw [anti, Matrix.mul_assoc, ← Matrix.mul_assoc (sigA (J.map τ.1) a), ha, Matrix.one_mul, hb]
    obtain ⟨ya, rfl⟩ := exists_archMat h hJ τ ha
    obtain ⟨yb, rfl⟩ := exists_archMat h hJ τ hb
    rw [← map_mul, secA_archMat h, secA_archMat h, secA_archMat h, map_mul]

theorem hasLog (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    HasLog (sigA (J.map τ.1)) (jA (J.map τ.1)) :=
  GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData _ _ _ _ _ _ (isLieData h hJ τ)

theorem isLineOf_expMap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Y : LieL (J.map τ.1)) :
    IsLineOf σ J τ Y.1 fun t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y) := fun t => by
  have hA := isUnit_det_map hJ τ.1
  have hY : (t • Y.1)ᴴ * J.map τ.1 + J.map τ.1 * (t • Y.1) = 0 := by
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  have h1 : (NormedSpace.exp (t • Y.1))ᴴ * J.map τ.1 * NormedSpace.exp (t • Y.1) = J.map τ.1 :=
    GlobalTheory.SmoothForms.exp_mem_UH hA hY
  have hu : sigA (J.map τ.1) (NormedSpace.exp (t • Y.1)) * NormedSpace.exp (t • Y.1) = 1 := by
    change (J.map τ.1)⁻¹ * _ * J.map τ.1 * _ = 1
    rw [Matrix.mul_assoc _ _ (J.map τ.1), Matrix.mul_assoc, h1, nonsing_inv_mul _ hA]
  obtain ⟨y, hy⟩ := exists_archMat h hJ τ hu
  refine ⟨y, ?_, hy⟩
  change secA σ J τ (NormedSpace.exp (t • Y.1)) = _
  rw [← hy, secA_archMat h]

theorem sm_of_isSm (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {f : GAd σ J → ℂ} (hf : IsSm σ J f) :
    Sm (expMap (jA (J.map τ.1)) (secA σ J τ)) f := by
  rw [GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind _ _ _ _ _ _ (isLieData h hJ τ) (hasLog h hJ τ) Set.univ Submodule.span_univ]
  intro k Y _ g
  exact hf k (fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y i))
    (fun i => (isLineOf_expMap h hJ τ (Y i)).isRealLine h) g

end Chart

end GlobalTheory.LeviHC.LineLie

end
end
