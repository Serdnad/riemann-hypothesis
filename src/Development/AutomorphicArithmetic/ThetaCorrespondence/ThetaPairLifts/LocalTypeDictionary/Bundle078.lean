module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle013
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle076
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle028
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle062
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle609
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle075
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle065
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle723
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle331
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle070
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotAlgI
theorem classSum_kernel_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
      Finsupp.mapDomain Prod.fst k = dg → IsAlgebraic ℚ (X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h x / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX dg
  obtain ⟨Ω, hΩ, hjet⟩ := _root_.GlobalTheory.T.bottom_translate_jets_algebraic hP hI hL hX dg
  refine ⟨Ω, hΩ, fun t x hx h hh k hk => ?_⟩
  obtain ⟨n, c, w, hc, hw, hf⟩ := _root_.GlobalTheory.T.bottom_fourier_coeff_heisenberg_expansion hP hI hL hX t
  choose n' c' w' hc' hw' hm using fun p => _root_.GlobalTheory.T.twisted_moved_translate_algebraic hP hI hL hX t x hx h hh (w p) (hw p)
  have hψ := hX.is.isVac.1
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  set φ : PolF D WW.rank A.rank := MvPolynomial.monomial k 1 with hφ
  set pt : (WO (GlobalTheory.Grid.neg A) WW → ℂ) → (WO (GlobalTheory.Grid.neg A) WW → ℂ) := fun f =>
    pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B f φ with hpt
  have comb : ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, (y p).map (infPart D) = 0) →
      pt (∑ p, a p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) =
        ∑ p, a p • pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) := fun n a y hy => by
    have h1 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) X.rW.s
      X.rA.B X.rW.B X.vac hv n a y hy φ).1
    have h2 : ∀ p, heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) (pt X.vac) = pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) :=
      fun p => by
        have := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) X.rW.s
          X.rA.B X.rW.B X.vac hv 1 (fun _ => 1) (fun _ => y p) (fun _ => hy p) φ).1
        simpa using this
    simp only [← h2]
    exact h1.symm
  have e1 : ∀ g, ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm x, h) g = X.ω t (x, h) g := fun g => rfl
  have move : ∀ g, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW g → X.ω t (x, h) (pt g) = pt (X.ω t (x, h) g) := fun g hg => by
    rw [← e1, ← e1]
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hX.is.weil t) W.θ hθ ((GlobalTheory.Grid.ofSgn true A).symm x) hx h hh
      (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B g φ hg
  have hval : X.ker W.ψ W.θ t φ h x / Ω =
      ∑ p, c p * ∑ q, c' p q * (pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w' p q) X.vac) 0 / Ω) := by
    have e2 : X.ker W.ψ W.θ t φ h x = X.ω t (x, h) (pt (X.f t)) 0 := rfl
    have e3 : ∀ p, X.ω t (x, h) (pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac)) =
        ∑ q, c' p q • pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w' p q) X.vac) := fun p => by
      rw [move _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv _), hm p, comb _ _ _ (hw' p)]

    rw [e2, hf, comb _ _ _ hw, map_sum]
    simp only [map_smul, e3, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  rw [hval, ← mem_algebraicClosure_iff]
  refine sum_mem fun p _ => mul_mem (mem_algebraicClosure_iff.2 (hc p)) (sum_mem fun q _ => mul_mem
    (mem_algebraicClosure_iff.2 (hc' p q)) (mem_algebraicClosure_iff.2 (hjet _ (hw' p q) k hk)))
theorem classSums_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨v, N, z, w, κ, hv, hz, hw, hκ1, hκ2, hcls⟩ := _root_.GlobalTheory.T.bottom_class_sum_integral_neg hP hI hL hX
  obtain ⟨dg, hproj⟩ := _root_.GlobalTheory.T.twisted_real_average_kernel_isAlgebraic hP hI hL hX
  obtain ⟨Ω, hΩ, hdict⟩ := _root_.GlobalTheory.BotAlgI.classSum_kernel_isAlgebraic hP hI hL hX dg
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  refine ⟨(v : ℂ) * Ω, mul_ne_zero hv' hΩ, fun t h hh k => ?_⟩
  choose m r U hr hU heq using fun l => hproj κ hκ1 hκ2 t (z l) (hz l) h hh k
  have hval : X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / ((v : ℂ) * Ω) =
      ∑ l, ((w l : ℂ))⁻¹ * ∑ p, r l p * (X.ker W.ψ W.θ t (MvPolynomial.monomial (U l p) 1) h (z l) / Ω) := by
    rw [hcls t _ h hh]
    simp only [heq, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    field_simp
  rw [hval, ← mem_algebraicClosure_iff]
  refine sum_mem fun l _ => mul_mem (inv_mem ?_) (sum_mem fun p _ => mul_mem ?_ ?_)
  · rw [mem_algebraicClosure_iff]
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((w l : ℚ)))
  · rw [mem_algebraicClosure_iff]; exact hr l p
  · rw [mem_algebraicClosure_iff]; exact hdict t (z l) (hz l) h hh (U l p) (hU l p)
end GlobalTheory.BotAlgI
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_classSums_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  first | exact @_root_.GlobalTheory.BotAlgI.classSums_isAlgebraic | exact _root_.GlobalTheory.BotAlgI.classSums_isAlgebraic | (intros; apply _root_.GlobalTheory.BotAlgI.classSums_isAlgebraic <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotFormulaI'
theorem bottomClassSum_formula : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ (n : ℕ) (c z : Fin n → ℂ), (∀ l, IsAlgebraic ℚ (c l)) ∧
      (∀ l, ∃ (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (h' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n),
        z l = P.coord h' U) ∧
      X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = Ω * ∑ l, c l * z l := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨v, N, z, w, κ, hv, hz, hw, hκ1, hκ2, hcls⟩ := _root_.GlobalTheory.T.twist_integral_eq_bottom_classSum hP hI hL hX
  obtain ⟨n, hproj⟩ := _root_.GlobalTheory.T.twist_realProjection_average_monomial hP hI hL hX
  obtain ⟨Ω, hΩ, hdict⟩ := _root_.GlobalTheory.T.twist_kernel_div_period_isAlgebraic hP hI hL hX n
  obtain ⟨δ, hδ⟩ := GlobalTheory.NormSum.exists_crv_top D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex ⊤ δ hδ).1
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  refine ⟨(v : ℂ) * Ω, mul_ne_zero hv' hΩ, fun t h hh k => ?_⟩
  choose m r U hr heq using fun l => hproj κ hκ1 hκ2 t (z l) (hz l) h hh k
  set S : ℂ := ∑ l, ((w l : ℂ))⁻¹ * ∑ p, r l p * (X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U l p)) h (z l) / Ω) with hSdef
  have hval : X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = (v : ℂ) * Ω * S := by
    rw [hcls t _ h hh, hSdef]
    simp only [heq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    field_simp
  have hS : IsAlgebraic ℚ S := by
    rw [← mem_algebraicClosure_iff] at *
    refine sum_mem fun l _ => mul_mem (inv_mem ?_) (sum_mem fun p _ => mul_mem ?_ ?_)
    · rw [mem_algebraicClosure_iff]
      simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((w l : ℚ)))
    · rw [mem_algebraicClosure_iff]; exact hr l p
    · rw [mem_algebraicClosure_iff]; exact hdict t (z l) (hz l) h hh (U l p)
  refine ⟨1, fun _ => S, fun _ => 1, fun _ => hS,
    fun _ => ⟨δ, t0, 1, GlobalTheory.NormSum.RankZero.pair0 hδ ht0, 1, fun τ j => j.elim0,
      ((GlobalTheory.NormSum.RankZero.normSumPairRankZeroOfCurve_coord_norm hδ ht0).1 _ _).symm⟩, ?_⟩
  rw [hval]
  simp
end GlobalTheory.BotFormulaI'
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottomClassSum_eq_formula : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ (n : ℕ) (c z : Fin n → ℂ), (∀ l, IsAlgebraic ℚ (c l)) ∧
      (∀ l, ∃ (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (h' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n),
        z l = P.coord h' U) ∧
      X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = Ω * ∑ l, c l * z l := by
  first | exact @_root_.GlobalTheory.BotFormulaI'.bottomClassSum_formula | exact _root_.GlobalTheory.BotFormulaI'.bottomClassSum_formula | (intros; apply _root_.GlobalTheory.BotFormulaI'.bottomClassSum_formula <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.RealQuot
theorem twist_quotient_isReal : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (ρ : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pr)
      (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧ Module.rank ℂ Pr ≤ Cardinal.aleph0 ∧
      (∀ N : Submodule ℂ Pr, (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, ρ τ Y x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          (∀ f, IsFinF ψ θ true A B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p (fockF ψ θ true A B f P) = φ (q P)) ∧
          ∀ f, IsFinF ψ θ false A₁ B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p' (fockF ψ θ false A₁ B f P) = φ (q' P) := by
  intro hH hP _ _ D ψ θ hψ hθ W W₁ X A A₁ B a b
  classical
  let ρA : LieIx X → Module.End ℂ (PolF D X.rank W.rank) := fun i => actT true A B b i.1.1 i.1.2
  let CA := coinv true A B (fun τ => b τ - a τ)
  let ρB : LieIx X → Module.End ℂ (PolF D X.rank W₁.rank) := fun i => actT false A₁ B a i.1.1 i.1.2
  let CB := coinv false A₁ B (fun τ => a τ - b τ)
  have fam : ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
      let σ : LieIx X → Module.End ℂ Pi := fun i => rl i.1.1 i.1.2
      let βA : {f // IsFinF ψ θ true A B f} → PolF D X.rank W.rank →ₗ[ℂ] Pi := fun f => p ∘ₗ fockF ψ θ true A B f.1
      let βB : {f // IsFinF ψ θ false A₁ B f} → PolF D X.rank W₁.rank →ₗ[ℂ] Pi := fun f => p' ∘ₗ fockF ψ θ false A₁ B f.1
      ((∀ f i, βA f ∘ₗ ρA i = σ i ∘ₗ βA f) ∧ (∀ f, CA ≤ LinearMap.ker (βA f)) ∧
        (∀ (j : {h // h ∈ GfC X}) f, ∃ f', rf j.1 ∘ₗ βA f = βA f') ∧ (⨆ f, LinearMap.range (βA f)) = ⊤) ∧
      ((∀ f i, βB f ∘ₗ ρB i = σ i ∘ₗ βB f) ∧ (∀ f, CB ≤ LinearMap.ker (βB f)) ∧
        (∀ (j : {h // h ∈ GfC X}) f, ∃ f', rf j.1 ∘ₗ βB f = βB f') ∧ (⨆ f, LinearMap.range (βB f)) = ⊤) ∧
      (∀ N : Submodule ℂ Pi, IsStab σ N → IsStab (fun j : {h // h ∈ GfC X} => rf j.1) N → N = ⊥ ∨ N = ⊤) ∧
      HoweCond ρA CA ∧ HoweCond ρB CB ∧ Nontrivial Pi := by
    intro α β htr hexp ωA ωB Pi rf rl p p' hm
    have hexpA : ∀ τ, HasInfExp D β τ (b τ) ∧ HasInfExp D (β / α) τ (b τ - a τ) :=
      fun τ => ⟨(hexp τ).2, hasInfExp_div D α β τ _ _ (hexp τ).1 (hexp τ).2⟩
    have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨oA1, oA2, oA3⟩ := GlobalTheory.T.orientedPair_fockMaps_lie_equivariant D ψ θ hθ true W X A B β (β / α) ωA b (fun τ => b τ - a τ) hm.weilA hexpA Pi rf rl p hm.mapA
    obtain ⟨oB1, oB2, oB3⟩ := GlobalTheory.T.orientedPair_fockMaps_lie_equivariant D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ) hm.weilB hexpB Pi rf rl p' hm.mapB
    have hspan : ∀ {M : HSp D} {ε : Bool} {A' : Fr M} (pp : (WO M X → ℂ) →ₗ[ℂ] Pi), (algF ψ θ ε A' B).map pp = ⊤ →
        (⨆ f : {f // IsFinF ψ θ ε A' B f}, LinearMap.range (pp ∘ₗ fockF ψ θ ε A' B f.1)) = ⊤ := by
      intro M ε A' pp h
      rw [eq_top_iff, ← h, algF, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨f, P, hf, rfl⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨P, rfl⟩
    refine ⟨⟨fun f i => LinearMap.ext fun P => oA1 f.1 f.2 i.1.1 i.1.2 i.2 P,
        fun f P hP => oA2 f.1 f.2 P hP, fun j f => ?_, hspan p hm.mapA.onto⟩,
      ⟨fun f i => LinearMap.ext fun P => oB1 f.1 f.2 i.1.1 i.1.2 i.2 P,
        fun f P hP => oB2 f.1 f.2 P hP, fun j f => ?_, hspan p' hm.mapB.onto⟩,
      fun N h1 h2 => hm.irred.2 N (fun g hg x hx => h2 ⟨g, hg⟩ x hx) (fun τ Y hY x hx => h1 ⟨(τ, Y), hY⟩ x hx),
      _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants hH hP D ψ θ hψ hθ true W X A B β (β / α) ωA b _ hm.weilA hexpA,
      _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants hH hP D ψ θ hψ hθ false W₁ X A₁ B α (α / β) ωB a _ hm.weilB hexpB, hm.irred.1⟩
    · obtain ⟨f', hf', e⟩ := oA3 j.1 j.2 f.1 f.2
      exact ⟨⟨f', hf'⟩, LinearMap.ext fun P => e P⟩
    · obtain ⟨f', hf', e⟩ := oB3 j.1 j.2 f.1 f.2
      exact ⟨⟨f', hf'⟩, LinearMap.ext fun P => e P⟩
  by_cases hex : ∃ α β, IsTriple W W₁ X α β ∧ (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) ∧
      ∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p'
  swap
  · refine ⟨ModuleCat.of ℂ PUnit, fun _ _ => 0, 0, 0, fun _ => ⟨0, Subsingleton.elim _ _⟩,
      fun _ => ⟨0, Subsingleton.elim _ _⟩, ?_, fun N _ => Or.inl (Submodule.eq_bot_of_subsingleton), ?_⟩
    · show Module.rank ℂ PUnit ≤ _
      simp
    · intro α β htr hexp ωA ωB Pi rf rl p p' hm
      exact absurd ⟨α, β, htr, hexp, ωA, ωB, Pi, rf, rl, p, p', hm⟩ hex
  obtain ⟨α₀, β₀, htr₀, hexp₀, ωA₀, ωB₀, Pi₀, rf₀, rl₀, p₀, p₀', hm₀⟩ := hex
  obtain ⟨⟨iA, kA, cA, sA⟩, ⟨iB, kB, cB, sB⟩, irr₀, hHA, hHB, hnt⟩ := fam α₀ β₀ htr₀ hexp₀ ωA₀ ωB₀ Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  set σ₀ : LieIx X → Module.End ℂ Pi₀ := fun i => rl₀ i.1.1 i.1.2
  have nz : ∀ {Fm Q : Type} [AddCommGroup Q] [Module ℂ Q] (β : Fm → Q →ₗ[ℂ] Pi₀), (⨆ f, LinearMap.range (β f)) = ⊤ →
      ∃ f, β f ≠ 0 := by
    intro Fm Q _ _ β h
    by_contra hc
    push_neg at hc
    have : (⊤ : Submodule ℂ Pi₀) = ⊥ := by
      rw [← h]; exact iSup_eq_bot.2 fun f => by rw [hc f, LinearMap.range_zero]
    exact bot_ne_top this.symm
  have wit : ∀ {Q : Type} [AddCommGroup Q] [Module ℂ Q] (ρ : LieIx X → Module.End ℂ Q) (C : Submodule ℂ Q)
      (β : Q →ₗ[ℂ] Pi₀), (∀ i, β ∘ₗ ρ i = σ₀ i ∘ₗ β) → C ≤ LinearMap.ker β → β ≠ 0 →
      IsStab ρ (LinearMap.ker β) ∧ C ≤ LinearMap.ker β ∧ LinearMap.ker β ≠ ⊤ := by
    intro Q _ _ ρ C β hi hk hne
    refine ⟨fun i x hx => ?_, hk, fun h => hne (LinearMap.ker_eq_top.1 h)⟩
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨fA, hfA⟩ := nz _ sA
  obtain ⟨fB, hfB⟩ := nz _ sB
  obtain ⟨wA1, wA2, wA3⟩ := wit ρA CA _ (iA fA) (kA fA) hfA
  obtain ⟨wB1, wB2, wB3⟩ := wit ρB CB _ (iB fB) (kB fB) hfB
  have radA : rad ρA CA ≠ ⊤ := rad_ne_top _ _ ρA CA _ hHA wA1 wA2 wA3
  have radB : rad ρB CB ≠ ⊤ := rad_ne_top _ _ ρB CB _ hHB wB1 wB2 wB3
  have CleA : CA ≤ rad ρA CA := wA2.trans (le_sSup ⟨wA1, wA2, wA3⟩)
  have CleB : CB ≤ rad ρB CB := wB2.trans (le_sSup ⟨wB1, wB2, wB3⟩)
  have simA : ∀ N, IsStab ρA N → rad ρA CA ≤ N → N = rad ρA CA ∨ N = ⊤ := by
    intro N h1 h2
    by_cases h : N = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (le_sSup ⟨h1, CleA.trans h2, h⟩) h2)
  have simB : ∀ N, IsStab ρB N → rad ρB CB ≤ N → N = rad ρB CB ∨ N = ⊤ := by
    intro N h1 h2
    by_cases h : N = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (le_sSup ⟨h1, CleB.trans h2, h⟩) h2)
  have ss₀ := GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners _ _ _ _ _ ρA CA σ₀ (fun j : {h // h ∈ GfC X} => rf₀ j.1) _ hHA iA kA cA sA irr₀
  have killA₀ : ∀ f, rad ρA CA ≤ LinearMap.ker _ := fun f => rad_le_ker _ _ _ ρA CA σ₀ _ (iA f) (kA f) radA ss₀
  have killB₀ := rad_le_ker _ _ _ ρB CB σ₀ _ (iB fB) (kB fB) radB ss₀
  obtain ⟨e, he⟩ := GlobalTheory.T.simple_quotients_iso_of_intertwined_semisimple _ _ _ _ _ ρA CA ρB CB σ₀ _ _ iA (iB fB) killA₀ killB₀ hfB sA simA simB ss₀
  let R := rad ρA CA
  let RB := rad ρB CB
  refine ⟨ModuleCat.of ℂ (PolF D X.rank W.rank ⧸ R),
    fun τ Y => if h : Y ∈ lieAt X τ then radAct ρA CA ⟨(τ, Y), h⟩ else 0,
    R.mkQ, e.symm.toLinearMap ∘ₗ RB.mkQ, R.mkQ_surjective, e.symm.surjective.comp RB.mkQ_surjective, ?_, ?_, ?_⟩
  · show Module.rank ℂ (PolF D X.rank W.rank ⧸ R) ≤ _
    refine (rank_quotient_le R).trans ?_
    rw [← (MvPolynomial.basisMonomials (FVar D X.rank W.rank) ℂ).mk_eq_rank'']
    exact Cardinal.mk_le_aleph0
  · intro N hN
    have hst : IsStab ρA (N.comap R.mkQ) := fun i x hx => by
      have h1 := hN i.1.1 i.1.2 i.2 _ hx
      simp only [dif_pos i.2] at h1
      exact h1
    have hle : R ≤ N.comap R.mkQ := fun x hx => by
      show R.mkQ x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R).2 hx]
      exact N.zero_mem
    rcases simA _ hst hle with h | h
    · left
      rw [← Submodule.map_comap_eq_of_surjective R.mkQ_surjective N, h, Submodule.mkQ_map_self]
    · right
      rw [← Submodule.map_comap_eq_of_surjective R.mkQ_surjective N, h, Submodule.map_top, Submodule.range_mkQ]
  · intro α β htr hexp ωA ωB Pi rf rl p p' hm
    obtain ⟨⟨iA', kA', cA', sA'⟩, ⟨iB', kB', cB', sB'⟩, irr', -, -, -⟩ := fam α β htr hexp ωA ωB Pi rf rl p p' hm
    have ss' := GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners _ _ _ _ _ ρA CA (fun i : LieIx X => rl i.1.1 i.1.2) (fun j : {h // h ∈ GfC X} => rf j.1) _ hHA
      iA' kA' cA' sA' irr'
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · have hk := rad_le_ker _ _ _ ρA CA _ _ (iA' ⟨f, hf⟩) (kA' ⟨f, hf⟩) radA ss'
      refine ⟨R.liftQ (p ∘ₗ fockF ψ θ true A B f) hk, fun τ Y hY => ?_, fun P => rfl⟩
      simp only [dif_pos hY]
      refine Submodule.linearMap_qext _ (LinearMap.ext fun P => ?_)
      exact LinearMap.congr_fun (iA' ⟨f, hf⟩ ⟨(τ, Y), hY⟩) P
    · have hk := rad_le_ker _ _ _ ρB CB _ _ (iB' ⟨f, hf⟩) (kB' ⟨f, hf⟩) radB ss'
      refine ⟨RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk ∘ₗ e.toLinearMap, fun τ Y hY => ?_, fun P => ?_⟩
      · simp only [dif_pos hY]
        refine LinearMap.ext fun x => ?_
        have h1 := LinearMap.congr_fun (he ⟨(τ, Y), hY⟩) x
        simp only [LinearMap.comp_apply] at h1 ⊢
        rw [h1]
        have key : ∀ y, RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk (radAct ρB CB ⟨(τ, Y), hY⟩ y) =
            rl τ Y (RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk y) := by
          intro y
          obtain ⟨P, rfl⟩ := RB.mkQ_surjective y
          exact LinearMap.congr_fun (iB' ⟨f, hf⟩ ⟨(τ, Y), hY⟩) P
        exact key _
      · simp
end GlobalTheory.RealQuot
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

theorem _root_.GlobalTheory.T.twisted_quotient_real : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (ρ : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pr)
      (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧ Module.rank ℂ Pr ≤ Cardinal.aleph0 ∧
      (∀ N : Submodule ℂ Pr, (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, ρ τ Y x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          (∀ f, IsFinF ψ θ true A B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p (fockF ψ θ true A B f P) = φ (q P)) ∧
          ∀ f, IsFinF ψ θ false A₁ B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p' (fockF ψ θ false A₁ B f P) = φ (q' P) := by
  first | exact @_root_.GlobalTheory.RealQuot.twist_quotient_isReal | exact _root_.GlobalTheory.RealQuot.twist_quotient_isReal | (intros; apply _root_.GlobalTheory.RealQuot.twist_quotient_isReal <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.SquareAgree
theorem twisted_theta_integrals_agree : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  intro hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨-, ⟨c, hc, -⟩, hc0⟩, hCo⟩ := hK' R Rf hR
  obtain ⟨s, hs0, hs⟩ := _root_.GlobalTheory.T.twisted_theta_kernels_agree_up_to_scalar hP.howeDualityReal hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
    Pi rf rl p p' hM
  refine ⟨c * s, mul_ne_zero (hc0 c hc) hs0, fun Φ' hΦ' => ?_⟩
  obtain ⟨Φ₀, hΦ₀, hrel, Φ₀D, hD₀, hSo⟩ :=
    GlobalTheory.SquareAgree.CoinvPass.coinv_passage D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hTD R Rf hR hCo Φ' hΦ'
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D hSo
  refine ⟨Φ₀, hΦ₀, hrel, GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hTD Φ₀ Φ₀D hD₀
    hconv ?_, fun Φ hΦ hp => ?_⟩
  · obtain ⟨C, k, hC⟩ := hbd 0
    exact ⟨C, k, fun g h => by simpa using hC g h⟩
  · obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
    have hm := hs Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
    funext h
    rw [GlobalTheory.SquareAgree.thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h,
      _root_.Pi.smul_apply,
      GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (kapX X e hO.JX) Φ₀D Φ₀ hO.measW₁ hO.domW₁ (hO.theta_eq_B hD₀) h,
      hc ΦD (s • Φ₀D) hm (kapX X e hO.JX h), I_smul, smul_eq_mul, mul_assoc]
end GlobalTheory.SquareAgree
end
end

section

theorem _root_.GlobalTheory.T.twisted_square_theta_integrals_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  first | exact @_root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree | exact _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree | (intros; apply _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree <;> assumption)
end
end
