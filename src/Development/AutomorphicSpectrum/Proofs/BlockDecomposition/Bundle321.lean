module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle298
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle303
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle304
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle305
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepFormulaF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.ExplicitFunctionSquareIntegrable

@[expose] public section

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegJacquet

theorem exists_isTopCut_two_of_jhMult_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), Zc.LSegJacquet k → IsLSeg Δ π →
    ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 →
    ∃ Γ : Fin 2 → Segment k, Zc.IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (x a).rep := by
  intro k _ _ _ _ Δ N V _ _ π hJ hπ x hd hpos hne
  by_contra hno
  exact hne ((hJ Δ π hπ 2 x hd hpos).2 hno)

end GlobalTheory.CompanionTheory.SegJacquet
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.uniform_limit_right_derivatives : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n)) → ∃ Gf : List (Bool × Fin n × Fin n) → Mat n → V, (∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n)) ∧ ContDiffOn ℝ ∞ (Gf []) (GLs n) ∧ ∀ w, ∀ z ∈ GLs n, Rw w (Gf []) z = Gf w z := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth | exact GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth | (intros; apply GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth <;> assumption)
end
end

section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.contraction_fixed : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  first | exact @GlobalTheory.CompanionTheory.RepTensor.contrFix | exact GlobalTheory.CompanionTheory.RepTensor.contrFix | (intros; apply GlobalTheory.CompanionTheory.RepTensor.contrFix <;> assumption)
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end

section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.hecke_eigen_finite : PositivityTheory.Rg.BcB.F.Tail.PExp.HkEFin := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | exact GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | (intros; apply GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin <;> assumption)
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end

section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.tensor_hecke : PositivityTheory.Rg.BcB.F.Tail.PExp.TensHk := by
  first | exact @GlobalTheory.CompanionTheory.TensHkSum.tensHk | exact GlobalTheory.CompanionTheory.TensHkSum.tensHk | (intros; apply GlobalTheory.CompanionTheory.TensHkSum.tensHk <;> assumption)
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end

section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.sub_eigen_tail_hecke : PositivityTheory.Rg.BcB.F.Tail.PExp.SubEig := by
  first | exact @GlobalTheory.CompanionTheory.SubEigIrr.subEig | exact GlobalTheory.CompanionTheory.SubEigIrr.subEig | (intros; apply GlobalTheory.CompanionTheory.SubEigIrr.subEig <;> assumption)
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end

section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.tensor_eigen_real : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  first | exact @GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | exact GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | (intros; apply GlobalTheory.CompanionTheory.TensEigSecond.tensEigR <;> assumption)
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end

section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.tensor_eigen : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEig := by
  first | exact @GlobalTheory.CompanionTheory.TensContr.tensEig | exact GlobalTheory.CompanionTheory.TensContr.tensEig | (intros; apply GlobalTheory.CompanionTheory.TensContr.tensEig <;> assumption)
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end

section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.coset_count_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  first | exact @GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | exact GlobalTheory.CompanionTheory.IwahoriCount.cosetCount | (intros; apply GlobalTheory.CompanionTheory.IwahoriCount.cosetCount <;> assumption)
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end

section

namespace GlobalTheory.CompanionTheory.DiscreteSeries

private lemma two_mul_rhoN_add_rhoC_eq_card_sub_card {n : ℕ} (ε : Fin n → Bool) (x : Fin n) :
    2 * (Formalism.REAL.rhoN ε x + Formalism.REAL.rhoC ε x) =
      (({y | x < y} : Finset (Fin n)).card : ℝ) - (({y | y < x} : Finset (Fin n)).card : ℝ) := by
  have hA : ({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card = ({y | x < y} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : x < y <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hB : ({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card = ({y | y < x} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : y < x <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hA' : (({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | x < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hA
  have hB' : (({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | y < x} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hB
  simp only [Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  linarith

private lemma rhoN_add_rhoC_le_of_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) :
    Formalism.REAL.rhoN ε b + Formalism.REAL.rhoC ε b ≤ Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a := by
  have h1 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε a
  have h2 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε b
  have c1 : ({y | b < y} : Finset (Fin n)).card ≤ ({y | a < y} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hab hy
  have c2 : ({y | y < a} : Finset (Fin n)).card ≤ ({y | y < b} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hy hab
  have c1' : (({y | b < y} : Finset (Fin n)).card : ℝ) ≤ (({y | a < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c1
  have c2' : (({y | y < a} : Finset (Fin n)).card : ℝ) ≤ (({y | y < b} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c2
  linarith

private lemma nsq_le_nsq_add_of_dot_nonneg {n : ℕ} (v w : Fin n → ℝ) (h : 0 ≤ Formalism.REAL.dot v w) :
    Formalism.REAL.nsq v ≤ Formalism.REAL.nsq (v + w) := by
  unfold Formalism.REAL.nsq Formalism.REAL.dot at *
  have h2 : 0 ≤ ∑ a, w a * w a := Finset.sum_nonneg (fun a _ => mul_self_nonneg (w a))
  have e : ∑ a, (v + w) a * (v + w) a = ∑ a, v a * v a + 2 * ∑ a, v a * w a + ∑ a, w a * w a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by simp only [Pi.add_apply]; ring)
  rw [e]
  linarith

private lemma dot_nonneg_sum_root_of_antitone {n : ℕ} (v : Fin n → ℝ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b : Fin n, c a b ≠ 0 → a < b) (hmono : ∀ a b : Fin n, a < b → v b ≤ v a) :
    0 ≤ Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) := by
  have hdot : Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b)
      = ∑ a, ∑ b, (c a b : ℝ) * (v a - v b) := by
    unfold Formalism.REAL.dot
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hdot]
  refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
  by_cases h0 : c a b = 0
  · simp [h0]
  · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hmono a b (hc a b h0)))


open GlobalTheory.LowestKTypeDetermines in
theorem stepVogan : PositivityTheory.RgDs.Hilb.StepVogan := by
  intro n ε lam η hlam hη
  obtain ⟨c, hc, rfl⟩ := hη
  have hk : ReciprocityTheory.ChartRestriction.DS.lowK ε lam = Formalism.QuantumDeterminants.lowK ε lam := by rfl
  unfold Formalism.MainNotions.S.vNormSq
  rw [hk, add_right_comm]
  apply nsq_le_nsq_add_of_dot_nonneg
  apply dot_nonneg_sum_root_of_antitone _ c hc
  intro a b hab
  simp only [Formalism.QuantumDeterminants.lowK, two_nsmul, two_smul, Pi.add_apply, Pi.sub_apply]
  have h1 := rhoN_add_rhoC_le_of_lt ε hab
  have h2 := hlam.1 hab
  linarith

end GlobalTheory.CompanionTheory.DiscreteSeries
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS

theorem stepWtSpan : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  intro n ε S hSf hSD hSK N _ _ e he
  classical
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hE : IsGlRep (smE ε (rreg ε)) := hD.glRep
  have hKU : IsKUnitary ε (smE ε (rreg ε)) :=
    isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, rreg ε k x ∈ S := hSK
  haveI := hSf
  haveI hS'f : FiniteDimensional ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm
  have hS'k : IsKStableSub ε (smE ε (rreg ε)) (S.comap (smD ε (rreg ε)).subtype) :=
    isKStableSub_of_kStable hσ hD _ hS'f fun k hk v hv =>
      ⟨⟨rreg ε k v, hD.kStable k hk _ v.2⟩, hSK' k hk _ hv, rfl⟩
  let T : Fin n → Module.End ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    fun c => (smE ε (rreg ε) c c).restrict (hS'k c c rfl)
  have hTs : ∀ c, (T c).IsSymmetric := fun c x z => hKU c c rfl (x : smD ε (rreg ε)) (z : smD ε (rreg ε))
  have hcomm : Pairwise (Function.onFun Commute T) := fun a c _ =>
    LinearMap.ext fun x => Subtype.ext (kUnit_diag_comm hE a c (x : smD ε (rreg ε)))
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hcomm
  let e' : (S.comap (smD ε (rreg ε)).subtype) →ₗ[ℂ] N :=
    e.comp (Submodule.comapSubtypeEquivOfLe hSD).toLinearMap
  by_contra hno
  push_neg at hno
  have hle : ∀ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (T c) (χ c)) ≤ LinearMap.ker e' := by
    intro χ x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    have hxc : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) = χ c • (x : smD ε (rreg ε)) := fun c =>
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx c))
    have hx0' : (x : smD ε (rreg ε)) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxν : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) =
        (((χ c).re : ℝ) : ℂ) • (x : smD ε (rreg ε)) := fun c =>
      (hxc c).trans (congrArg (· • (x : smD ε (rreg ε))) (kUnit_eig_real hKU hx0' (hxc c)))
    exact hno (fun c => (χ c).re) (Submodule.comapSubtypeEquivOfLe hSD x)
      ((isWtOn_iff hσ hD (x : smD ε (rreg ε)) _).2 hxν)
  have hker : LinearMap.ker e' = ⊤ := top_le_iff.mp (htop ▸ iSup_le hle)
  refine he (LinearMap.ext fun y => ?_)
  have hy : (Submodule.comapSubtypeEquivOfLe hSD).symm y ∈ LinearMap.ker e' := hker ▸ Submodule.mem_top
  have h2 : e' ((Submodule.comapSubtypeEquivOfLe hSD).symm y) = 0 := hy
  calc e y = e (Submodule.comapSubtypeEquivOfLe hSD ((Submodule.comapSubtypeEquivOfLe hSD).symm y)) := by
        rw [LinearEquiv.apply_symm_apply]
    _ = 0 := h2

end GlobalTheory.CompanionTheory.RgDsHilb
end
end

section

noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgDs PositivityTheory.RgDs.Hilb

variable {n : ℕ}

theorem isKTypeOf_map_of_injOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S) (A : H →ₗ[ℂ] H)
    (hcomm : ∀ k ∈ Kset ε, ∀ v, σ k (A v) = A (σ k v))
    (hinj : ∀ w ∈ S, A w = 0 → w = 0) :
    Formalism.MainNotions.S.IsKTypeOf ε σ Λ (S.map A) := by
  haveI : FiniteDimensional ℂ S := hS.1
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S.map A → Formalism.MainNotions.S.IsKStableOn ε σ S' →
      S' = ⊥ ∨ S' = S.map A := by
    intro S' hS' hK'
    have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap A) := by
      intro g hg v hv
      rw [Submodule.mem_inf] at hv ⊢
      refine ⟨hS.2.1 g hg v hv.1, ?_⟩
      show A (σ g v) ∈ S'
      rw [← hcomm g hg v]
      exact hK' g hg _ hv.2
    rcases hS.2.2.1 (S ⊓ S'.comap A) inf_le_left hTK with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hwT : w ∈ S ⊓ S'.comap A := Submodule.mem_inf.2 ⟨hw, hx⟩
      rw [h] at hwT
      rw [(Submodule.mem_bot ℂ).1 hwT, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hwT : w ∈ S ⊓ S'.comap A := by rw [h]; exact hw
      exact (Submodule.mem_inf.1 hwT).2
  refine ⟨inferInstance, ?_, hirr, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hS.2.1 g hg w hw, (hcomm g hg w).symm⟩
  · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
    refine ⟨A v, ⟨v, hv, rfl⟩, fun h => hv0 (hinj v hv h), ?_⟩
    intro θ hθ
    rw [hcomm _ hθ, hwt θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hne hwt
    refine hS.2.2.2.2 μ w hw (fun h => hne (by rw [h, map_zero])) ?_
    intro θ hθ
    have h1 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) w -
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • w) = 0 := by
      rw [map_sub, map_smul, ← hcomm _ hθ, hwt θ hθ, sub_self]
    have h2 := hinj _ (Submodule.sub_mem _ (hS.2.1 _ hθ w hw) (Submodule.smul_mem _ _ hw)) h1
    exact sub_eq_zero.1 h2

theorem stepIrred_of_stepDatum : StepDatum → StepIrred := by
  intro hDatum n ε lam T Ψ hP _hst huniq W hWle hWc hWG
  classical
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV1 : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ) := hDatum n ε lam T Ψ hP
  have : CompleteSpace W := hWc.completeSpace_coe
  have hWo : ∀ g ∈ UJset ε, ∀ x ∈ Wᗮ, rreg ε g x ∈ Wᗮ := by
    intro g hg
    obtain ⟨g', hg', hgg⟩ := UnitaryGroupOfForm.inv_mem_UJ hg
    exact UnitaryGroupOfForm.orth_stable hσ hg hg' hgg W (hWG g' hg')
  have hK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) (V1 ε Ψ ⊓ Wᗮ) := by
    intro k hk x hx
    exact ⟨hV1.2.1 k hk x hx.1, hWo k (UnitaryGroupOfForm.K_mem_UJ hk) x hx.2⟩
  have hmem : ∀ v ∈ datumV ε Ψ T.w, ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ :=
    fun v hv => Submodule.mem_map_of_mem hv
  rcases hV1.2.2.1 (V1 ε Ψ ⊓ Wᗮ) inf_le_left hK with h0 | hV'
  · right
    refine le_antisymm hWle (UnitaryGroupOfForm.closGen_le hD W hWc hWG _ ?_)
    have hcomm : ∀ k ∈ Kset ε, ∀ v, rreg ε k (W.starProjection.toLinearMap v) =
        W.starProjection.toLinearMap (rreg ε k v) := by
      intro k hk v
      have hkU := UnitaryGroupOfForm.K_mem_UJ hk
      exact (UnitaryGroupOfForm.proj_comm W (rreg ε k) (hWG k hkU) (hWo k hkU) v).symm
    have hinj : ∀ w ∈ V1 ε Ψ, W.starProjection.toLinearMap w = 0 → w = 0 := by
      intro w hw h
      have hwo : w ∈ Wᗮ := by
        have := W.sub_starProjection_mem_orthogonal w
        have h' : W.starProjection w = 0 := h
        rwa [h', sub_zero] at this
      have : w ∈ V1 ε Ψ ⊓ Wᗮ := ⟨hw, hwo⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).1 this
    have hle : (V1 ε Ψ).map W.starProjection.toLinearMap ≤ W := by
      rintro _ ⟨w, -, rfl⟩
      exact W.starProjection_apply_mem w
    have heq := huniq _ (hle.trans hWle) (isKTypeOf_map_of_injOn hV1 _ hcomm hinj)
    intro v hv
    have hv' : ((v : smD ε (rreg ε)) : L2 ε) ∈ (V1 ε Ψ).map W.starProjection.toLinearMap := by
      rw [heq]; exact hmem v hv
    exact hle hv'
  · left
    have hle : Hlam ε Ψ T.w ≤ Wᗮ :=
      UnitaryGroupOfForm.closGen_le hD Wᗮ (Submodule.isClosed_orthogonal W) hWo _
        (fun v hv => (show ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ ⊓ Wᗮ by
          rw [hV']; exact hmem v hv).2)
    rw [eq_bot_iff, ← Submodule.inf_orthogonal_eq_bot W]
    exact le_inf le_rfl (hWle.trans hle)

end GlobalTheory.CompanionTheory.RgDsHilb
end
end
