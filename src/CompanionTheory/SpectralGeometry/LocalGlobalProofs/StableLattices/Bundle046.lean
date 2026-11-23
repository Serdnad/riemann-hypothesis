module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithBoundary
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle044
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.exterior_differential_matrix_unit_formula : ∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single | exact GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single | (intros; apply GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single <;> assumption)
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.StandardDifferential : StdD := by
  first | exact @GlobalTheory.CompanionTheory.ZuckStdD.stdD | exact GlobalTheory.CompanionTheory.ZuckStdD.stdD | (intros; apply GlobalTheory.CompanionTheory.ZuckStdD.stdD <;> assumption)
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.levi_action_commutes_with_boundary : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → GlRel E → ∀ p q : Fin n, lev p = lev q → ∀ x : Cn n V, SuppIn (inU lev) x →
      lF E p q (bd (allT n) E x) = bd (allT n) E (lF E p q x) := by
  first | exact @GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm | exact GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm | (intros; apply GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm <;> assumption)
end

section

theorem _root_.GlobalTheory.T.GrowthStatement : CompanionTheory.RgExh.Dec.L.Growth :=
  GlobalTheory.CompanionTheory.PathGrowth.growth
end

section

namespace GlobalTheory.CompanionTheory.BaseFamily

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

theorem baseFam : CompanionTheory.RgExh.Dec.J.BaseFam := by
  intro n ε H _ _ _ σ D E hK hσ
  refine ⟨fun ξ u Y hY g hg => ?_, fun ξ => ?_⟩
  · have h := GlobalTheory.T.NilpotentRightRule n ε H σ D E hK 0 [] hσ ((ξ, []) : D × List (Fin n)) u Y hY g hg
    have e : actM E Y u = ∑ a, ∑ b, Y a b • E a b u := by
      simp [actM, LinearMap.sum_apply]
    show HasDerivAt _ (baseCoef σ D (ξ : H) (actM E Y u) g) 0
    rw [e]
    exact h
  · obtain ⟨l, hl⟩ := GlobalTheory.T.NilpotentLeftRule n ε H σ D E hK 0 [] hσ ((ξ, []) : D × List (Fin n))
    refine ⟨fun c d => (l c d).mapDomain Prod.fst, fun a b u g hg => ?_⟩
    have h := hl a b u g hg
    refine h.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
    congr 1
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
    rfl

end GlobalTheory.CompanionTheory.BaseFamily
end

section

open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem GlobalTheory.T.iwasawa_parabolic_compact_factorization :
    ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
      ∀ g : S7.UJ ε, ∃ (x : PSub ε A) (k : S7.KG ε), g = (x : S7.UJ ε) * (k : S7.UJ ε) :=
  GlobalTheory.CompanionTheory.UGeo.iwasawa_psub
end

section

open Matrix
open CompanionTheory.RgExh.Dec (IsGrad)
open GlobalTheory.CompanionTheory.PSubFlag (Pm Pp)

theorem _root_.GlobalTheory.T.finite_net_of_graded_projections :
    ∀ (n : ℕ) (ε : Fin n → Bool),
      ∃ (m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ j, IsGrad ε (A j)) ∧
        ∀ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' →
          ∃ j, Formalism.REAL.hs (Pm (A j) - Pm A') ≤ 1 / 4 ∧
            Formalism.REAL.hs (Pp (A j) - Pp A') ≤ 1 / 4 :=
  GlobalTheory.CompanionTheory.UGeo.GradNet.exists_net
end
