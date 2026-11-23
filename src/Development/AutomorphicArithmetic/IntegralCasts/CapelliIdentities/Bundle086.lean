module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle046
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

theorem UpperTheory.Reformulated.B.LatticePowerSmul.exists_pow_smul_mem_lattice_alt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (LL : Formalism.BasicNotions.Loc.FinExt l) (T : GlobalTheory.BKGal.QLat LL) (v : T.V),
      ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈ T.L.T := by
  intro l inst LL T v
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact UpperTheory.exists_pow_smul_mem_alt T.L.T (fun c hc => ⟨⟨c, hc⟩, rfl⟩) T.L.span v
end

section

theorem UpperTheory.Reformulated.B.InfiniteNormOne.infinite_norm_one :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
      {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
      {θ : NumberField.InfinitePlace F → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) E →+* ℂ}
      {ι : (NumberField.InfinitePlace F → ℂ) →+ Formalism.IndefR.DatumF.AEF F E},
      PositivityTheory.ThKW.Ctx σ B JS JT ξ₀ θ ι → {t : E | t * (σ : E → E) t = (1 : E)}.Infinite := by
  intro F E _ _ _ _ _ σ B nS nT JS JT ξ θ ι h
  obtain ⟨-, -, -, h0, hσ, -, -⟩ := h
  have hz : ∀ n : ℤ, (n : E) - ξ ≠ 0 := fun n hn => h0 <| by
    have e : ξ = (n : E) := (sub_eq_zero.mp hn).symm
    have e2 : σ ξ = ξ := by rw [e, map_intCast]
    linear_combination (1 / 2 : E) * hσ - (1 / 2 : E) * e2
  have hp : ∀ n : ℤ, (n : E) + ξ ≠ 0 := fun n hn => hz (-n) <| by
    push_cast; linear_combination -hn
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => ((n : E) + ξ) / ((n : E) - ξ))
    (fun n m hnm => ?_) (fun n => ?_)
  · have e := (div_eq_div_iff (hz n) (hz m)).mp hnm
    have e2 : ((n : E) - m) * ξ = 0 := by linear_combination (-1 / 2 : E) * e
    exact Int.cast_injective (sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right h0))
  · simp only [Set.mem_setOf_eq, map_div₀, map_add (f := _), map_sub, map_intCast, hσ, sub_neg_eq_add,
      ← sub_eq_add_neg]
    rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hz n) (hp n))]
end
