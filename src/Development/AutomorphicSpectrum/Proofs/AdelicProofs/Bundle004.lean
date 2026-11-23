module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.log_norms_of_nonzero_adelic : ∀ (k : Type) [Field k] [NumberField k] (x : k), x ≠ 0 → (LogNorms.ofElt x).IsAdelic := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt | exact GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt <;> assumption)
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem logIdeal_mul_span_map : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]), Function.Injective j → (∀ I J : Ideal (𝓞 E), I ≠ ⊥ → J ≠ ⊥ → logIdeal j (I * J) = logIdeal j I + logIdeal j J) ∧ (∀ a : 𝓞 E, logIdeal j (Ideal.span {a}) = Real.log ‖j a‖) ∧ ∀ e : 𝓞 E ≃+* 𝓞 E, ∀ I : Ideal (𝓞 E), logIdeal j (I.map (e : 𝓞 E →+* 𝓞 E)) = logIdeal (j.comp (e : 𝓞 E →+* 𝓞 E)) I :=
  @PositivityTheory.Xgf.log_ideal_mul_span_map

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem finite_logIdeal_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ →
    {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite :=
  @PositivityTheory.Xgf.logIdeal_support_finite

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem logNorms_ext_deg_isAdelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) :=
  @PositivityTheory.Xgf.logNorms_ext_degree_adelic

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_logIdeal_attained : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E)), Function.Injective j → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) ∧ logIdeal j I = Real.log ‖j a‖ :=
  @PositivityTheory.Xgf.padic_logIdeal_max_element

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem rat_product_formula_complex : ∀ r : ℚ, r ≠ 0 → {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0 :=
  PositivityTheory.Xgf.rat_product_formula

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.padic_embedding_discrete_valuation_ring : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes) (j : K →+* ℂ_[p]), ∃ (V : ValuationSubring K), IsDiscreteValuationRing V ∧ (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V) ∧ (∀ a : 𝓞 K, (a : K) ∈ V) ∧ ∀ n : ℕ, ¬ (p : ℕ) ∣ n → ‖j (n : K)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding | exact GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Lines

open NumberField TensorProduct GroundTheory.Heights₂.Heights Matrix
open scoped ComplexOrder nonZeroDivisors

noncomputable section

theorem gramAt_standard {L : Type} [Field L] {i : ℕ} (h : Matrix (Fin i) (Fin i) ℂ) (σ : L →+* ℂ) :
    gramAt h σ (fun j : Fin i => (Pi.single j 1 : Fin i → L)) = h := by
  have he : ∀ j : Fin i, embVec σ (Pi.single j 1 : Fin i → L) = Pi.single j 1 := by
    intro j
    funext k
    by_cases hk : k = j
    · subst hk; simp [embVec]
    · simp [embVec, Pi.single_eq_of_ne hk]
  ext a b
  simp [gramAt, he, Matrix.mulVec_single_one, Matrix.col_apply]

theorem degree_eq_degreeWith (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L))
    (Fl : HermLattice L i) (hf : LinearIndependent (𝓞 L) f) (hi : i = B.rank F)
    (hc : Function.Injective c) (hcf : ∀ j, c (f j) = Pi.single j 1)
    (hlat : Fl.lattice = LinearMap.range c)
    (hmet : ∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) :
    Fl.degree = B.degreeWith F f := by
  have hspanK : Submodule.span L (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) = ⊤ := by
    have h : (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) =
        Set.range (Pi.basisFun L (Fin i)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]
    exact (Pi.basisFun L (Fin i)).span_eq
  have hS : (Submodule.span (𝓞 L) (Set.range f)).map c =
      Submodule.span (𝓞 L) (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact congrArg _ (congrArg Set.range (funext hcf))
  have hA : (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i =>
      (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)) = LinearMap.range c := by
    rw [hspanK, hlat, Submodule.restrictScalars_top, inf_top_eq]
  have hidx : genIndex
      (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i =>
        (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)).toAddSubgroup
      (Submodule.span (𝓞 L) (Set.range fun j : Fin i =>
        (Pi.single j 1 : Fin i → L))).toAddSubgroup =
      (Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range f)) : ℝ) := by
    rw [hA, ← hS, genIndex]
    have hle : ((Submodule.span (𝓞 L) (Set.range f)).map c).toAddSubgroup ≤
        (LinearMap.range c).toAddSubgroup := by
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    rw [AddSubgroup.relIndex_eq_one.mpr hle, LinearMap.range_eq_map, Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hc,
      Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    simp
    rfl
  have hgram : ∀ σ : L →+* ℂ,
      (gramAt (Fl.metric σ) σ fun j : Fin i => (Pi.single j 1 : Fin i → L)).det.re =
        ‖HermitianBundle.gramDet B σ (fun j => (f j : B.carrier))‖ := by
    intro σ
    have hd : HermitianBundle.gramDet B σ (fun j => (f j : B.carrier)) = (Fl.metric σ).det := by
      rw [hmet σ]
      rfl
    rw [gramAt_standard, hd]
    have hp : 0 < (Fl.metric σ).det := (Fl.posDef σ).det_pos
    have hre : ((Fl.metric σ).det.re : ℂ) = (Fl.metric σ).det := by
      apply Complex.ext
      · simp
      · simpa using (Complex.lt_def.mp hp).2.symm ▸ rfl
    rw [← hre, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    exact (Complex.lt_def.mp hp).1
  simp only [HermLattice.degree, subDegree, HermitianBundle.degreeWith, hidx, hgram]

end

end GlobalTheory.CompanionTheory.Ar.Lines
end

section

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem finrank_mul_sum_comp_eq : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j :=
  PositivityTheory.Xgf.sum_embeddings_base_change

end GlobalTheory.CompanionTheory.Ar.Fl
end
