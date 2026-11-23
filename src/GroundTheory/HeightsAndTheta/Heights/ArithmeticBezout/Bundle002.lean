module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ZeroLocusDimH

theorem ringKrullDim_le_of_isIntegral_inj {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by
  rcases isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA
  · rw [ringKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  rw [ringKrullDim, Order.krullDim_eq_iSup_length]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R)
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

theorem aeval_derivative_minpoly_ne_zero {R A : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] (hinj : Function.Injective (algebraMap R A)) (x : A) :
    Polynomial.aeval x (Polynomial.derivative (minpoly R x)) ≠ 0 := by
  have : Module.IsTorsionFree R A := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have hx : IsIntegral R x := Algebra.IsIntegral.isIntegral x
  intro h0
  have hdvd := minpoly.isIntegrallyClosed_dvd hx h0
  have hmon := minpoly.monic hx
  have hne : Polynomial.derivative (minpoly R x) ≠ 0 := by
    intro hd
    exact (minpoly.natDegree_pos hx).ne' (Polynomial.derivative_eq_zero.1 hd)
  have h1 := Polynomial.degree_le_of_dvd hdvd hne
  have h2 := Polynomial.degree_derivative_lt hmon.ne_zero
  exact absurd h1 (not_le.2 h2)

theorem exists_simple_root_data {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [hp : p.IsPrime] :
    ∃ s : ℕ, (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ∧
    ∃ (π : Fin s → MvPolynomial (Fin n) ℂ) (P : Fin n → Polynomial (MvPolynomial (Fin s) ℂ)),
      (∀ i, (P i).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∈ p) ∧
      (∀ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∉ p) := by
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ p) := Ideal.Quotient.nontrivial_iff.2 hp.ne_top
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ p)
  let _ : Algebra (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := ⟨hint⟩
  have hdim : ringKrullDim (MvPolynomial (Fin s) ℂ) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  refine ⟨s, hdim ▸ ringKrullDim_le_of_isIntegral_inj hinj, ?_⟩
  choose π hπ using fun j : Fin s => Ideal.Quotient.mk_surjective (I := p) (g (X j))
  have hcomp : (Ideal.Quotient.mk p).comp (MvPolynomial.aeval π).toRingHom =
      algebraMap (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      change _ = g (C a)
      rw [← MvPolynomial.algebraMap_eq, g.commutes]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact hπ j
  have hkey : ∀ (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (i : Fin n),
      Ideal.Quotient.mk p (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
        Polynomial.aeval (Ideal.Quotient.mk p (X i)) Q := by
    intro Q i
    rw [Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def]
  have hx : ∀ i : Fin n, IsIntegral (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)) :=
    fun i => Algebra.IsIntegral.isIntegral _
  refine ⟨π, fun i => minpoly (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)), fun i => ?_,
    fun i => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey, minpoly.aeval]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey]
    exact aeval_derivative_minpoly_ne_zero hinj _

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartParAlgebraic.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.IsAlgebraic
        (Algebra.adjoin (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (Set.range fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1)))) L

def ChartFreeParAlgIndep.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal) →
      AlgebraicIndependent (IntermediateField.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1))) ∧
        Algebra.IsAlgebraic K L

def ChartPointSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F)
    (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    (∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal)) →
      Algebra.IsSeparable K L

section Inhabitants

namespace ChartPointLine

end ChartPointLine

open ChartPointLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory

noncomputable section

namespace ObjectsHeight

variable {n : ℕ}

variable {k : ℕ}

theorem map_curry_volume :
    (volume : Measure (Fin k × Fin n → ℂ)).map (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) =
      Measure.pi fun _ : Fin k => (volume : Measure (Fin n → ℂ)) := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  show Measure.pi (fun _ : Fin k × Fin n => (volume : Measure ℂ)) = _
  refine Measure.pi_eq fun s hs => ?_
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_curry_symm]
  have hset : Function.uncurry ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : Fin k => Set.univ.pi fun j : Fin n => s (i, j) := by
    ext x
    simp
  rw [hset, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [Fintype.prod_prod_type]

end ObjectsHeight

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

theorem ChartGram.det_eq_corner_mul_schur {K : Type*} [Field K] {e : ℕ}
    (M : Matrix (Fin (e + 1)) (Fin (e + 1)) K) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 *
      (Matrix.of fun i j : Fin e => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0).det := by
  set c : Fin (e + 1) → K := fun i => if i = 0 then 0 else -(M i 0 / M 0 0) with hc
  set B : Matrix (Fin (e + 1)) (Fin (e + 1)) K := Matrix.of fun i j => M i j + c i * M 0 j with hB
  have hdet : B.det = M.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [hc]) (fun i j => by simp [hB])
  rw [← hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin e, B i.succ 0 = 0 := by
    intro i
    simp only [hB, hc, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    field_simp
    ring
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero]
  congr 1
  · simp [hB, hc]
  · congr 1
    ext i j
    simp only [hB, hc, Matrix.submatrix_apply, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    ring

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def TrdegAdjoinLe.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (s : Set Ω) (ι : Type) [Fintype ι] (t : ι → Ω)
    (ι' : Type) (w : ι' → Ω), (∀ i, IsAlgebraic (Algebra.adjoin K (s ∪ Set.range t)) (w i)) →
      Algebra.trdeg K (Algebra.adjoin K (Set.range w)) ≤
        Algebra.trdeg K (Algebra.adjoin K s) + Fintype.card ι

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def TrdegBaseAlgebraic.Statement : Prop :=
  ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra K Ω] [Algebra F Ω]
    [IsScalarTower F K Ω], Algebra.IsAlgebraic F K → ∀ (ι : Type) (z : ι → Ω),
      Algebra.trdeg K (Algebra.adjoin K (Set.range z)) ≤ Algebra.trdeg F (Algebra.adjoin F (Set.range z))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def quotToPiMinimalPrimes {B : Type*} [CommRing B] (J : Ideal B) :
    (B ⧸ J) →ₗ[B] ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) :=
  LinearMap.pi fun P => Submodule.factor P.2.1.2

def PiQuotCokerFiniteLength.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (J : Ideal B),
    J.IsRadical →
    (∀ Q : Ideal B, Q.IsPrime → J ≤ Q → Q ∈ J.minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B) →
      Function.Injective (quotToPiMinimalPrimes J) ∧
        IsFiniteLength B
          (((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) ⧸ LinearMap.range (quotToPiMinimalPrimes J))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ZeroLocusDimH.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} ≤ 2 * (d : ENNReal)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def LocalSectionLengthSum.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (J : Ideal B) (f : B),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    (∀ Q : Ideal B, Q.IsPrime → J ≤ Q → Q ∈ J.minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B) →
      Module.length B (B ⧸ (J ⊔ Ideal.span {f})) =
        ∑ P ∈ (J.finite_minimalPrimes_of_isNoetherianRing B).toFinset,
          Module.length B (B ⧸ (P ⊔ Ideal.span {f}))

end GroundTheory.Heights₂.Heights
end
