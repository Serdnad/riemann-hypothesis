module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Tactic.Continuity
import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
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
public import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def ComplexMinimalPrimesContract.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    ∀ Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
      Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def PolySandwich.Statement : Prop :=
  ∀ (D c : ℕ) (p q : Polynomial ℚ), q.natDegree ≤ D →
    (∀ᶠ n : ℕ in Filter.atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ) ∧ q.eval (n : ℚ) ≤ p.eval ((n : ℚ) + c)) →
    p.natDegree ≤ D ∧ p.coeff D = q.coeff D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter

def PolyNonnegAtZero.Statement : Prop :=
  ∀ (d : ℕ) (p : Polynomial ℝ) (c : ℝ), 0 < c →
    (∀ t : ℚ, 0 < t → 0 < p.eval (t : ℝ) → c * (t : ℝ) ^ d ≤ p.eval (t : ℝ)) →
    (∀ᶠ t in atTop, 0 < p.eval t) → 0 ≤ p.eval 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set

noncomputable section

def ChartSupBound.Statement : Prop :=
  ∀ (D : ℕ) (V K : Set (Fin D → ℂ)) (ψ ν : (Fin D → ℂ) → ℝ), IsOpen V → IsCompact K → K ⊆ V →
    ContDiffOn ℝ 2 ψ V → ContinuousOn ν V → (∀ z ∈ V, 0 < ν z) →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ F : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ F V → ∀ w ∈ K,
      ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w)) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ D) *
          ∫⁻ z in V, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(n : ℝ) * ψ z) * ν z)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def CharpolyRootLift.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω) (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ),
      l j ≠ 0 → c 0 = 1 → (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) →
      (LinearMap.charpoly (Algebra.lmul P Ω (u / l j ^ m))).map (algebraMap P Ω) =
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
      ∀ (a : Fin (D + 1)) (hu : u / l a ^ m ∈
          integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω)
        (ζ : Fin (D + 1) → ℂ), ζ a ≠ 0 → ∀ w : ℂ,
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (Module.finrank P Ω - i) = 0 →
        ∃ ψ : integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω →+* ℂ,
          (∀ (k : Fin (D + 1)) (hk : l k / l a ∈
              integralClosure (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) Ω),
            ψ ⟨l k / l a, hk⟩ = ζ k / ζ a) ∧
          ψ ⟨u / l a ^ m, hu⟩ = w / ζ a ^ m

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def ConstantsDescend.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (R T : Subalgebra ℤ Ω), R.FG → Module.Finite ℤ T →
    (∀ w w' : ↥(R ⊔ T) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom) →
    ∃ m : ℕ, 1 ≤ m ∧ ∀ t ∈ T, (m : Ω) * t ∈ R

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def IndependentModBaseChange.Statement : Prop :=
  ∀ (σ : Type) (P : Ideal (MvPolynomial σ ℤ)) (r : ℕ) (g : Fin r → MvPolynomial σ ℤ),
    LinearIndependent ℤ (fun i => Ideal.Quotient.mk P (g i)) →
    LinearIndependent ℂ (fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomNormPIntegral.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (p : ℕ), p.Prime → ∀ M : ℕ, ¬ p ∣ M → ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      u ∈ integralClosure (Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j))) Ω →
      ∀ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ,
        (c (Module.finrank P Ω)).IsHomogeneous (Module.finrank P Ω * m) →
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
        ∀ μ : Fin (D + 1) →₀ ℕ, 0 ≤ padicValRat p ((c (Module.finrank P Ω)).coeff μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def NormFormGaussBound.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ p : ℕ, p.Prime → ∀ (j : Fin (D + 1)) (K d : ℕ) (x : Ω) (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ),
      (c (Module.finrank P Ω)).IsHomogeneous d →
      (LinearMap.charpoly (Algebra.lmul P Ω x)).map (algebraMap P Ω) =
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
      (p : Ω) ^ K * x ∈ integralClosure
        (Subring.closure ({z | ∃ i k, z = l i / l k} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})) Ω →
      ∀ μ : Fin (D + 1) →₀ ℕ,
        -((Module.finrank P Ω * K : ℕ) : ℤ) ≤ padicValRat p ((c (Module.finrank P Ω)).coeff μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomCharpolyForms.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      (∀ k, u * (l j / l k) ^ m ∈ integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω) →
      ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, c 0 = 1 ∧
        (∀ i ≤ Module.finrank P Ω, (c i).IsHomogeneous (i * m)) ∧
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) ∧
        (u ≠ 0 → c (Module.finrank P Ω) ≠ 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace TranscRatioDeg

open Polynomial

theorem transcendental_subfieldClosure {E : Type*} [Field E] {ι : Type*} (u : ι → E) (t : E)
    (ht : Transcendental (Algebra.adjoin ℤ (Set.range u)) t) :
    Transcendental (Subfield.closure (Set.range u)) t := by
  have hR : ∀ x, x ∈ Algebra.adjoin ℤ (Set.range u) ↔ x ∈ Subring.closure (Set.range u) := fun x => by
    rw [Algebra.adjoin_int]; rfl
  set R := Algebra.adjoin ℤ (Set.range u)
  set Q := Subfield.closure (Set.range u)
  have hmem : ∀ x : R, (x : E) ∈ Q := fun x => Subfield.subring_closure_le _ ((hR x).1 x.2)
  let _ : Algebra R Q := RingHom.toAlgebra
    { toFun := fun x => ⟨x.1, hmem x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have : IsScalarTower R Q E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul R Q := (faithfulSMul_iff_algebraMap_injective R Q).2
    (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have : IsFractionRing R Q := IsFractionRing.of_field R Q (fun z => by
    obtain ⟨y, hy, z', hz', h⟩ := Subfield.mem_closure_iff.1 z.2
    exact ⟨⟨y, (hR y).2 hy⟩, ⟨z', (hR z').2 hz'⟩, Subtype.ext (by rw [Subfield.coe_div]; exact h.symm)⟩)
  intro halg
  exact ht ((IsFractionRing.isAlgebraic_iff R Q E).2 halg)

theorem transcendental_of_subfield {E : Type*} [Field E] {S : Type*} [CommRing S] [Algebra S E]
    (Q : Subfield E) (h : ∀ x : S, algebraMap S E x ∈ Q) (hinj : Function.Injective (algebraMap S E))
    {t : E} (ht : Transcendental Q t) : Transcendental S t := by
  rintro ⟨p, hp0, hp⟩
  let φ : S →+* Q := (algebraMap S E).codRestrict Q h
  have hφ : Function.Injective φ := fun a b hab => hinj (congrArg Subtype.val hab :)
  refine ht ⟨p.map φ, (Polynomial.map_ne_zero_iff hφ).2 hp0, ?_⟩
  rw [aeval_def, eval₂_map]
  exact hp


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem linearIndependent_adjoin_of_transcendental {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) {κ : Type*} {b : κ → A}
    (hb : LinearIndependent K b) :
    LinearIndependent (IntermediateField.adjoin K {t}) (A.val ∘ b) :=
  open scoped IntermediateField.algebraAdjoinAdjoin in by
  letI : Algebra (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K {t})).toAlgebra
  letI : FaithfulSMul (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
      Subtype.ext (by simpa using congrArg (fun x : IntermediateField.adjoin K {t} => (x : E)) h)
  letI : IsFractionRing (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    IsFractionRing.of_field _ _ fun ⟨_, h⟩ =>
      have ⟨x, hx, y, hy, eq⟩ := IntermediateField.mem_adjoin_iff_div.mp h
      ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩
  letI : IsScalarTower (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine (LinearIndependent.iff_fractionRing (Algebra.adjoin K {t})
    (IntermediateField.adjoin K {t})).1 ?_
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hp : ∀ j, ∃ p : K[X], aeval t p = (g j : E) := fun j => by
    have h : (g j : E) ∈ (aeval t : K[X] →ₐ[K] E).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (g j).2
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp⟩
  choose p hp using hp
  have hsum : ∑ j ∈ s, aeval t (p j) * (b j : E) = 0 := by
    simpa [hp, Subalgebra.smul_def] using hg
  let P : A[X] := ∑ j ∈ s, C (b j) * (p j).map (algebraMap K A)
  have hP : aeval t P = 0 := by

    simp only [P, map_sum, map_mul, aeval_C, aeval_map_algebraMap]
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  have hP0 : P = 0 := by
    by_contra hne
    exact ht ⟨P, hne, hP⟩
  have hcoeff : ∀ n, ∑ j ∈ s, (p j).coeff n • b j = 0 := by
    intro n
    have := congrArg (fun q => q.coeff n) hP0
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := by
    ext n
    exact linearIndependent_iff'.1 hb s (fun j => (p j).coeff n) (hcoeff n) i hi
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl

theorem finrank_adjoin_eq_of_transcendental {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) :
    Module.finrank (IntermediateField.adjoin K {t})
      (IntermediateField.adjoin (IntermediateField.adjoin K {t}) (A : Set E)) = Module.finrank K A := by
  set L := IntermediateField.adjoin K {t}
  let a := Module.Free.chooseBasis K A
  have hind : LinearIndependent L (A.val ∘ a) :=
    linearIndependent_adjoin_of_transcendental A ht a.linearIndependent
  by_cases hfin : Module.Finite K A
  · have H : A.LinearDisjoint L := IntermediateField.LinearDisjoint.of_basis_left a hind
    have hr := H.adjoin_rank_eq_rank_left_of_isAlgebraic_left
    exact congrArg Cardinal.toNat hr
  · rw [Module.finrank_of_not_finite hfin]
    set M := IntermediateField.adjoin L (A : Set E)
    letI : Module.Free L M := Module.Free.of_divisionRing L M
    refine Module.finrank_of_not_finite (M := M) ?_
    intro hfin'
    apply hfin
    let f : Module.Free.ChooseBasisIndex K A → M :=
      fun k => ⟨A.val (a k), IntermediateField.subset_adjoin L _ (a k).2⟩
    have hf : LinearIndependent L f := LinearIndependent.of_comp M.val.toLinearMap hind
    have : Finite (Module.Free.ChooseBasisIndex K A) := hf.finite
    exact Module.Finite.of_basis a

theorem finrank_adjoin_congr {E Φ L : Type*} [Field E] [Field Φ] [Field L] [Algebra Φ E] [Algebra L E]
    {S T : Set E} (h : (algebraMap Φ E).fieldRange = (algebraMap L E).fieldRange)
    (hST : Subfield.closure (Set.range (algebraMap Φ E) ∪ S) =
      Subfield.closure (Set.range (algebraMap L E) ∪ T)) :
    Module.finrank Φ (IntermediateField.adjoin Φ S) = Module.finrank L (IntermediateField.adjoin L T) := by
  let i : Φ ≃+* L := ((algebraMap Φ E).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr h)).trans
    (algebraMap L E).rangeRestrictFieldEquiv.symm
  have hi : ∀ r, algebraMap L E (i r) = algebraMap Φ E r := fun r => by
    simp only [i, RingEquiv.trans_apply, RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    rfl
  have hmem : ∀ x : E, x ∈ IntermediateField.adjoin Φ S ↔ x ∈ IntermediateField.adjoin L T := fun x => by
    rw [← IntermediateField.mem_toSubfield, ← IntermediateField.mem_toSubfield,
      IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, hST]
  let j : IntermediateField.adjoin Φ S ≃+ IntermediateField.adjoin L T :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩, invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  have hr := rank_eq_of_equiv_equiv i j i.bijective (fun r m => Subtype.ext (by
    simp only [j, AddEquiv.coe_mk, Equiv.coe_fn_mk, Algebra.smul_def]
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul]
    exact congrArg (· * (m : E)) (hi r).symm))
  exact congrArg Cardinal.toNat hr

end TranscRatioDeg

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField

def UnitApprox.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (u : (F →+* ℂ) → ℝ),
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ C : ℝ, ∀ n : ℕ, ∃ ε : (𝓞 F)ˣ, ∀ sg : F →+* ℂ,
      |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ C

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
