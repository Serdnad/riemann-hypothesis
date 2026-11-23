module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Matrix.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Discriminant
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePSplit

open Polynomial

def SplitSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : O →+* Matrix (Fin n) (Fin n) C) (P : Matrix (Fin n) (Fin n) C) (em : ι → (O →+* C)),
    P * P = P → (∀ x, P * M x = M x * P) → Function.Injective em →
    (∀ x, Polynomial.aeval (M x) (∏ c, (X - Polynomial.C (em c x))) * P = 0) →
    ∀ v : Fin n → C, ∃ w : ι → (Fin n → C), Matrix.mulVec P v = ∑ c, w c ∧ ∀ c x, Matrix.mulVec (M x) (w c) = em c x • w c

end RowTiePSplit

end Formalism.L2.FormalSeriesBounds
end

section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def JointEigSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C], IsAlgClosed C → ∀ (n q : ℕ), 2 ≤ q →
    ∀ (T : Set (Matrix (Fin n) (Fin n) C)), (∀ t ∈ T, t ^ q = t) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
    ∀ v : Fin n → C, ∃ (m : ℕ) (w : Fin m → Fin n → C), v = ∑ j, w j ∧
      ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Chars

variable {F A L : Type} [CommRing F] [CommRing A] [Algebra F A] [Field L] {ι' ι : Type} [Fintype ι'] [Fintype ι]

theorem char_indep (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) (c : ι' → L) (hc : ∀ i, ∑ j, c j * χ j (b i) = 0) :
    c = 0 := by
  have key : ∀ x : A, ∑ j, c j * χ j x = 0 := by
    intro x
    obtain ⟨r, hr⟩ := hb x
    have hx : ∀ j, χ j x = ∑ i, φ (r i) * χ j (b i) := by
      intro j
      have h1 : χ j (e * x) = χ j x := by rw [map_mul, he, one_mul]

      rw [← h1, hr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hφ]
    calc ∑ j, c j * χ j x = ∑ j, ∑ i, c j * (φ (r i) * χ j (b i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hx j, Finset.mul_sum]
      _ = ∑ i, φ (r i) * ∑ j, c j * χ j (b i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by simp [hc]
  have hli : LinearIndependent L (fun j => ((χ j).toMonoidHom : A → L)) := by
    have h := (linearIndependent_monoidHom A L).comp (fun j => (χ j).toMonoidHom) (by
      intro j k hjk
      apply hχ
      ext x
      exact DFunLike.congr_fun hjk x)
    exact h
  funext j
  have h2 := Fintype.linearIndependent_iff.mp hli c (by
    funext x
    rw [Finset.sum_apply]
    exact key x)
  exact h2 j

theorem card_le_of_chars (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : Fintype.card ι' ≤ Fintype.card ι := by
  have hli : LinearIndependent L (fun j : ι' => fun i : ι => χ j (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := char_indep χ hχ φ hφ e he b hb g (fun i => by
      have h3 := congrFun hg i
      rw [Finset.sum_apply] at h3
      exact h3)
    intro j
    simp [h0]
  simpa using hli.fintype_card_le_finrank

theorem det_ne_zero_of_chars [DecidableEq ι] (χ : ι → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : (Matrix.of fun i j => χ j (b i)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply char_indep χ hχ φ hφ e he b hb v
  intro i
  have h := congrFun hv i
  calc ∑ j, v j * χ j (b i) = ∑ j, χ j (b i) * v j :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = 0 := by
        first
        | exact h
        | simpa [Matrix.mulVec, dotProduct] using h

end Chars

section Label

end Label

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

def tauX {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE] {R : Type} [CommRing R] [Algebra ℤ_[l] R] (τ : OE →+* R) :
    (ℤ_[l] ⊗[ℤ] OE) →ₐ[ℤ_[l]] R :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[l] R) τ.toIntAlgHom (fun _ _ => Commute.all _ _)

def EmbX {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE] {R : Type} [CommRing R] [Algebra ℤ_[l] R]
    (e : ℤ_[l] ⊗[ℤ] OE) : Set (OE →+* R) := {τ | tauX τ e = 1}

def PlaceX (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ e : ℤ_[l] ⊗[ℤ] OE, e * e = e ∧ e ≠ 0 ∧ (∀ f : ℤ_[l] ⊗[ℤ] OE, f * f = f → f * e = f → f = 0 ∨ f = e) ∧
    ∃ (_ : NeZero (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))))
      (t : Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) ≃ EmbX (R := R) e)
      (jj : ZMod d ≃ Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))),
      (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))) ℤ_[l]
          (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)),
        IsUnit (Matrix.det (Matrix.of fun i j =>
          tauX ((t j : EmbX (R := R) e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def PlaceCriterionOfIdempotent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra ℤ_[l] R],
    (l : R) ∈ maximalIdeal R → ¬ ((l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (d : ℕ) [NeZero d] (em : ZMod d → OE →+* R),
      (∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) →
      (∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) →
      (∃ ε : OE, (∃ y, ε * ε - ε = (l : OE) * y) ∧ (∀ a, em a ε - 1 ∈ maximalIdeal R) ∧
        ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) → PlaceX l OE R d em

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end
