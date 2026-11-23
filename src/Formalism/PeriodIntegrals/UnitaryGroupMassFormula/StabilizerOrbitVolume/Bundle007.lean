module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle005
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.Bundle018

@[expose] public section

section

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation

section B

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => hR R σ J (X i) (Y j) + hR R σ J (Y i) (X j)

theorem hR_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y z : Fin M → R ⊗[F] E) : hR R σ J (x + y) z = hR R σ J x z + hR R σ J y z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y z : Fin M → R ⊗[F] E) : hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_herm (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  have hinv : ∀ a : R ⊗[F] E, sigR R σ (sigR R σ a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hJ' : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    simp [JR, inclR, sigR, hJ]

  simp only [hR, Formalism.UG.hform, map_sum, map_mul, hinv, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramB_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X Y : Fin n → Fin M → R ⊗[F] E) : gramB R σ J X Y ∈ HermR R σ n := by
  show ∀ a b, sigR R σ (gramB R σ J X Y b a) = gramB R σ J X Y a b
  intro a b
  simp only [gramB, map_add (f := _), hR_herm R σ hσ J hJ]
  ring

end B

section BTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_gramB_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      gramB R σ J p.1 p.2 a b) := by
  show Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
    hR R σ J (p.1 a) (p.2 b) + hR R σ J (p.2 a) (p.1 b))
  have hc := continuous_hR R σ J
  have e1 : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      ((p.1 a, p.2 b) : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E))) := by fun_prop
  have e2 : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      ((p.2 a, p.1 b) : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E))) := by fun_prop
  have h1 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc e1
  have h2 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc e2
  exact h1.add h2

theorem continuous_gramB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      gramB R σ J p.1 p.2) := by
  exact continuous_pi fun a => continuous_pi fun b => continuous_gramB_apply R σ J a b

end BTop

end PI.VolStabSW
end
end

section

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def DensAll {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    Prop :=
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

def FibOfDens : Prop :=
  ∀ (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    [T2Space V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] (μ : Measure V) (ν : Measure X),
    IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → ν.IsOpenPosMeasure →
    ∀ (f : V → Y) (ι : X → Y) (U : Set V), Continuous f → IsClosedEmbedding ι →
      (∀ v, f v ∈ Set.range ι) → IsOpen U → DensAll μ f ι ν U →
      ∃ fib : X → Measure V, IsFibreFamily μ f ι U ν Set.univ fib

def TensFacts (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : Prop :=
  LocallyCompactSpace (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧
    IsClosed (HermR R σ a : Set (Matrix (Fin a) (Fin a) (R ⊗[F] E))) ∧
    Continuous (gramR R σ J (n := a)) ∧ (∀ X, gramR R σ J (n := a) X ∈ HermR R σ a) ∧
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}

theorem fib_of_tens {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {a : ℕ} {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] (hG : FibOfDens) (hT : TensFacts F E σ M J a R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hD : DensAll μ (gramR R σ J) Subtype.val ν {X | LinearIndependent (R ⊗[F] E) X}) :
    ∃ fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E),
      IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
        Set.univ fib := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hT
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR R σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → R ⊗[F] E))
  have : LocallyCompactSpace (HermR R σ a) := h4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR R σ a) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact hG _ _ _ μ ν inferInstance inferInstance inferInstance _ _ _ h5
    h4.isClosedEmbedding_subtypeVal (fun X => ⟨⟨_, h6 X⟩, rfl⟩) h7 hD

end PI.VolStabSW
end
end

section

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix

section Mat

variable {A : Type} [CommRing A] (s : A →+* A)

end Mat

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

variable {b v}

theorem sigR_incl (σ : E →ₐ[F] E) (e : E) :
    sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem sigR_smul (σ : E →ₐ[F] E) (c : Fv F v) (z : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • z) = c • sigR (Fv F v) σ z := by
  rw [Algebra.smul_def, map_mul, sigR_algebraMap, ← Algebra.smul_def]

end Int

end PI.VolStabSW
end
end
