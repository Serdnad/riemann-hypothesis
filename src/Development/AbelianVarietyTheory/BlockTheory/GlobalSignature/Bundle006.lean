module

public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.NumberField.ClassNumber
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

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassesDoubleCosets

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

def CosetMass {G : Type} [Group G] (Γ K : Subgroup G) (m : ℝ) : Prop :=
  Finite (ClassSet Γ K) ∧
  (∀ y : G, Finite (stabAt Γ K y)) ∧
  ∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
    ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m

def stabHat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E) (N : Submodule (𝓞 E) W.V) : Subgroup (UAf hc W) :=
  (stabGL (hatL (F := F) (crdLat W N))).subgroupOf (UAf hc W)

def General : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E), W.SigOK → W.IsPosDef →
    ∀ N : Submodule (𝓞 E) W.V, Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular W.hT N →
      CosetMass (UFin hc W) (stabHat hc W N) (Formalism.HermitianLatticesTheory.mass W.hT N)

def DefiniteSpaceClassStatement (D : D7) (_Lv : LevelData D) (_u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  ∀ N : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E N →
    Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT N →
    CosetMass
      ((ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
        (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      ((levelAfL D.sp.cm.sig D.sp.gram0 (D.sp.crdLat0 N)).subgroupOf
        (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT N)

def ClassesAsDoubleCosets : Prop :=
  General ∧ ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), DefiniteSpaceClassStatement D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.ClassesDoubleCosets

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def MeanPeriodAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D (tor0 D cc δ) M →
    ∀ τ : D.what₂.Tau, meanLogOm D (tor0 D cc δ).abelian₂ M τ = logOmVal D

def MeanPeriod : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    MeanPeriodAt D cc δ

theorem logOmVal_eq (D : D7) :
    logOmVal D = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / D.host.rdE) - logDerivativeAtOne D := by
  have h : Real.pi / D.host.v = 2 * Real.pi / D.host.rdE := by
    unfold Host.v
    rw [div_div_eq_mul_div, mul_comm]
  unfold logOmVal
  rw [h]

end GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement

open Formalism.MainNotions.TaylorLogMetric
open scoped UpperHalfPlane

def latt (ω₁ τ : ℂ) : AddSubgroup ℂ where
  carrier := {w | ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ)}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    exact ⟨m + m', n + n', by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨m, n, rfl⟩
    exact ⟨-m, -n, by push_cast; ring⟩

def scale (c : ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ := Λ.map (AddMonoidHom.mulLeft c)

def period (Λ : AddSubgroup ℂ) : ℝ := ‖discr Λ‖ ^ ((1 : ℝ) / 6) * area Λ / Real.pi

def DiscrEta : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 →
    discr (latt ω₁ τ) = (2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24

def AreaEq : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 → area (latt ω₁ τ) = ‖ω₁‖ ^ 2 * τ.im

def PeriodEta : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 →
    period (latt ω₁ τ) = 4 * Real.pi * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4

def DiscrScale : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ) (c : ℂ), ω₁ ≠ 0 → c ≠ 0 →
    discr (scale c (latt ω₁ τ)) = c ^ (-12 : ℤ) * discr (latt ω₁ τ)

def AgreePeriodPair : Prop :=
  ∀ L : PeriodPair,
    (∀ k : ℕ, 2 ≤ k →
      Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧
      eisG L.lattice.toAddSubgroup k = L.G (2 * k)) ∧
    g2 L.lattice.toAddSubgroup = L.g₂ ∧ g3 L.lattice.toAddSubgroup = L.g₃

def LatticePeriodEta : Prop :=
  DiscrEta ∧ AreaEq ∧ PeriodEta ∧ DiscrScale ∧ AgreePeriodPair

theorem mem_latt {ω₁ τ w : ℂ} : w ∈ latt ω₁ τ ↔ ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ) := Iff.rfl

theorem mem_scale {c w : ℂ} {Λ : AddSubgroup ℂ} : w ∈ scale c Λ ↔ ∃ v ∈ Λ, c * v = w := by
  simp [scale, AddSubgroup.mem_map]

theorem scale_latt (c ω₁ τ : ℂ) : scale c (latt ω₁ τ) = latt (c * ω₁) τ := by
  ext w
  rw [mem_scale, mem_latt]
  constructor
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m, n, rfl⟩, by ring⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassMeanPeriods

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors

def period (D : D7) (c : (Ideal (𝓞 D.host.K))⁰) : ℝ :=
  ‖discr (lamOf D (c : Ideal (𝓞 D.host.K)) 1)‖ ^ ((1 : ℝ) / 6) *
    area (lamOf D (c : Ideal (𝓞 D.host.K)) 1) / Real.pi

def IsReps (D : D7) (r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰) : Prop :=
  ∀ C, ClassGroup.mk0 (r C) = C

def meanLogPeriod (D : D7) (r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰) : ℝ :=
  (∑ C : ClassGroup (𝓞 D.host.K), Real.log (period D (r C))) / (classNumber D.host.K : ℝ)

def classMeanValue (D : D7) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt (D.host.d : ℝ)) - logDerivativeAtOne D

def ClassMeanAt (D : D7) : Prop :=
  ∀ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, IsReps D r →
    meanLogPeriod D r = classMeanValue D

def ClassMean : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ClassMeanAt D

theorem exists_curveIdeal_delta (D : D7) :
    ∃ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (discr (lamOf D ⊤ 1)) (n := 12) (by norm_num)
  exact ⟨⊤, δ, ⟨top_ne_bot, by simp⟩, hδ⟩

theorem classMean_iff : ClassMean ↔ ∀ D : D7, ClassMeanAt D := by
  refine ⟨fun h D => ?_, fun h D _ _ _ _ => h D⟩
  obtain ⟨cc, δ, h1, h2⟩ := exists_curveIdeal_delta D
  exact h D cc δ h1 h2

end GlobalTheory.IndefiniteRowSideFullHecke.ClassMeanPeriods
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors

def ContainsData (D : D7) (M : IntermediateField ℚ ℂ) (Λ : AddSubgroup ℂ) : Prop :=
  (∀ x : D.host.K, D.host.φ₀ (x : D.host.E) ∈ M) ∧ g2 Λ ∈ M ∧ g3 Λ ∈ M

def FixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Prop :=
  ∀ (x : D.host.K) (y : M), (y : ℂ) = D.host.φ₀ (x : D.host.E) → ρ y = (y : ℂ)

def conjEmb (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : M →ₐ[ℚ] ℂ :=
  ((Complex.conjAe : ℂ →ₐ[ℝ] ℂ).restrictScalars ℚ).comp ρ

def HomotheticTo (D : D7) (Λ' : AddSubgroup ℂ) (c' : Ideal (𝓞 D.host.K)) : Prop :=
  ∃ x : ℂ, x ≠ 0 ∧ Λ' = lamOf D c' x

def normArea (D : D7) (c' : Ideal (𝓞 D.host.K)) : ℝ :=
  ‖Formalism.MainNotions.TaylorLogMetric.discr (lamOf D c' 1)‖ ^ ((1 : ℝ) / 6) * area (lamOf D c' 1)

def ConjugatesEquidistributed : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
  ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], ContainsData D M (lamOf D cc δ) →
    (∃ c : {ρ : M →ₐ[ℚ] ℂ // FixesK D M ρ} → (Ideal (𝓞 D.host.K))⁰,
      (∀ ρ, HomotheticTo D (lamConj M ρ.1 (lamOf D cc δ)) (c ρ : Ideal (𝓞 D.host.K))) ∧
      ∀ C C' : ClassGroup (𝓞 D.host.K),
        Nat.card {ρ // ClassGroup.mk0 (c ρ) = C} = Nat.card {ρ // ClassGroup.mk0 (c ρ) = C'}) ∧
    (∀ ρ : M →ₐ[ℚ] ℂ, ¬ FixesK D M ρ →
      FixesK D M (conjEmb M ρ) ∧
      area (lamConj M ρ (lamOf D cc δ)) = area (lamConj M (conjEmb M ρ) (lamOf D cc δ))) ∧
    (∀ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, (∀ C, ClassGroup.mk0 (r C) = C) →
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) =
        (∑ C : ClassGroup (𝓞 D.host.K), Real.log (normArea D (r C : Ideal (𝓞 D.host.K)))) /
          (classNumber D.host.K : ℝ))

theorem conjEmb_apply (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (y : M) :
    conjEmb M ρ y = (starRingEnd ℂ) (ρ y) := rfl

theorem exists_representatives (D : D7) :
    ∃ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, ∀ C, ClassGroup.mk0 (r C) = C :=
  ⟨Function.surjInv ClassGroup.mk0_surjective, Function.surjInv_eq _⟩

end GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates
end
end
