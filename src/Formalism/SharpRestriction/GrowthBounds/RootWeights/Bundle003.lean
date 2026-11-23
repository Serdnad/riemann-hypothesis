module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Mathlib.RingTheory.Derivation.Lie
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def linf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V) : ℕ :=
  sSup {k | ∃ nu ∈ wtsOf E W, (∑ a, nu a = 0) ∧ ∃ a, k = (nu a).natAbs}

def InvariantDenominatorLinftyBound : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (linf E (MQ M)))) • Inv x ∈ M

def InvariantProjectionDenominator : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • Inv x ∈ M

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees


open Classical in
def letterPolarizationDerivation (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    Derivation R (MvPolynomial (ι × Fin n) R) (MvPolynomial (ι × Fin n) R) :=
  ∑ l : ι,
    if l ∈ S then
      (if LL.vec l then (X (l, a) : MvPolynomial (ι × Fin n) R) • pderiv (l, b)
       else -((X (l, b) : MvPolynomial (ι × Fin n) R) • pderiv (l, a)))
    else 0

theorem v2con_sum_apply {R : Type*} [CommRing R] {σ : Type*} {α : Type*} (s : Finset α)
    (f : α → Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (F : MvPolynomial σ R) :
    (∑ i ∈ s, f i) F = ∑ i ∈ s, f i F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

theorem v2con_glAct_eq {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (F : MvPolynomial (ι × Fin n) R) : glAct R LL S a b F = letterPolarizationDerivation R LL S a b F := by
  unfold glAct letterPolarizationDerivation
  rw [LinearMap.sum_apply, v2con_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

open Classical in
theorem v2con_der_X {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (l : ι) (c : Fin n) : letterPolarizationDerivation R LL S a b (X (l, c)) =
      if l ∈ S then
        (if LL.vec l then (if c = b then X (l, a) else 0) else (if c = a then -X (l, b) else 0))
      else 0 := by
  unfold letterPolarizationDerivation
  rw [v2con_sum_apply, Finset.sum_eq_single l]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro l' _ hl'
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hl']
  · simp

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diagonal_rep (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem gl_commutation_apply {E : GLOps n K V} (hE : IsGLRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  have h := LinearMap.congr_fun (hE.1 a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have e1 : (if b = c then E a d else 0) x = (if b = c then E a d x else 0) := by split_ifs <;> rfl
  have e2 : (if d = a then E c b else 0) x = (if d = a then E c b x else 0) := by split_ifs <;> rfl
  rw [e1, e2] at h
  rw [add_sub_assoc, ← h]
  abel

theorem gl_rep_weight_shift {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {x : V}
    (hx : x ∈ weightSp E mu) (a b : Fin n) : E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diagonal_rep] at hx ⊢
  intro c
  rw [gl_commutation_apply hE c c a b x, hx c, map_smul]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  split_ifs <;> subst_vars <;> first | module | (exfalso; simp_all; done)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def restrictStableOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V)
    (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) : GLOps n K W := fun a b => (E a b).restrict (h a b)

def CompleteReducibilityIsotypic : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def ContravariantIsotypicOrthogonal : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ B : V →ₗ[K] V →ₗ[K] K, (∀ a b x y, B (E a b x) y = B x (E b a y)) →
      ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0

def HighestWeightDominant : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ lam v, IsHWV E lam v → Dominant lam

def SubrepRestrictionRep : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W),
      IsGLRep (restrictStableOperators E W h) ∧
      (∀ (mu : Fin n → ℤ) (x : W), x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu) ∧
      (∀ a b k (x : W), ((divPowE (restrictStableOperators E W h) a b k x : W) : V) = divPowE E a b k x) ∧
      (∀ a k (x : W), ((binomE (restrictStableOperators E W h) a k x : W) : V) = binomE E a k x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e →
        ∃ e' : Module.End K W, IsIsoProj (restrictStableOperators E W h) lam e' ∧ ∀ x : W, ((e' x : W) : V) = e x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e → (¬ ∃ v : W, IsHWV (restrictStableOperators E W h) lam v) →
        ∀ x ∈ W, e x = 0)

def PolynomialGLRepresentation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (LL : Letters ι),
    (∀ S, IsGLRep (glOps K n LL S)) ∧
    (∀ S S' : Set ι, Disjoint S S' → ∀ a b c d,
      glOps K n LL S a b * glOps K n LL S' c d = glOps K n LL S' c d * glOps K n LL S a b) ∧
    (∀ S S' : Set ι, S ⊆ S' → ∀ a b, glOps K n LL S' a b = glOps K n LL S a b + glOps K n LL (S' \ S) a b) ∧
    (∀ S d a b, ∀ F ∈ Pol K n d, glOps K n LL S a b F ∈ Pol K n d) ∧
    (∀ d : ι → ℕ, FiniteDimensional K (Pol K n d)) ∧
    (∀ S mu F, F ∈ weightSp (glOps K n LL S) mu → ∀ m ∈ F.support, wtS LL S m = mu) ∧
    (∃ B : MvPolynomial (ι × Fin n) K →ₗ[K] MvPolynomial (ι × Fin n) K →ₗ[K] K,
      (∀ F G, B F G = fock F G) ∧ ∀ S a b F G, B (glOps K n LL S a b F) G = B F (glOps K n LL S b a G))

def latticeMultidegreePart {O : Type} [CommRing O] [IsDomain O] {ι : Type} {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) : Submodule O (Pol (KK O) n d) :=
  L.comap (((Pol (KK O) n d).subtype).restrictScalars O)

def AdmissibleDVRIntegralFormLatticesStable : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O → CharZero (KK O) ∧
    ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι),
      (∀ S : Set ι, PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def casimirConjugation (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) : Module.End K (Module.End K V) :=
  ∑ i ∈ s, (LinearMap.mulLeft K (E c i)).comp (LinearMap.mulRight K (E i c))

def casimirPower (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (q : ℕ) : Module.End K V :=
  ((casimirConjugation E c s) ^ q) 1

def casimirPowerScaled (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (b q : ℕ) : Module.End K V :=
  ((b.factorial : K) / (((q + b).factorial : K) * (q.factorial : K))) • casimirPower E c s q

def extremalProjector (E : GLOps n K V) (c : Fin n) (L : ℕ) : Module.End K V :=
  ∑ q ∈ range (L + 1), ((-1 : K) ^ q) • casimirPowerScaled E c (Finset.Iio c) c.val q

def DegreeZeroWeightsBounded (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ ν : Fin n → ℤ, (∑ a, ν a = 0) → weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (L : ℤ)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def binomialDiagonalSubring (E : GLOps n K V) : Subring (Module.End K V) :=
  Subring.closure {u | ∃ a k, u = binomE E a k}

def OperatorsShiftWeightsByRoots (E : GLOps n K V) : Prop :=
  ∀ a b ν, ∀ x ∈ weightSp E ν, E a b x ∈ weightSp E (ν + rootW a b)

def WeightsBounded (E : GLOps n K V) : Prop :=
  ∃ m : ℕ, ∀ ν, weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (m : ℤ)

def WeightProjectionsIntegralBinomial (E : GLOps n K V) : Prop :=
  ∃ Θ : (Fin n → ℤ) → Module.End K V, (∀ μ, Θ μ ∈ binomialDiagonalSubring E) ∧
    ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0

def IsotypicComponentsSpanModule (E : GLOps n K V) : Prop := (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def TrivialIsotypicIsInvariant (E : GLOps n K V) : Prop :=
  ∀ x ∈ isoSub E 0, x ∈ weightSp E 0 ∧ ∀ a b : Fin n, a < b → E a b x = 0

def NontrivialIsotypicWeightZeroKilled (E : GLOps n K V) : Prop :=
  ∀ (P π : Module.End K V), IsWtProj E 0 π → (∀ w ∈ weightSp E 0, w ∈ nMinus E → P w = 0) →
    ∀ mu, mu ≠ 0 → ∀ x ∈ isoSub E mu, P (π x) = 0

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def SatisfiesGLRelations {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def IsStableUnderOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def isotypicPartIn {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (W : Submodule K V) (mu : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}

def StableSubspaceCompleteReducibility : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V), SatisfiesGLRelations E →
    ∀ W : Submodule K V, FiniteDimensional K W → IsStableUnderOperators E W → W ≤ ⨆ mu, weightSp E mu →
      W ≤ ⨆ mu, isotypicPartIn E W mu

def HighestWeightModuleWeightBounds : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) [NeZero n] (E : GLOps n K V),
    SatisfiesGLRelations E → ∀ (mu : Fin n → ℤ) (v : V), IsHWV E mu v → ∀ u ∈ Umon E,
      u v ∈ ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

def PolynomialOperatorsGLRelations : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι), SatisfiesGLRelations (glOps R n LL S)

def MonomialsAreWeightVectors : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι),
    (∀ (m : ι × Fin n →₀ ℕ) (c : R), monomial m c ∈ weightSp (glOps R n LL S) (wtS LL S m)) ∧
    (∀ (ν : Fin n → ℤ) (x : MvPolynomial (ι × Fin n) R), x ∈ weightSp (glOps R n LL S) ν →
      ∀ m ∈ x.support, wtS LL S m = ν)

def PolynomialLocallyFinite : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (x : MvPolynomial (ι × Fin n) R), ∃ T : Submodule R (MvPolynomial (ι × Fin n) R),
      FiniteDimensional R T ∧ x ∈ T ∧ IsStableUnderOperators (glOps R n LL S) T

def DividedPowerFormulaCharZero : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (a b : Fin n) (k : ℕ), a ≠ b → divPowE (glOps R n LL S) a b k = divPow R LL S a b k

def BinomialFormulaCharZero : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (a : Fin n) (k : ℕ), binomE (glOps R n LL S) a k = binomPol R LL S a k

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def HighestWeightVectorIntegrality : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      v ∈ Nabla (O := O) E lam v

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem derivation_finset_sum_apply {σ α : Type} (s : Finset α)
    (D : α → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (F : MvPolynomial σ K) :
    (∑ l ∈ s, D l) F = ∑ l ∈ s, D l F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]


open Classical in
def glDerivation (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) :=
  ∑ l : ι, if l ∈ S then
      (if LL.vec l then (X (l, a) : MvPolynomial (ι × Fin n) K) • pderiv (l, b)
       else -((X (l, b) : MvPolynomial (ι × Fin n) K) • pderiv (l, a)))
    else 0

theorem gl_action_eq_derivation (LL : Letters ι) (S : Set ι) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K) :
    glAct K LL S a b F = glDerivation K LL S a b F := by
  unfold glAct glDerivation
  rw [LinearMap.sum_apply, derivation_finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

open Classical in
theorem gl_derivation_variable (LL : Letters ι) (S : Set ι) (a b : Fin n) (l : ι) (c : Fin n) :
    glDerivation K LL S a b (X (l, c)) =
      if l ∈ S then (if LL.vec l then (if c = b then X (l, a) else 0) else (if c = a then -X (l, b) else 0))
      else 0 := by
  unfold glDerivation
  rw [derivation_finset_sum_apply, Finset.sum_eq_single l]
  · split_ifs <;> simp_all [pderiv_X, Pi.single_apply]
  · intro l' _ hl'
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hl']
  · simp

theorem gl_derivation_lie_bracket (LL : Letters ι) (S : Set ι) (a b c d : Fin n) :
    ⁅glDerivation K LL S a b, glDerivation K LL S c d⁆ =
      (if b = c then glDerivation K LL S a d else 0) - (if d = a then glDerivation K LL S c b else 0) := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨l, e⟩
  rw [Derivation.commutator_apply]
  by_cases hl : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = d <;> by_cases h4 : e = b <;>
        subst_vars <;> simp_all [gl_derivation_variable] <;> grind
    · simp only [gl_derivation_variable, hl, hv, if_true, apply_ite (glDerivation K LL S a b), apply_ite (glDerivation K LL S c d),
        map_zero, map_neg, Derivation.coe_sub, Pi.sub_apply]
      by_cases h1 : b = c <;> by_cases h2 : d = a <;> by_cases h3 : e = c <;> by_cases h4 : e = a <;>
        subst_vars <;> simp_all [gl_derivation_variable]
  · by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [gl_derivation_variable, hl, h1, h2]

end Formalism.MainNotions.G.GLWeightTheory
end
end
