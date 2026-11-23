module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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

noncomputable section

open scoped TensorProduct
open Module

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

def IsForm (LL : Type) {Ks WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    (WK : Submodule Ks WL) : Prop :=
  ∃ (n : ℕ) (b : Fin n → WL), (∀ i, b i ∈ WK) ∧ LinearIndependent Ks b ∧
    Submodule.span Ks (Set.range b) = WK ∧ LinearIndependent LL b ∧ Submodule.span LL (Set.range b) = ⊤

section

variable {Ks LL WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
  {WK : Submodule Ks WL}
  (O : Type) {K K'' : Type} [CommRing O] [Field K] [Algebra Ks K] [Field K''] [Algebra O K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm]

def IsExt (emb : LL →+* K'') (eF : Fm ≃ₗ[K] K ⊗[Ks] WK) (e : WL →ₛₗ[emb] K'' ⊗[O] Fm) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → LL) (f : ι → WK),
    e (∑ k, a k • (f k : WL)) = ∑ k, emb (a k) ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f k)

def CarriesBases {emb : LL →+* K''} (e : WL →ₛₗ[emb] K'' ⊗[O] Fm) : Prop :=
  ∀ (ι : Type) (b : Basis ι LL WL), ∃ b'' : Basis ι K'' (K'' ⊗[O] Fm), ∀ i, b'' i = e (b i)

end

def SemilinearExtension : Prop :=
  ∀ (Ks LL WL : Type) [Field Ks] [Field LL] [Algebra Ks LL]
    [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL), IsForm LL WK →
  ∀ (O K K'' : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
    [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
    (emb : LL →+* K''), emb.comp (algebraMap Ks LL) = (algebraMap K K'').comp (algebraMap Ks K) →
  ∀ (Fm : Type) [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
    (eF : Fm ≃ₗ[K] K ⊗[Ks] WK),
    (∃! e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e) ∧
    (∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e → CarriesBases O e) ∧
    (∀ (a : Ks) (m : Fm),
      emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m))

theorem IsExt.apply_coe {Ks LL WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    {WK : Submodule Ks WL} {O K K'' : Type} [CommRing O] [Field K] [Algebra Ks K] [Field K''] [Algebra O K'']
    {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm]
    {emb : LL →+* K''} {eF : Fm ≃ₗ[K] K ⊗[Ks] WK} {e : WL →ₛₗ[emb] K'' ⊗[O] Fm} (h : IsExt O emb eF e) (f : WK) :
    e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
  simpa using h Unit (fun _ => 1) (fun _ => f)

end GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
end
end

section

open Module

namespace GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula

def gaussBinom (q m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun j => Nat.casesOn j 1 fun _ => 0)
    (fun m b j => Nat.casesOn j 1 fun j => b (j + 1) + q ^ (m - j) * b j) m

open Module in
@[simp] theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right (q m : ℕ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m 0 = 1 := by
  cases m <;> rfl

@[simp] theorem gaussBinom_zero_succ (q j : ℕ) : gaussBinom q 0 (j + 1) = 0 := rfl

theorem gaussBinom_succ_succ (q m j : ℕ) :
    gaussBinom q (m + 1) (j + 1) = gaussBinom q m (j + 1) + q ^ (m - j) * gaussBinom q m j := rfl

open Module in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero (q : ℕ) :
    ∀ m j : ℕ, m < j → _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rfl
  | succ m ih =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, ih (j + 1) (by omega), ih j (by omega)]
    simp

def SubspaceCount : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (j : ℕ),
    Nat.card {L : Submodule k V // finrank k L = j} = gaussBinom (Nat.card k) (finrank k V) j

end GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula
end
