module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle002
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

section

noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct

namespace UpperTheory.V.Pa

def Til (O O' R : Type) [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R] : Type :=
  PowerSeries (O' ⊗[O] R)

namespace Til

variable (O O' R : Type) [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R]

instance : CommRing (Til O O' R) := inferInstanceAs (CommRing (PowerSeries (O' ⊗[O] R)))

instance : Algebra O' (Til O O' R) := inferInstanceAs (Algebra O' (PowerSeries (O' ⊗[O] R)))

def C : O' ⊗[O] R →+* Til O O' R := PowerSeries.C

def ι : R →+* Til O O' R := (C O O' R).comp (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom

instance algR : Algebra R (Til O O' R) := (ι O O' R).toAlgebra

theorem algebraMap_eq : algebraMap R (Til O O' R) = ι O O' R := rfl

def s : Til O O' R := PowerSeries.X

def coeff (k : ℕ) (a : Til O O' R) : O' ⊗[O] R := PowerSeries.coeff k (show PowerSeries (O' ⊗[O] R) from a)

theorem ι_algebraMap (a : O) : ι O O' R (algebraMap O R a) = algebraMap O' (Til O O' R) (algebraMap O O' a) := by
  have h : algebraMap O' (Til O O' R) (algebraMap O O' a) = C O O' R (algebraMap O' (O' ⊗[O] R) (algebraMap O O' a)) :=
    PowerSeries.algebraMap_apply
  rw [h, ← IsScalarTower.algebraMap_apply]
  exact congrArg (C O O' R) ((Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).commutes a)

variable {O R} {R' : Type} [CommRing R'] [Algebra O R']

def map (f : R →ₐ[O] R') : Til O O' R →ₐ[O'] Til O O' R' :=
  PowerSeries.mapAlgHom (Algebra.TensorProduct.map (AlgHom.id O' O') f)

theorem map_ι (f : R →ₐ[O] R') (a : R) : map O' f (ι O O' R a) = ι O O' R' (f a) := by
  show PowerSeries.map _ (PowerSeries.C _) = PowerSeries.C _
  rw [PowerSeries.map_C]
  rfl

theorem map_s (f : R →ₐ[O] R') : map O' f (s O O' R) = s O O' R' := PowerSeries.map_X _

def act {M : Type} [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M] (m : M) :
    O' ⊗[O] R →ₗ[O] O' ⊗[O] M :=
  TensorProduct.map LinearMap.id ((LinearMap.toSpanSingleton R M m).restrictScalars O)

end Til

def lamEmb (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (D : ℕ) : abelian₂ O Empty D →+* abelian₂ O' Unit D :=
  (MvPowerSeries.rename (Sum.map Empty.elim id : Empty ⊕ Fin D → Unit ⊕ Fin D) : abelian₂ O' Empty D →ₐ[O'] abelian₂ O' Unit D).toRingHom.comp
    (MvPowerSeries.map (algebraMap O O'))

variable {l : ℕ} [Fact l.Prime]

def RBC {F : GFrame l} {O O' : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O']
    [Algebra ℤ_[l] O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] {n : ℕ} (r : Resid F O n) (r' : Resid F O' n) : Prop :=
  (∀ i, r'.chib i = pushCh (ResidueField.map (algebraMap O O')) (r.chib i)) ∧
    (∀ v i, r'.psib v i = pushCh (ResidueField.map (algebraMap O O')) (r.psib v i)) ∧
    ∀ v i, r'.th v i = pushCh (algebraMap O O') (r.th v i)

structure BaseRel {L : Loc} {G0 : Glob l L} {O O' : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CommRing O']
    [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] {n : ℕ} {r : Resid G0.frame O n} {r' : Resid G0.frame O' n}
    {B : Type} [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] {u : Pair r B} {u' : Pair r' (Til O O' B)}
    {J : Ideal B} {J' : Ideal (Til O O' B)} {D : ℕ} (b : TWBase u J Empty D) (b' : TWBase u' J' Unit D)
    (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) where
  wt : b'.wt = ⟨b.wt.v, b.wt.i, b.wt.γ, fun k => algebraMap O O' (b.wt.c k)⟩
  lam : ∀ a, b'.lam (τ a) = Til.map O' b.lam a
  μ : Til O O' B ⊗[B] b.M ≃ₗ[Til O O' B] b'.M

end UpperTheory.V.Pa
end
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.chain_tens :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [IsLocalRing O] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing B] [Algebra O B] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal (O' ⊗[O] B)) (E : Fin h → Ideal (O' ⊗[O] B)), (∀ i, (P i).IsPrime ∧ (P i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal (O' ⊗[O] B)) (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) → ∃ Q : Ideal (O' ⊗[O] B), Q.IsPrime ∧ Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = q ∧ Q ≤ P := by
  intro O O' B _ _ _ _ _ _ _ _ _ h p e hp he
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  let φ : B ⊗[O] O' ≃ₐ[B] O' ⊗[O] B := Algebra.TensorProduct.commRight O B O'
  haveI : Module.Finite B (O' ⊗[O] B) := Module.Finite.equiv φ.toLinearEquiv
  haveI : Module.Free B (O' ⊗[O] B) := Module.Free.of_equiv φ.toLinearEquiv
  haveI : Module.FaithfullyFlat O O' := inferInstance
  haveI : Module.FaithfullyFlat B (O' ⊗[O] B) :=
    Module.FaithfullyFlat.of_linearEquiv B (B ⊗[O] O') φ.symm.toLinearEquiv
  haveI : FaithfulSMul B (O' ⊗[O] B) := inferInstance
  exact UpperTheory.V.Pa.BC.chain_lift B (O' ⊗[O] B) h p e hp he
end
