module

public import Formalism.LocalToGlobal.Columns.Bundle001
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.GlobalTheory.Bundle001
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
public import Formalism.LocalToGlobal.Columns.AdjointFrobeniusPreservesRamified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.Bundle002
public import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq

@[expose] public section

section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
  (b : Basis ι K V) (P : V →ₗ⋆[K] V →ₗ[K] K)

theorem isSesq_formAt : IsSesq (formAt b P) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [formAt, map_add (f := _), Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  · simp only [formAt, map_add (f := _), Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
  · simp only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  · simp only [formAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem gramOf_formAt [DecidableEq ι] (v : InfinitePlace K) :
    gramOf b (formAt b P v) = Matrix.of fun i j => v.embedding (P (b i) (b j)) := by
  ext i j
  simp only [gramOf, Matrix.of_apply, formAt, Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i' _ hi
    simp [Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem posAt_formAt [DecidableEq ι] (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef) :
    PosAt b (formAt b P) := fun v => by rw [gramOf_formAt]; exact hpos v

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [DecidableEq ι]

theorem formH_spec (hpos : ∀ v : InfinitePlace K, (Matrix.of fun i j => v.embedding (P (b i) (b j))).PosDef)
    (L : Submodule (𝓞 K) V) :
    FrameOK (ofFormB b L (formAt b P)) ∧
    (∀ v (x y : V), Formalism.HermitianLatticesTheory.majAt (ofFormB b L (formAt b P)).b (ofFormB b L (formAt b P)).X v x y = formAt b P v x y) ∧
    (∀ v (x : V), Formalism.HermitianLatticesTheory.normAt (ofFormB b L (formAt b P)).b (ofFormB b L (formAt b P)).X v x =
      Real.sqrt (formAt b P v x x).re) :=
  of_form_spec K V ι b L (formAt b P) (isSesq_formAt b P) (posAt_formAt b P hpos)

end Forms

theorem isLattice_ne_bot {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Nontrivial V] {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) : L ≠ ⊥ := by
  intro h
  letI := hL
  have h2 := Submodule.IsFullLattice.span_eq_top (A := K) (M := L)
  rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at h2
  exact bot_ne_top h2

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

end Val

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

theorem brz_colLat_one_lattice : Submodule.IsLattice K (colLat (1 : GL (Fin n) K)) := by
  have e : colLat (1 : GL (Fin n) K) = stdLat K n := by
    ext x
    rw [lc_mem_colLat_one]
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  rw [e]
  exact stdLat_lattice

end Std

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV

section L3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_localization_of_smul_mem'₂ (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) {s : 𝓞 E}
    (hs : s ∉ P.asIdeal) {w : Sp E n} (h : s • w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  obtain ⟨s', hs', h'⟩ := (mem_locP P N _).1 h
  refine (mem_locP P N w).2 ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs' hs, ?_⟩
  rwa [mul_smul]

theorem frame_exists (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsFullLattice E N) :
    ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) := by
  obtain ⟨β, hβN, hβI⟩ := exists_locBasis P hN
  refine ⟨β.equivFun.symm, fun z => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [mem_localization_standardLattice]
    intro i
    have := hβI _ h i
    rwa [Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self] at this
  · rw [mem_localization_standardLattice] at h
    rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, hrs⟩ := h i
    apply mem_localization_of_smul_mem'₂ P N hs
    have e : s • (z i • β i) = r • β i := by
      rw [← algebraMap_smul E s, ← algebraMap_smul E r, smul_smul, hrs]
    rw [e]
    exact Submodule.smul_mem _ r (hβN i)

end L3

section Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Mat

section Unit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Unit

section Bwd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Bwd

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

end Cong

end DetChrL

end Formalism.L2.Col
end
end
