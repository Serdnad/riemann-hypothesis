module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle080
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PlusPolynomialInclusion
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Module.PID
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGeneratedByQuasiReflectionsAndWitt
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumSmulMemOfSumZpowSmulMem
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarmonicColumnOperatorEndMemOfUnitaryStable
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

noncomputable section

open Polynomial TensorProduct Matrix Formalism.UG

namespace GlobalTheory.ClassParam

section Cyclic

theorem charpoly_dvd_of_aeval {K : Type} [Field K] {r : ℕ} (g : Matrix (Fin r) (Fin r) K)
    (hs : g.charpoly.Separable) (q : K[X]) (hq : aeval g q = 0) : g.charpoly ∣ q := by
  apply GlobalTheory.CompanionTheory.Centraliser.charpoly_dvd_of_aeval_eq_zero <;> assumption

def krylov {A : Type} [CommRing A] {r : ℕ} (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    Matrix (Fin r) (Fin r) A := Matrix.of fun i j => ((g ^ (j : ℕ)) *ᵥ v) i

theorem krylov_map {A B : Type} [CommRing A] [CommRing B] {r : ℕ} (f : A →+* B)
    (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    (krylov g v).map f = krylov (g.map f) (f ∘ v) := by
  ext i j
  simp only [krylov, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

theorem exists_cyclic_field {K : Type} [Field K] {r : ℕ} (g : Matrix (Fin r) (Fin r) K)
    (hs : g.charpoly.Separable) : ∃ v, (krylov g v).det ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  refine ⟨(Module.AEval'.of (Matrix.toLin' g)).symm x, fun h => ?_⟩
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (w j)
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [← hw]
    ext i

    simp [q, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  have hd := charpoly_dvd_of_aeval g hs q hq
  have hdeg : q.degree < g.charpoly.degree := by
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => lt_of_le_of_lt (degree_monomial_le _ _) ?_
    exact_mod_cast j.2
  have hq0 := eq_zero_of_dvd_of_degree_lt hd hdeg
  apply hw0
  ext j
  have := congrArg (fun p => p.coeff j) hq0
  simpa only [q, Polynomial.finsetSum_coeff, coeff_monomial_apply, Fin.val_inj,
    Fintype.sum_ite_eq', coeff_zero, Pi.zero_apply] using this

theorem exists_cyclic {A : Type} [CommRing A] [IsArtinianRing A] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) A) (hs : g.charpoly.Separable) :
    ∃ v, IsUnit (krylov g v).det := by
  classical
  have hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

end Cyclic

section Transfer

variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S]
  [Algebra A B] {ι : Type} [Fintype ι] [DecidableEq ι]

end Transfer

section Forms

variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)

theorem hform_eq (J : Matrix (Fin r) (Fin r) A) (x y : Fin r → A) :
    hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (J g : Matrix (Fin r) (Fin r) A) (x y : Fin r → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ (cT σ g * J * g) x y := by
  have h2 : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [hform_eq, hform_eq, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cT,
    Matrix.dotProduct_mulVec _ (g.map σ)ᵀ, Matrix.vecMul_transpose]

theorem hform_single (J : Matrix (Fin r) (Fin r) A) (i j : Fin r) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite σ]

theorem mem_UJ_iff (J : Matrix (Fin r) (Fin r) A) (g : GL (Fin r) A) :
    g ∈ UJ σ J ↔ ∀ x y, hform σ J ((g : Matrix (Fin r) (Fin r) A) *ᵥ x)
      ((g : Matrix (Fin r) (Fin r) A) *ᵥ y) = hform σ J x y := by
  show cT σ (g : Matrix (Fin r) (Fin r) A) * J * g = J ↔ _
  constructor
  · intro h x y; rw [hform_mulVec, h]
  · intro h; ext i j
    rw [← hform_single σ (_ * J * _), ← hform_mulVec, h, hform_single]

end Forms

section Core

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}

variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}

end Core

section Concrete

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion

attribute [local instance] algLk

variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]

end Concrete

end GlobalTheory.ClassParam
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSubgroup

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def zM (c p : ℕ) (t : k) : Matrix (Fin c) (Fin c) k :=
  Matrix.of fun l i => if l.val + 1 = p ∧ i.val + 1 = p + 1 then t else 0

def hM (c p : ℕ) (u β : n → k) (t : k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  fromBlocks 1 (ExchangeSupport.colM c (p + 1) β) (ExchangeSupport.rowM c p u) (1 + zM c p t)

theorem zM_add (s t : k) : zM c p (s + t) = zM c p s + zM c p t := by
  ext l i
  simp only [zM, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem zM_zero : zM c p (0 : k) = 0 := by
  ext l i
  simp [zM]

theorem zM_mul (s t : k) : zM c p s * zM c p t = 0 := by
  ext l i
  simp only [Matrix.mul_apply, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [Fintype n] [DecidableEq n] in
theorem col_mul_zM (β : n → k) (t : k) : ExchangeSupport.colM c (p + 1) β * zM c p t = 0 := by
  ext r i
  simp only [Matrix.mul_apply, ExchangeSupport.colM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [Fintype n] [DecidableEq n] in
theorem zM_mul_row (u : n → k) (t : k) : zM c p t * ExchangeSupport.rowM c p u = 0 := by
  ext l s
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [DecidableEq n] in
theorem row_mul_col (u β : n → k) :
    ExchangeSupport.rowM c p u * ExchangeSupport.colM c (p + 1) β = zM c p (u ⬝ᵥ β) := by
  ext l i
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, ExchangeSupport.colM, zM, Matrix.of_apply]
  by_cases hl : l.val + 1 = p <;> by_cases hi : i.val + 1 = p + 1 <;> simp [hl, hi, dotProduct]

omit [Fintype n] [DecidableEq n] in
theorem row_add (u w : n → k) : ExchangeSupport.rowM c p (u + w) =
    ExchangeSupport.rowM c p u + ExchangeSupport.rowM c p w := by
  ext l s
  simp only [ExchangeSupport.rowM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem col_add (u w : n → k) : ExchangeSupport.colM c p (u + w) =
    ExchangeSupport.colM c p u + ExchangeSupport.colM c p w := by
  ext r i
  simp only [ExchangeSupport.colM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem row_zero : ExchangeSupport.rowM c p (0 : n → k) = 0 := by
  ext l s
  simp [ExchangeSupport.rowM]

omit [Fintype n] [DecidableEq n] in
theorem col_zero : ExchangeSupport.colM c p (0 : n → k) = 0 := by
  ext r i
  simp [ExchangeSupport.colM]

theorem hM_mul (u β u' β' : n → k) (t t' : k) :
    hM c p u β t * hM c p u' β' t' = hM c p (u + u') (β + β') (t + t' + u ⬝ᵥ β') := by
  simp only [hM, Matrix.fromBlocks_multiply]
  congr 1
  · rw [ExchangeSupport.colM_mul_rowM, Matrix.one_mul, add_zero]
  · rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, col_mul_zM, add_zero, col_add]
    abel
  · rw [Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, zM_mul_row, add_zero, row_add]
  · rw [row_mul_col]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, zM_mul, zM_add]
    abel

omit [Fintype n] in
theorem hM_zero : hM c p (0 : n → k) 0 0 = 1 := by
  rw [hM, row_zero, col_zero, zM_zero, add_zero, Matrix.fromBlocks_one]

theorem rowE_eq (u : n → k) : (rowE c p u).val = hM c p u 0 0 := by
  rw [ExchangeSupport.rowE_val, hM, col_zero, zM_zero, add_zero]

theorem colE_eq (β : n → k) : (colE c (p + 1) β).val = hM c p 0 β 0 := by
  rw [ExchangeSupport.colE_val, hM, row_zero, zM_zero, add_zero]

theorem cenM_eq (t : k) : cenM n c p t = hM c p 0 0 t := by
  rw [hM, row_zero, col_zero]
  rfl

theorem prod_eq (u β : n → k) (t : k) :
    (rowE c p u).val * (colE c (p + 1) β).val * cenM n c p t = hM c p u β (u ⬝ᵥ β + t) := by
  rw [rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul]
  simp only [add_zero, zero_add, dotProduct_zero]

def Heisenberg₂ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | ∃ (u β : n → k) (t : k), g.val = hM c p u β t}
  one_mem' := ⟨0, 0, 0, hM_zero.symm⟩
  mul_mem' := by
    rintro g h ⟨u, β, t, hg⟩ ⟨u', β', t', hh⟩
    exact ⟨_, _, _, by rw [Units.val_mul, hg, hh, hM_mul]⟩
  inv_mem' := by
    rintro g ⟨u, β, t, hg⟩
    refine ⟨-u, -β, u ⬝ᵥ β - t, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hg, hM_mul, ← hM_zero (p := p)]
    simp

theorem mem_N_of_val {g : GL (n ⊕ Fin c) k} {β : n → k} {t : k} (hg : g.val = hM c p 0 β t) :
    g ∈ N k n c p := by
  show g ∈ Subgroup.closure {g | InN p g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [hg, hM, row_zero]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₁₂, ExchangeSupport.colM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.add_apply, zM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp [Matrix.one_apply]

private theorem eMat_mem_N_succ (u : n → k) : rowE c p u ∈ N k n c (p + 1) := by
  show rowE c p u ∈ Subgroup.closure {g | InN (p + 1) g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [ExchangeSupport.rowE_val]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₁, ExchangeSupport.rowM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp [Matrix.one_apply]

theorem heis_le : Heisenberg₂ k n c p ≤ NFJ k n c p := by
  rintro g ⟨u, β, t, hg⟩
  have hinv : rowE c p u * rowE c p (-u) = 1 := by
    rw [← ExchangeSupport.rowE_add, add_neg_cancel, ExchangeSupport.rowE_zero]
  have hsplit : g = rowE c p u * (rowE c p (-u) * g) := by
    rw [← mul_assoc, hinv, one_mul]
  have hrest : rowE c p (-u) * g ∈ N k n c p := by
    refine mem_N_of_val (β := β) (t := t - u ⬝ᵥ β) ?_
    rw [Units.val_mul, hg, rowE_eq, hM_mul]
    simp only [neg_add_cancel, zero_add, neg_dotProduct]
    ring_nf
  rw [hsplit]
  exact Subgroup.mul_mem _ (le_sup_right (a := N k n c p) (eMat_mem_N_succ u))
    (le_sup_left (b := N k n c (p + 1)) hrest)

end

theorem heisenberg_subgroup : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∃ H : Subgroup (GL (n ⊕ Fin c) k), H ≤ NFJ k n c ρ ∧ ∀ g, g ∈ H ↔ ∃ (u β : n → k) (t : k), g.val = (rowE c ρ u).val * (colE c (ρ + 1) β).val * cenM n c ρ t) ∧ ∀ u β₀ : n → k, (rowE c ρ u * colE c (ρ + 1) β₀).val = cenM n c ρ (u ⬝ᵥ β₀) * (colE c (ρ + 1) β₀ * rowE c ρ u).val := by
  intro k _ n _ _ c ρ _ _
  refine ⟨⟨Heisenberg₂ k n c ρ, heis_le, fun g => ?_⟩, fun u β₀ => ?_⟩
  · constructor
    · rintro ⟨u, β, t, hg⟩
      refine ⟨u, β, t - u ⬝ᵥ β, ?_⟩
      rw [prod_eq, hg]
      congr 1
      ring
    · rintro ⟨u, β, t, hg⟩
      exact ⟨u, β, u ⬝ᵥ β + t, by rw [hg, prod_eq]⟩
  · rw [Units.val_mul, Units.val_mul, rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul, hM_mul]
    simp only [add_zero, zero_add, dotProduct_zero, zero_dotProduct]

end GlobalTheory.RootEx.HeisenbergSubgroup
end
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.unitaryCharacter_kills_unitaryTransvections : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  first | exact @GlobalTheory.UTrans.TvKill.char_tvGen | exact GlobalTheory.UTrans.TvKill.char_tvGen | (intros; apply GlobalTheory.UTrans.TvKill.char_tvGen <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.unitary_generated_by_quasiReflections_and_witt : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → (∀ γ, GlobalTheory.UTrans.IsU σ G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, GlobalTheory.UTrans.hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧ γ = (l.map fun p => GlobalTheory.UTrans.tv σ G p.1 ((p.2 - 1) / GlobalTheory.UTrans.hf σ G p.1 p.1)).prod) ∧ ∀ x z : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G z z = GlobalTheory.UTrans.hf σ G x x → ∃ γ, GlobalTheory.UTrans.IsU σ G γ ∧ γ *ᵥ z = x := by
  first | exact @GlobalTheory.UTrans.ReflChar0.gen_and_witt | exact GlobalTheory.UTrans.ReflChar0.gen_and_witt | (intros; apply GlobalTheory.UTrans.ReflChar0.gen_and_witt <;> assumption)
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by
  first | exact @GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | exact GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | (intros; apply GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply <;> assumption)
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

theorem _root_.GlobalTheory.T.nonempty_equiv_of_smoothTrace_eq_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → π.IsIrreducible → π'.IsIrreducible → (∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace π μ f = smoothTrace π' μ f) → Nonempty (π.Equiv π') := by
  first | exact @GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq | exact GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq | (intros; apply GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.rootExchange_support_and_fourier_relation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → (fun u : n → k => l (σ (rowE c p u) v)) ∈ SB (n → k) ∧ (∀ u β : n → k, l (σ (rowE c p u) (σ (colE c (p + 1) β) v)) = (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v)) ∧ ∀ β : n → k, exUp ν p σ l (σ (colE c (p + 1) β) v) = ∫ u : n → k, (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)) ∧ (IsNEquiv ψ (p + 1) σ l → (fun β : n → k => l (σ (colE c (p + 1) β) v)) ∈ SB (n → k) ∧ ∀ u β : n → k, l (σ (colE c (p + 1) β) (σ (rowE c p u) v)) = (ψ (-(u ⬝ᵥ β)) : ℂ) * l (σ (colE c (p + 1) β) v)) := by
  first | exact @GlobalTheory.RootEx.ExchangeSupport.exchange_support | exact GlobalTheory.RootEx.ExchangeSupport.exchange_support | (intros; apply GlobalTheory.RootEx.ExchangeSupport.exchange_support <;> assumption)
end

section

noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.SatakeBound

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsBorelSph (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ) : Prop :=
  (∀ g : GL (Fin n) k, ∀ x ∈ KO k (Fin n), φ (g * x) = φ g) ∧
    ∀ b ∈ borel k (Fin n), ∀ t : Fin n → kˣ,
      (∀ i, (b : Matrix (Fin n) (Fin n) k) i i = t i) → φ b = ∏ i, γ i ^ ord k (t i)

def HasBoundedSums (φ : GL (Fin n) k → ℂ) : Prop :=
  ∀ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)), (∀ x ∈ KO k (Fin n), ∀ c ∈ S, x • c ∈ S) →
    ‖∑ c ∈ S, φ c.out‖ ≤ S.card

theorem isBorelSph_one : IsBorelSph k (n := n) (fun _ => 1) fun _ => 1 :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩

end GlobalTheory.SatakeBound
end
end

section

open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.harmonicColumnOperatorEnd_mem_of_unitary_stable : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {p q n : ℕ} (W : Submodule ℂ (GlobalTheory.Harm.Poly ℂ ι p q (Fin n))), (∀ g : ι → GL (Fin n) ℂ, (∀ t, (g t : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ w ∈ W, GlobalTheory.Harm.colActHom g w ∈ W) → ∀ (t : ι) (k l : Fin n), ∀ w ∈ W, GlobalTheory.Harm.colLie ℂ p q t k l w ∈ W := by
  first | exact @GlobalTheory.Harm.colLie_mem_of_unitary_stable | exact GlobalTheory.Harm.colLie_mem_of_unitary_stable | (intros; apply GlobalTheory.Harm.colLie_mem_of_unitary_stable <;> assumption)
end
