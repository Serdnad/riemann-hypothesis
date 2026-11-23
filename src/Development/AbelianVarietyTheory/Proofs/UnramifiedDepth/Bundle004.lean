module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Perfectoid.Untilt
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReciprocityTheory.DualLattices.Bundle003
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import ReciprocityTheory.DualLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoeffFunctional

open MvPolynomial

variable {σ K L : Type} [Field K] [Field L] [Algebra K L]

def coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ μ ∈ P.support, monomial μ (φ (P.coeff μ))

theorem coeff_coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) (μ : σ →₀ ℕ) :
    (coeffMap φ P).coeff μ = φ (P.coeff μ) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

theorem coeffMap_add (φ : L →ₗ[K] K) (P Q : MvPolynomial σ L) :
    coeffMap φ (P + Q) = coeffMap φ P + coeffMap φ Q := by
  ext μ
  simp [coeff_coeffMap]

theorem coeffMap_zero (φ : L →ₗ[K] K) : coeffMap φ (0 : MvPolynomial σ L) = 0 := by
  ext μ
  simp [coeff_coeffMap]

theorem coeffMap_map_mul_C (φ : L →ₗ[K] K) (A : MvPolynomial σ K) (c : L) :
    coeffMap φ (MvPolynomial.C c * MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.C (φ c) * A := by
  ext μ
  rw [coeff_coeffMap, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm c, ← Algebra.smul_def,
    map_smul, smul_eq_mul, mul_comm]

theorem coeffMap_comm (φ : L →ₗ[K] K) (f : MvPolynomial σ L →ₗ[L] MvPolynomial σ L)
    (g : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (h : ∀ A, f (MvPolynomial.map (algebraMap K L) A) = MvPolynomial.map (algebraMap K L) (g A))
    (P : MvPolynomial σ L) : coeffMap φ (f P) = g (coeffMap φ P) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), coeffMap_add, coeffMap_add, map_add (f := _), hp, hq]
  | monomial μ c =>
    have e : (monomial μ c : MvPolynomial σ L) =
        MvPolynomial.C c * MvPolynomial.map (algebraMap K L) (monomial μ 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, coeffMap_map_mul_C, C_mul', map_smul, h, ← C_mul', coeffMap_map_mul_C, C_mul', C_mul',
      map_smul]

variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem lap_one_map (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (A : MvPolynomial (Letter T r n) K) :
    lap r n L 1 τ τ' a a' (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (lap r n K 1 τ τ' a a' A) := by

  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  by_cases hb : b = b'
  · subst hb
    simp [pderiv_map]
  · simp [Matrix.one_apply_ne hb]

theorem rowShift_map (s : T) (i i' : Fin (r s)) (t : K) (A : MvPolynomial (Letter T r n) K) :
    rowShift r n L s i i' (algebraMap K L t) (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (rowShift r n K s i i' t A) := by
  induction A using MvPolynomial.induction_on with
  | C c => simp [rowShift]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p l hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

theorem mem_HHa_of_coeff_functional :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (K C : Type) [Field K] [Field C] [Algebra K C] (φ : C →ₗ[K] K) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C) (Q : MvPolynomial (Letter T r n) K), (∀ μ, Q.coeff μ = φ (P.coeff μ)) → P ∈ HHa r n C cc isX a → Q ∈ HHa r n K cc isX a := by
  intro T r n K L _ _ _ φ cc isX a P Q hQ hP
  have hQ' : Q = coeffMap φ P := by
    ext μ
    rw [hQ, coeff_coeffMap]
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [hQ', ← coeffMap_comm φ _ _ (lap_one_map r n τ (cc τ) b b') P, h1 τ hτ b b', coeffMap_zero]
  · intro s i i' hi t
    have := coeffMap_comm φ (rowShift r n L s i i' (algebraMap K L t)).toLinearMap
      (rowShift r n K s i i' t).toLinearMap (rowShift_map r n s i i' t) P
    simp only [AlgHom.toLinearMap_apply] at this
    rw [hQ', ← this, h2 s i i' hi]
  · intro m hm
    refine h3 m ?_
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hQ, h0, map_zero])

end GlobalTheory.CoeffFunctional
end
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem vV_algebraMap_nonneg_dvr (T : CDVR) (x : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr x) := by
  unfold vV valV
  rw [neg_nonneg]
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
    (IsDiscreteValuationRing.maximalIdeal T.V) x
  by_cases h0 : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
      (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr x) = 0
  · rw [h0, WithZero.log_zero]
  · rw [WithZero.log_le_iff_le_exp h0]
    simpa using h1

theorem nval_eq_of_extension :
    ∀ (T : CDVR) (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l ≠ 0 → v (l : C) = 1 → ∀ (ι : T.Fr →+* C), (∀ x : T.Fr, x ≠ 0 → v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((l : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)) → (∀ x : T.V, ((0 : ℝ) : WithTop ℝ) ≤ v (ι (algebraMap T.V T.Fr x))) ∧ ∀ x : T.Fr, nval T.V (vV T.V ((l : ℕ) : T.Fr)).toNat x = (WithBot.some (v (ι x)) : WithBot (WithTop ℝ)) := by
  intro T C _ v l hl hv ι hι
  have hvl : 0 ≤ vV T.V ((l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg_dvr T (l : T.V)
    rwa [map_natCast] at h
  have hcast : (((vV T.V ((l : ℕ) : T.Fr)).toNat : ℕ) : ℝ) = ((vV T.V ((l : ℕ) : T.Fr) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hvl]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : algebraMap T.V T.Fr x ≠ 0 := fun h =>
        hx ((IsFractionRing.injective T.V T.Fr) (by rw [h, map_zero]))
      rw [hι _ hx']
      have h1 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr x) : ℝ) := by
        exact_mod_cast vV_algebraMap_nonneg_dvr T x
      have h2 : (0 : ℝ) ≤ (vV T.V ((l : ℕ) : T.Fr) : ℝ) := by exact_mod_cast hvl
      exact WithTop.coe_le_coe.mpr (div_nonneg h1 h2)
  · unfold nval
    split_ifs with hx
    · subst hx
      simp only [map_zero, AddValuation.map_zero]
      rfl
    · rw [hι x hx, hcast]
      rfl

end GlobalTheory
end

section

open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.FlowProgramme

lemma sum_shift (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : Finset ℕ) :
    ∑ a : ZMod d, ∑ i ∈ s, x (a - i) i = ∑ a, ∑ i ∈ s, x a i := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)

lemma duality (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (x : ZMod d → ℕ → ℝ)
    (hx : ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a)) :
    ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i ≤ ∑ a, X a ∧
      ∀ i₀ : ℕ, ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i ≤ ((l : ℝ) ^ i₀)⁻¹ * ∑ a, X a := by
  obtain ⟨h0, h1, h2⟩ := hx
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) ≤ l := by linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun a _ => h2 a
  rw [Finset.sum_add_distrib, sum_shift] at hs
  have hT : 0 ≤ ∑ a, ∑ i ∈ Finset.range d, x a i :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => h0 a i
  constructor
  · have : (l : ℝ) * ∑ a, ∑ i ∈ Finset.range d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h : x a i = 0
      · simp [h]
      · have hi : i ≠ 0 := by
          rintro rfl
          exact absurd (h1 a 0 h).1 (by decide)
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi) (h0 a i)
    linarith
  · intro i₀
    have hp : (0 : ℝ) < (l : ℝ) ^ i₀ := by positivity
    rw [le_inv_mul_iff₀ hp]
    have : (l : ℝ) ^ i₀ * ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i
        ≤ ∑ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      calc ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i₀ * x a i
          ≤ ∑ i ∈ Finset.Ico i₀ d, (l : ℝ) ^ i * x a i :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 (Finset.mem_Ico.1 hi).1) (h0 a i)
        _ ≤ _ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
              mul_nonneg (by positivity) (h0 a i)
            intro i hi
            exact Finset.mem_range.2 (Finset.mem_Ico.1 hi).2
    linarith

lemma cyclic_nonneg (l : ℝ) (d : ℕ) [NeZero d] (X y : ZMod d → ℝ) (hl : 2 ≤ l)
    (hX : ∀ a b, X a ≤ l * X b) (hy : ∀ a, l * y a + y (a - 1) = X a) (a : ZMod d) :
    0 ≤ y a := by
  obtain ⟨a₀, h₀⟩ := Finite.exists_min y
  obtain ⟨a₁, h₁⟩ := Finite.exists_max y
  refine le_trans ?_ (h₀ a)
  have e0 := hy a₀
  have e1 := hy a₁
  have f0 := h₁ (a₀ - 1)
  have f1 := h₀ (a₁ - 1)
  have g := hX a₁ a₀
  have k : l * y (a₀ - 1) ≤ l * y a₁ := mul_le_mul_of_nonneg_left f0 (by linarith)
  have k2 : 0 ≤ (l * l - 1) * y a₀ := by rw [← e0] at g; nlinarith
  have k3 : 0 < l * l - 1 := by nlinarith
  exact (mul_nonneg_iff_of_pos_left k3).1 k2

lemma cyclic_solvable (l : ℝ) (d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) :
    ∃ y : ZMod d → ℝ, ∀ a, l * y a + y (a - 1) = X a := by
  let T : (ZMod d → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun y a => l * y a + y (a - 1)
      map_add' := fun y z => by ext a; simp; ring
      map_smul' := fun c y => by ext a; simp; ring }
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have hy' : ∀ a, l * y a + y (a - 1) = 0 := fun a => congrFun hy a
    ext a
    have h1 := cyclic_nonneg l d (fun _ => 0) y hl (by simp) hy' a
    have h2 := cyclic_nonneg l d (fun _ => 0) (fun a => - y a) hl (by simp)
      (fun a => by have := hy' a; linarith) a
    simp only [Pi.zero_apply]
    linarith
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.1 hinj X
  exact ⟨y, fun a => congrFun hy a⟩

lemma balanced (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (hd : 2 ≤ d)
    (hX : ∀ a b, X a ≤ l * X b) :
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧
      ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i = ∑ a, X a := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨y, hy⟩ := cyclic_solvable l d X hl'
  have hpos := cyclic_nonneg l d X y hl' hX hy
  have h1 : 1 ∈ Finset.range d := Finset.mem_range.2 (by omega)
  refine ⟨fun a i => if i = 1 then y a else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a i
    dsimp only
    split_ifs
    · exact hpos a
    · exact le_rfl
  · intro a i h
    dsimp only at h
    split_ifs at h with hi
    · subst hi
      exact ⟨odd_one, by omega⟩
    · exact absurd rfl h
  · intro a
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', h1, if_true, pow_one, Nat.cast_one]
    exact (hy a).le
  · simp only [Finset.sum_ite_eq', h1, if_true]
    have : ∑ a, y (a - 1) = ∑ a, y a := Equiv.sum_comp (Equiv.subRight (1 : ZMod d)) y
    rw [← Finset.sum_congr rfl fun a _ => hy a, Finset.sum_add_distrib, this, ← Finset.mul_sum]
    ring

end GlobalTheory.FlowProgramme
end

section

open Ideal

namespace GlobalTheory.PadicComplexHost

variable (p : ℕ) [hp : Fact p.Prime]

theorem valuation_coe_eq_norm (x : ℂ_[p]) : ((Valued.v x : NNReal) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl),
    Valuation.embedding_restrict]

theorem norm_p : ‖((p : ℕ) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← valuation_coe_eq_norm, PadicComplex.valuation_p]; simp

theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem mem_iff_norm (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [← valuation_coe_eq_norm]
  change Valued.v x ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

theorem not_isUnit_p : ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := by
  intro h
  have h1 := (PadicComplexInt.integers p).one_of_isUnit h
  rw [map_natCast] at h1
  have h2 := valuation_coe_eq_norm p ((p : ℕ) : ℂ_[p])
  rw [h1, norm_p] at h2
  have := inv_p_lt_one p
  rw [← h2] at this
  simp at this

theorem smodEq_iff (n : ℕ) (x y : 𝓞_ℂ_[p]) :
    x ≡ y [SMOD ((span {((p : ℕ) : 𝓞_ℂ_[p])}) ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton, (PadicComplexInt.integers p).dvd_iff_le, map_pow, map_natCast,
    ← norm_p, ← norm_pow, ← valuation_coe_eq_norm, ← valuation_coe_eq_norm, NNReal.coe_le_coe]
  rfl

theorem tendsto_inv_p_pow :
    Filter.Tendsto (fun n : ℕ => (p : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_p_lt_one p)

theorem isHausdorff : IsHausdorff (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun x hx => ?_⟩
  have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := fun n => by
    simpa using (smodEq_iff p n x 0).1 (hx n)
  have h0 : ‖(x : ℂ_[p])‖ ≤ 0 :=
    ge_of_tendsto (tendsto_inv_p_pow p) (Filter.Eventually.of_forall h)
  exact Subtype.ext (norm_le_zero_iff.1 h0)

theorem isPrecomplete : IsPrecomplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun f hf => ?_⟩
  have h : ∀ {m n : ℕ}, m ≤ n → ‖(f m : ℂ_[p]) - (f n : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ m :=
    fun hmn => (smodEq_iff p _ _ _).1 (hf hmn)
  have hc : CauchySeq fun n => (f n : ℂ_[p]) := by
    refine cauchySeq_of_le_geometric (p : ℝ)⁻¹ 1 (inv_p_lt_one p) fun n => ?_
    rw [dist_eq_norm, one_mul]
    exact h (Nat.le_succ n)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hm : ∀ m : ℕ, ‖(f m : ℂ_[p]) - L‖ ≤ (p : ℝ)⁻¹ ^ m := fun m =>
    le_of_tendsto ((tendsto_const_nhds.sub hL).norm)
      ((Filter.eventually_ge_atTop m).mono fun n hn => h hn)
  have hLO : L ∈ 𝓞_ℂ_[p] := by
    rw [mem_iff_norm]
    exact le_of_tendsto hL.norm
      (Filter.Eventually.of_forall fun n => (mem_iff_norm p _).1 (f n).2)
  exact ⟨⟨L, hLO⟩, fun n => (smodEq_iff p n _ _).2 (hm n)⟩

theorem isAdicComplete : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  { isHausdorff p, isPrecomplete p with }

theorem main : ∀ (p : ℕ) [Fact p.Prime], ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
    (ε : PreTilt 𝓞_ℂ_[p] p), (Valued.v : Valuation ℂ_[p] NNReal).Integers 𝓞_ℂ_[p] ∧
      IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p := by
  intro p _
  have h1 : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := ⟨not_isUnit_p p⟩
  have h2 := isAdicComplete p
  obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) ℂ_[p] Valued.v 𝓞_ℂ_[p]
    (PadicComplexInt.integers p)
  exact ⟨h1, h2, ε, PadicComplexInt.integers p, hε⟩

end GlobalTheory.PadicComplexHost
end

section

open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory

theorem exists_linearIndependent_sumElim_of_finrank_eq {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {n₀ n' : ℕ} (hV : Module.finrank k V = n₀ + n')
    (v : Fin n₀ → V) (hv : LinearIndependent k v) :
    ∃ w : Fin n' → V, LinearIndependent k (Sum.elim v w) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range v))
  have h1 := Submodule.finrank_add_eq_of_isCompl hQ
  rw [finrank_span_eq_card hv, Fintype.card_fin, hV] at h1
  have h2 : Module.finrank k Q = n' := by omega
  let b := Module.finBasisOfFinrankEq k Q h2
  refine ⟨fun j => (b j : V), hv.sum_type (b.linearIndependent.map' Q.subtype Q.ker_subtype) ?_⟩
  refine hQ.disjoint.mono_right ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact (b j).2

end GlobalTheory
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_pth_root_of_derivation_zero : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : K), (∀ D : Derivation ℤ K K, D f = 0) → ∃ h : K, h ^ p = f := by
  first | exact @GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero | exact GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero | (intros; apply GlobalTheory.exists_pow_eq_of_forall_derivation_eq_zero <;> assumption)
end
