module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle203
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PdPBotPos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle174
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem divided_power_xi_zero : A.dxi0 0 = 1 :=
  Subtype.ext (by simp [PAlg.dxi0, dpw])

theorem divided_power_xi_mul (i j : ℕ) :
    A.dxi0 i * A.dxi0 j = (((i + j).choose i : ℕ) : A.Acr0) * A.dxi0 (i + j) := by
  apply GlobalTheory.CompanionTheory.FilMul.divided_power_xi_mul <;> assumption

def spanFrom (r : ℕ) : Submodule A.W A.Acr0 :=
  Submodule.span A.W {z : A.Acr0 | ∃ k, r ≤ k ∧ z = A.dxi0 k}

theorem divided_power_xi_mem_span_from {r k : ℕ} (h : r ≤ k) : A.dxi0 k ∈ spanFrom A r :=
  Submodule.subset_span ⟨k, h, rfl⟩

theorem natCast_mul_mem (r : ℕ) (n : ℕ) {z : A.Acr0} (hz : z ∈ spanFrom A r) :
    (n : A.Acr0) * z ∈ spanFrom A r := by
  rw [← nsmul_eq_mul]
  exact (spanFrom A r).toAddSubmonoid.nsmul_mem hz n

theorem mul_mem_spanFrom (r : ℕ) {a b : A.Acr0} (ha : a ∈ spanFrom A 0) (hb : b ∈ spanFrom A r) :
    a * b ∈ spanFrom A r := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rw [divided_power_xi_mul]
      exact natCast_mul_mem A r _ (divided_power_xi_mem_span_from A (by omega))
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem mem_spanFrom_zero (z : A.Acr0) : z ∈ spanFrom A 0 := by
  obtain ⟨y, hy⟩ := z
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact divided_power_xi_mem_span_from A (Nat.zero_le k)
  | algebraMap x =>
    have h := Submodule.smul_mem (spanFrom A 0) x (divided_power_xi_mem_span_from A (le_refl 0))
    rw [divided_power_xi_zero] at h
    convert h using 1
    exact Subtype.ext (by simp [Algebra.smul_def])
  | add x y hx' hy' hx hy => exact add_mem hx hy
  | mul x y hx' hy' hx hy => exact mul_mem_spanFrom A 0 hx hy

theorem mem_crystalline_filtration_iff_span {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0) :
    z ∈ A.Fil0 r ↔ z ∈ Submodule.span A.W {z : A.Acr0 | ∃ k, r ≤ k ∧ z = A.dxi0 k} := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact mul_mem_spanFrom A r (mem_spanFrom_zero A c) hx
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hx

end GlobalTheory.CompanionTheory.PerfFil
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.FrameEx

theorem dividedPowerFiltration_dividedPowersBot (O : Type) [CommRing O] {n : ℕ} (hn : n ≠ 0) :
    pdP (dividedPowersBot O) n = ⊥ := by
  apply GlobalTheory.CompanionTheory.BcLoc.dividedPowerFiltration_dividedPowersBot' <;> assumption

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem inU_of_SS {l s : ℕ} {W : X.Opens} (T : Thick (LL q)) (h : SS q l s W T) : InU W T := by
  obtain ⟨-, V, hV, hT⟩ := h
  rw [Set.mem_singleton_iff.1 hV] at hT
  exact hT

end GlobalTheory.CompanionTheory.GrForm.FrameEx

namespace GlobalTheory.CompanionTheory.GrForm


open FrameEx in
theorem stFrame : StFrame := by
  intro O _ l s hb X q W d c u hu
  letI := (strV q W).toAlgebra
  obtain ⟨c', e, hTF, he1, het, hev⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := O) (I := ⊥) (dividedPowersBot O) l s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  have good := GlobalTheory.T.chart_is_good c'
  have hQ : ∀ T, SS q l s W T → InU W T := inU_of_SS
  have hD : SS q l s W c'.D := ⟨hTF, W, rfl, c'.inV⟩
  obtain ⟨hpow, hgr⟩ := GlobalTheory.T.chart_divided_powers_graded_constant c' good (SS q l s W) hQ hD
  have hval : ∀ (T : Thick (LL q)) (h : InU W T) (σ : c'.D ⟶ T) (f : Γ(X, W)),
      Ideal.Quotient.mk T.J (σ.φ (e (1 ⊗ₜ f))) = ev T h f := by
    intro T h σ f
    rw [ev_nat σ c'.inV h f, hev f]
    rfl
  have hσ : ∀ T : (SS q l s W).FullSubcategory, ∃ σ : c'.D ⟶ T.obj, ∀ i, σ.φ (c'.t i) = u i T.obj := by
    intro T
    have hT := hQ _ T.property
    obtain ⟨σ₀⟩ := good.1 T.obj hT
    obtain ⟨σ, h1, -⟩ := good.2 T.obj σ₀ (fun i => u i T.obj - σ₀.φ (c'.t i)) (fun i => by
      refine Ideal.Quotient.eq.1 ?_
      rw [hu i T.obj hT, ← het i, hval T.obj hT σ₀])
    exact ⟨σ, fun i => by simpa using h1 i⟩
  choose σ hσ using hσ
  let θ : Γ(X, W) ≃+* (sP (SS q l s W)).A.obj (c'.frame good (SS q l s W) hQ hD).D :=
    ((Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv).trans e
  have hθ : ∀ f, θ f = e (1 ⊗ₜ f) := fun f => rfl
  refine ⟨c'.frame good (SS q l s W) hQ hD, fun T => ObjectProperty.homMk (σ T), θ, hgr, ?_, ?_, ?_, ?_⟩
  · intro n hn
    change c'.D.pdPow ((n : ℤ).toNat) = ⊥
    rw [Int.toNat_natCast, hpow, dividedPowerFiltration_dividedPowersBot O hn, Ideal.map_bot]
  · intro i T s s'
    change (s'.hom.φ (c'.t i) - s.hom.φ (c'.t i) : T.obj.B) = s'.hom.φ (θ (c.t i)) - s.hom.φ (θ (c.t i))
    rw [hθ, het]
  · intro i T
    change (σ T).φ (θ (c.t i)) = u i T.obj
    rw [hθ, het, hσ]
  · intro T h f
    exact hval T.obj h (σ T) f

end GlobalTheory.CompanionTheory.GrForm
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def capR (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (u + ((r : ℂ) - 1) / 2)

def capS (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (u + ((s : ℂ) - 1) / 2)

end GlobalTheory.CompanionTheory.CTFin

end
end

section

open NumberField GlobalTheory.CuspRep Polynomial Finset

namespace GlobalTheory.CompanionTheory.CapelliTrace

theorem mem_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

theorem prod_X_sub {n : ℕ} (s : Finset (Fin n)) :
    (∏ l ∈ s, (X - C ((l : ℕ) : ℂ))).natDegree = s.card ∧ (∏ l ∈ s, (X - C ((l : ℕ) : ℂ))).Monic := by
  refine ⟨?_, monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _⟩
  rw [natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _, Finset.sum_congr rfl fun l _ => natDegree_X_sub_C _]
  simp

theorem trace_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ) (M : Fin n → Fin n → A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet M u ∈ S) : ∑ i, M i i ∈ S := by
  obtain ⟨Rm, hR⟩ := GlobalTheory.qdet_top_three_orders A n M
  refine mem_of_dual S _ fun f hf => ?_
  have f1 : f 1 = 0 := hf 1 S.one_mem
  set Q : ℂ[X] := ∑ i, C (f (M i i)) * ∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ)) +
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (f (M i i * M j j - M j i * M i j)) *
      ∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ)) +
    ∑ d ∈ range (n - 2), C (f (Rm d)) * X ^ d with hQ
  have hQ0 : Q = 0 := Polynomial.funext fun u => by
    have h1 := hf _ (h u)
    rw [hR u] at h1

    simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, f1, mul_zero, zero_add] at h1
    simp only [hQ, eval_add, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, eval_pow, eval_zero]
    rw [← h1]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  have hc := congrArg (fun p : ℂ[X] => p.coeff (n - 1)) hQ0
  simp only [hQ, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_zero] at hc
  have t1 : ∀ i : Fin n, (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 1 := fun i => by
    obtain ⟨hd, hm⟩ := prod_X_sub (univ.erase i)
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hd
    rw [← hd]; exact hm.coeff_natDegree
  have t2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j),
      (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0 := fun i j hj => by
    have hij : i < j := (mem_filter.1 hj).2
    have hj' : (j : ℕ) < n := j.2
    have hi' : (i : ℕ) < j := hij
    obtain ⟨hd, -⟩ := prod_X_sub ((univ.erase i).erase j)
    rw [card_erase_of_mem (mem_erase.2 ⟨hij.ne', mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin] at hd
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have t3 : ∀ d ∈ range (n - 2), ((X : ℂ[X]) ^ d).coeff (n - 1) = 0 := fun d hd => by
    rw [coeff_X_pow, if_neg]
    have := mem_range.1 hd
    omega
  have e3 : ∑ d ∈ range (n - 2), f (Rm d) * ((X : ℂ[X]) ^ d).coeff (n - 1) = 0 :=
    Finset.sum_eq_zero fun d hd => by rw [t3 d hd, mul_zero]
  have e2 : ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), f (M i i * M j j - M j i * M i j) *
      (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => by rw [t2 i j hj, mul_zero]
  have e1 : ∑ i : Fin n, f (M i i) * (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = ∑ i, f (M i i) :=
    Finset.sum_congr rfl fun i _ => by rw [t1 i, mul_one]
  rw [e1, e2, e3, add_zero, add_zero] at hc

  rw [map_sum]
  exact hc

end GlobalTheory.CompanionTheory.CapelliTrace

namespace GlobalTheory.CompanionTheory.CapelliTrace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
open Classical in
theorem atEmb_one (τ : E →+* ℂ) : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
  unfold atEmb; split_ifs <;> simp

theorem Eop_add_conj (τ : E →+* ℂ) (i j : Fin a) :
    Eop τ i j + Eop (ComplexEmbedding.conjugate τ) i j = lieS E a i j (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  module

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (2 : Cinf E) := by
  classical
  funext w
  simp only [atEmb_one, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_boole]
  have h := InfinitePlace.card_filter_mk_eq w
  have h2 : InfinitePlace.mult w = 2 := by
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
  have h3 : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ) =
      Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w := by
    ext τ; simp [eq_comm]
  rw [h3, h, h2]
  simp

end GlobalTheory.CompanionTheory.CapelliTrace

namespace GlobalTheory.CompanionTheory.CapelliTrace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem sum_Eop (i j : Fin a) : ∑ τ : E →+* ℂ, Eop τ i j = lieS E a i j 1 := by
  set X := ∑ τ : E →+* ℂ, Eop τ i j
  have hc : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i j = X :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate E)) fun τ => Eop τ i j
  have h2 : (2 : ℂ) • X = (2 : ℂ) • lieS E a i j 1 := by
    rw [two_smul, two_smul]
    nth_rewrite 2 [← hc]

    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conj τ i j, ← map_sum, sum_atEmb_one,
    show (2 : Cinf E) = 1 + 1 from one_add_one_eq_two.symm, map_add]
  exact smul_right_injective _ two_ne_zero h2

theorem lie_oneL_eq : lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i i]
  have e : oneL E a = ∑ i : Fin a, toL (Matrix.single i i (1 : Cinf E)) := by
    funext k l
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) k l = (∑ i : Fin a, Matrix.single i i (1 : Cinf E)) k l
    rw [Matrix.sum_apply]
    by_cases h : k = l
    · subst h; simp [Matrix.single_apply]
    · rw [Matrix.one_apply_ne h]
      exact (Finset.sum_eq_zero fun c _ => by
        rw [Matrix.single_apply, if_neg fun hc => h (hc.1.symm.trans hc.2)]).symm

  rw [e, map_sum]
  rfl

theorem lie_oneL_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    lie E a (oneL E a) ∈ Zalg E a := by
  intro E _ _ _ a
  rw [lie_oneL_eq]
  refine Subalgebra.sum_mem _ fun τ _ => trace_mem (Zalg E a) a (Eop τ) fun u => ?_
  have h : cap (a := a) τ (u - ((a : ℂ) - 1) / 2) ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, _, rfl⟩
  rwa [cap, sub_add_cancel] at h

end GlobalTheory.CompanionTheory.CapelliTrace
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.EmbUniq

variable {l : ℕ} [Fact l.Prime]

theorem norm_coe_algHom {K L : FinExt l} (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have a := minpoly.algHom_eq (L.1.val.comp τ) (RingHom.injective (L.1.val.comp τ : ↥K.1 →+* Om l)) x
  have b := minpoly.algHom_eq K.1.val (RingHom.injective (K.1.val : ↥K.1 →+* Om l)) x
  have c : minpoly ℚ_[l] ((τ x : ↥L.1) : Om l) = minpoly ℚ_[l] (x : Om l) := a.trans b.symm
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, c]

theorem norm_le_one_of_isIntegral {x : Om l} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Om l)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Om l))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

variable {E : Type} [Field E] [NumberField E]

theorem continuous_withVal (w : HeightOneSpectrum (𝓞 E)) (f : E →+* Om l)
    (h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1) (y : E) (hy0 : y ≠ 0) (hy : ‖f y‖ < 1) :
    Continuous (f.comp (WithVal.equiv (w.valuation E)).toRingHom) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hy
  let x0 : WithVal (w.valuation E) := WithVal.toVal _ (y ^ n)
  have hx0' : x0 ≠ 0 := by
    intro h
    exact pow_ne_zero n hy0 ((WithVal.equiv (w.valuation E)).symm.map_eq_zero_iff.1 h)
  have h0 : Valued.v.restrict x0 ≠ 0 := by simp [hx0']
  filter_upwards [Valued.mem_nhds_zero.2 ⟨Units.mk0 _ h0, subset_rfl⟩] with z hz
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
  have hz' : w.valuation E (WithVal.equiv (w.valuation E) z) < w.valuation E (y ^ n) := hz
  have hv : 0 < w.valuation E (y ^ n) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero n hy0))
  have hu : w.valuation E (WithVal.equiv (w.valuation E) z / y ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hv).2 hz'.le
  have h2 := h1 _ hu
  have hp : 0 < ‖f y‖ ^ n := pow_pos (norm_pos_iff.2 ((map_ne_zero f).2 hy0)) n
  rw [map_div₀, map_pow, norm_div, norm_pow, div_le_one₀ hp] at h2
  rw [dist_zero_right]
  exact lt_of_le_of_lt h2 hn

def toKw {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) : E →+* ↥Bw.Kw.1 :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E

theorem existsUnique_continuous_induced : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      ∃! j : {j : w.adicCompletion E →+* Qbar l // Continuous j},
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj LL' τ'
  let g : E →+* ↥LL'.1 := (τ' : ↥Bw.Kw.1 →+* ↥LL'.1).comp (toKw Bw)
  let f : E →+* Om l := (algebraMap ↥LL'.1 (Om l)).comp g
  have hfn : ∀ x, ‖f x‖ = ‖Bw.j (algebraMap E Ω x)‖ := fun x => norm_coe_algHom τ' (toKw Bw x)
  have hlt : ∀ y : 𝓞 E, ‖f (y : E)‖ < 1 ↔ y ∈ w.asIdeal := fun y => by
    rw [hfn, ← hj.valuation_lt_one_iff]
    exact hA y
  have hint : ∀ y : 𝓞 E, ‖f (y : E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral (by
      convert map_isIntegral_int f (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hd : 1 ≤ ‖f ((d : 𝓞 E) : E)‖ := not_lt.1 fun hl => d.2 ((hlt _).1 hl)
    have h2 : ‖f x‖ * ‖f ((d : 𝓞 E) : E)‖ = ‖f (n : E)‖ := by
      rw [← norm_mul, ← map_mul]
      exact congrArg (fun z => ‖f z‖) h
    have h3 := hint n
    nlinarith [norm_nonneg (f x)]
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hc := continuous_withVal w f h1 (y : E) (by simpa using hy0) ((hlt y).2 hyw)
  have hcg : Continuous (g.comp (WithVal.equiv (w.valuation E)).toRingHom) :=
    Topology.IsInducing.subtypeVal.continuous_iff.2 hc
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : CompleteSpace ↥LL'.1 := FiniteDimensional.complete ℚ_[l] ↥LL'.1
  let ext : w.adicCompletion E →+* ↥LL'.1 :=
    (UniformSpace.Completion.extensionHom _ hcg).comp (HeightOneSpectrum.adicCompletion.equiv E w).toRingHom
  have hextc : Continuous ext := UniformSpace.Completion.continuous_extension.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w)
  have hext : ∀ x : E, ext (algebraMap E _ x) = g x := fun k =>
    UniformSpace.Completion.extensionHom_coe _ hcg (WithVal.toVal _ k)
  have hval : ∀ x : E, ((ext (algebraMap E _ x) : ↥LL'.1) : Om l) = f x := fun x =>
    congrArg (Subtype.val) (hext x)
  refine ⟨⟨(algebraMap ↥LL'.1 (Om l)).comp ext, continuous_subtype_val.comp hextc⟩, fun x => (hval x), ?_⟩
  rintro ⟨j', hj'c⟩ hj'
  refine Subtype.ext (DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hj'c
    (continuous_subtype_val.comp hextc) (funext fun x => ?_)))
  exact (hj' x).trans (hval x).symm

end GlobalTheory.CompanionTheory.EmbUniq
end
end
