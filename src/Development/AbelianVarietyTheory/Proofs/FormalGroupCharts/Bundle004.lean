module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Mathlib.RingTheory.Regular.RegularSequence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Finiteness.Ideal

@[expose] public section

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by
  first | exact @GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem | exact GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem | (intros; apply GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem <;> assumption)
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

namespace NilpotentEval

variable {A : Type*} [CommRing A]

theorem pow_mul_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (n : ℕ) : J ^ (N * n) ≤ K ^ n := by
  rw [pow_mul]
  exact Ideal.pow_right_mono h n

theorem isHausdorff_of_pow_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) [IsHausdorff K A] :
    IsHausdorff J A := by
  refine ⟨fun x hx => IsHausdorff.haus' (I := K) x fun n => ?_⟩
  have := hx (N * n)
  rw [SModEq.zero] at this ⊢
  simp only [smul_eq_mul, Ideal.mul_top] at this ⊢
  exact pow_mul_le h n this

theorem isPrecomplete_of_pow_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (hKJ : K ≤ J)
    [IsPrecomplete K A] : IsPrecomplete J A := by
  have h' : J ^ (N + 1) ≤ K := (Ideal.pow_le_pow_right N.le_succ).trans h
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := K) (fun n => f ((N + 1) * n)) fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact pow_mul_le h' m (hf (Nat.mul_le_mul_left _ hmn))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  refine ⟨L, fun n => ?_⟩
  have h1 := hf (m := n) (n := (N + 1) * n) (Nat.le_mul_of_pos_left n N.succ_pos)
  have h2 := Ideal.pow_right_mono hKJ n (hL n)
  simpa using add_mem h1 h2

theorem exists_pow_sup_span_le (K : Ideal A) {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ j, ∃ M : ℕ, a j ^ M ∈ K) : ∃ N : ℕ, (K ⊔ Ideal.span (Set.range a)) ^ N ≤ K := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Ideal.span (Set.range a) ^ N ≤ K :=
    Ideal.exists_pow_le_of_le_radical_of_fg
      (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ha j))
      (Submodule.fg_span (Set.finite_range a))
  refine ⟨N, ?_⟩
  rw [← Ideal.mk_ker (I := K), ← Ideal.map_eq_bot_iff_le_ker] at hN
  conv_rhs => rw [← Ideal.mk_ker (I := K)]
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, Ideal.map_sup, Ideal.map_quotient_self,
    bot_sup_eq, ← Ideal.map_pow]
  exact hN

end NilpotentEval


open NilpotentEval in
theorem mvPowerSeries_eval_of_pow_mem : ∀ (A : Type) [CommRing A] (K : Ideal A) (σ : Type) [Finite σ] (a : σ → A), (∀ j, ∃ M : ℕ, a j ^ M ∈ K) → (IsAdicComplete K A → ∀ (R : Type) [CommRing R] [Algebra R A], ∃ ψ : MvPowerSeries σ R →ₐ[R] A, ∀ j, ψ (MvPowerSeries.X j) = a j) ∧ (IsHausdorff K A → ∀ (T : Type) [CommRing T] (ψ ψ' : MvPowerSeries σ T →+* A), (∀ t, ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)) → (∀ j, ψ (MvPowerSeries.X j) = a j) → (∀ j, ψ' (MvPowerSeries.X j) = a j) → ψ = ψ') := by
  intro A _ K σ _ a ha
  obtain ⟨N, hN⟩ := NilpotentEval.exists_pow_sup_span_le K a ha
  have hmem : ∀ j, a j ∈ K ⊔ Ideal.span (Set.range a) := fun j =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨fun hK R _ _ => ?_, fun hK T _ ψ ψ' hC hψ hψ' => ?_⟩
  · haveI : IsAdicComplete (K ⊔ Ideal.span (Set.range a)) A :=
      { toIsHausdorff := NilpotentEval.isHausdorff_of_pow_le hN
        toIsPrecomplete := NilpotentEval.isPrecomplete_of_pow_le hN le_sup_left }
    exact ⟨mvEvalAdic R _ a hmem, mvEvalAdic_X _ a hmem⟩
  · haveI := NilpotentEval.isHausdorff_of_pow_le hN
    letI : Algebra T A := (ψ.comp MvPowerSeries.C).toAlgebra
    let φ : MvPowerSeries σ T →ₐ[T] A := { ψ with commutes' := fun _ => rfl }
    let φ' : MvPowerSeries σ T →ₐ[T] A := { ψ' with commutes' := fun t => (hC t).symm }
    have : φ = φ' := mvPowerSeries_algHom_ext_of_isHausdorff (K ⊔ Ideal.span (Set.range a))
      (fun j => by change ψ _ ∈ _; rw [hψ]; exact hmem j)
      (fun j => (hψ j).trans (hψ' j).symm)
    exact RingHom.ext fun g => DFunLike.congr_fun this g

end GlobalTheory
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.module_flat_mvPowerSeries_of_isNoetherianRing : ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (σ : Type), Module.Flat T (MvPowerSeries σ T) := by
  first | exact @GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | exact GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing | (intros; apply GlobalTheory.FiniteHeight.flat_mvPowerSeries_of_isNoetherianRing <;> assumption)
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.flat_quotient_weakly_regular : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by
  first | exact @GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre | exact GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre | (intros; apply GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d m n : ℕ}

def CZ (a : Fin m → Pt k n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

theorem CZ.hasSubst {a : Fin m → Pt k n d} (ha : CZ a) : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem ev_add {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f + g) = ev a f + ev a g :=
  subst_add ha.hasSubst f g

theorem ev_mul {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f * g) = ev a f * ev a g :=
  subst_mul ha.hasSubst f g

def evHom {a : Fin m → Pt k n d} (ha : CZ a) : PS k m d →+* PS k n d :=
  (substAlgHom ha.hasSubst).toRingHom

theorem evHom_apply {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : evHom ha f = ev a f := by
  simp [evHom, ev]

theorem ev_sum {a : Fin m → Pt k n d} (ha : CZ a) {ι : Type} (s : Finset ι) (f : ι → PS k m d) :
    ev a (∑ x ∈ s, f x) = ∑ x ∈ s, ev a (f x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← evHom_apply ha, map_sum]

theorem ev_C {a : Fin m → Pt k n d} (ha : CZ a) (c : k) : ev a (C c : PS k m d) = C c := by
  rw [← evHom_apply ha]
  show substAlgHom ha.hasSubst (algebraMap k _ c) = _
  rw [AlgHom.commutes]; rfl

theorem ev_X {a : Fin m → Pt k n d} (ha : CZ a) (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS k m d) = a j i :=
  subst_X ha.hasSubst (j, i)

theorem ev_zero' {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  simp only [← evHom_apply ha, map_zero]

theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : CZ a) {f : PS k m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 :=
  constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf

theorem CZ.ev {a : Fin m → Pt k n d} (ha : CZ a) {l : ℕ} {b : Fin l → Pt k m d} (hb : CZ b) :
    CZ (fun j i => ev a (b j i)) := fun j i => constantCoeff_ev ha (hb j i)

theorem ev_ev {l : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) {b : Fin l → Pt k m d} (hb : CZ b) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  unfold ev
  rw [subst_comp_subst_apply hb.hasSubst ha.hasSubst]

theorem ev_pt (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by
  unfold ev pt
  exact congrFun subst_self f

theorem CZ.pt : CZ (fun j => pt k (n := n) d j) := fun j i => by
  show constantCoeff (X (j, i) : PS k n d) = 0
  simp

theorem pderiv_ev {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d) :
    pderiv (R := k) v (ev a f) =
      ∑ p : Fin m × Fin d, ev a (pderiv (R := k) p f) * pderiv (R := k) v (a p.1 p.2) := by
  unfold ev
  exact pderiv_subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f v

theorem ev_zeroFam (f : PS k m d) : ev (fun _ _ => (0 : PS k n d)) f = C (constantCoeff f) := by
  classical
  have hz : CZ (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  ext e
  unfold ev
  rw [coeff_subst hz.hasSubst, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp) (zero_pow hp), map_zero, smul_zero]

end GlobalTheory.FormalLog
end
end
