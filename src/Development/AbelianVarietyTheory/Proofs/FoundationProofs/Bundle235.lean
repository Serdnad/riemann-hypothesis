module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle220
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.InertParity

variable {D : D7}

def Ev (D : D7) (n : ℕ) : Prop := ∀ q : ℕ, q.Prime → InertQ D q → Even (n.factorization q)

def hlf (D : D7) (n : ℕ) : ℕ := ∑ q ∈ n.primeFactors.filter (InertQ D), n.factorization q / 2

def sgn (D : D7) (n : ℕ) : ℂ := (-1) ^ hlf D n

def idx (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : ℕ :=
  Nat.card (stdL D n ⧸ Submodule.comap (stdL D n).subtype L)

def scal (D : D7) (N N' : ℕ) (b : D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' :=
  GlobalTheory.RatEqui.mulV D (b • (1 : Matrix (Fin N') (Fin N') D.host.E)) 1

theorem scal_apply {N N' : ℕ} (b : D.host.E) (z : VC D N N') (τ i j) :
    scal D N N' b z τ i j = embT D τ b * z τ i j := by
  have e : (b • (1 : Matrix (Fin N') (Fin N') D.host.E)).map (embT D τ) =
      embT D τ b • (1 : Matrix (Fin N') (Fin N') ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [scal, GlobalTheory.RatEqui.mulV_apply, e, Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem idx_eq_relIndex {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    idx D L = L.toAddSubgroup.relIndex (stdL D n).toAddSubgroup := rfl

theorem idx_std (n : ℕ) : idx D (stdL D n) = 1 := by
  rw [idx_eq_relIndex, AddSubgroup.relIndex_self]

theorem hlf_eq_sum {n : ℕ} {s : Finset ℕ} (hs : n.primeFactors ⊆ s) :
    hlf D n = ∑ q ∈ s.filter (InertQ D), n.factorization q / 2 := by
  refine Finset.sum_subset (Finset.filter_subset_filter _ hs) fun q hq hq' => ?_
  have : q ∉ n.factorization.support := fun h =>
    hq' (Finset.mem_filter.2 ⟨by simpa using h, (Finset.mem_filter.1 hq).2⟩)
  rw [Finsupp.notMem_support_iff.1 this, Nat.zero_div]

theorem Ev.one : Ev D 1 := fun q _ _ => by simp

theorem sgn_one : sgn D 1 = 1 := by simp [sgn, hlf]

theorem sgn_mul_self (n : ℕ) : sgn D n * sgn D n = 1 := by
  rw [sgn, ← mul_pow]; simp

theorem sgn_pow_even (n : ℕ) {k : ℕ} (hk : Even k) : sgn D n ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_add, ← mul_pow, sgn_mul_self, one_pow]

theorem Ev.mul {a b : ℕ} (ha : Ev D a) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Ev D (a * b) := fun q hq hi => by
  rw [Nat.factorization_mul ha0 hb0]
  exact (ha q hq hi).add (hb q hq hi)

theorem Ev.of_mul {a b : ℕ} (hab : Ev D (a * b)) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Ev D a :=
  fun q hq hi => by
    have := hab q hq hi
    rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, Nat.even_add] at this
    exact this.2 (hb q hq hi)

theorem Ev.pow {a : ℕ} (ha : Ev D a) (k : ℕ) : Ev D (a ^ k) := fun q hq hi => by
  rw [Nat.factorization_pow]
  exact (ha q hq hi).mul_left k

theorem sgn_mul {a b : ℕ} (ha : Ev D a) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    sgn D (a * b) = sgn D a * sgn D b := by
  have h : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := Nat.primeFactors_mul ha0 hb0
  rw [sgn, sgn, sgn, ← pow_add, hlf_eq_sum (n := a) (s := (a * b).primeFactors) (h ▸ Finset.subset_union_left),
    hlf_eq_sum (n := b) (s := (a * b).primeFactors) (h ▸ Finset.subset_union_right), hlf, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hi⟩ := Finset.mem_filter.1 hq
  have hp := Nat.prime_of_mem_primeFactors hq1
  obtain ⟨i, hi'⟩ := ha q hp hi
  obtain ⟨j, hj⟩ := hb q hp hi
  rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply]
  omega

theorem sgn_pow {a : ℕ} (ha : Ev D a) (ha0 : a ≠ 0) (k : ℕ) : sgn D (a ^ k) = sgn D a ^ k := by
  induction k with
  | zero => simp [sgn_one]
  | succ k ih => rw [pow_succ, sgn_mul (ha.pow k) ha (pow_ne_zero _ ha0) ha0, ih, pow_succ]

theorem sgn_congr {a b : ℕ} (h : ∀ q : ℕ, q.Prime → InertQ D q → a.factorization q = b.factorization q) :
    sgn D a = sgn D b := by
  rw [sgn, sgn, hlf_eq_sum (n := a) (s := a.primeFactors ∪ b.primeFactors) Finset.subset_union_left,
    hlf_eq_sum (n := b) (s := a.primeFactors ∪ b.primeFactors) Finset.subset_union_right]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hi⟩ := Finset.mem_filter.1 hq
  have hp : q.Prime := by
    rcases Finset.mem_union.1 hq1 with h | h <;> exact Nat.prime_of_mem_primeFactors h
  rw [h q hp hi]

theorem sgn_of_eq {n a b c k : ℕ} (h : n * a ^ k = b ^ k * c ^ k) (ha : Ev D a) (hb : Ev D b) (hc : Ev D c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) : sgn D n = sgn D b ^ k * (sgn D c * sgn D a) ^ k := by
  have h0 : b ^ k * c ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ hc0)
  have hn0 : n ≠ 0 := left_ne_zero_of_mul (h ▸ h0)
  have hn : Ev D n := Ev.of_mul (h ▸ (hb.pow k).mul (hc.pow k) (pow_ne_zero _ hb0) (pow_ne_zero _ hc0)) (ha.pow k) hn0
    (pow_ne_zero _ ha0)
  have e := congrArg (sgn D) h
  rw [sgn_mul hn (ha.pow k) hn0 (pow_ne_zero _ ha0),
    sgn_mul (hb.pow k) (hc.pow k) (pow_ne_zero _ hb0) (pow_ne_zero _ hc0), sgn_pow ha ha0, sgn_pow hb hb0,
    sgn_pow hc hc0] at e
  rw [mul_pow, ← mul_assoc, ← e, mul_assoc, ← mul_pow, sgn_mul_self, one_pow, mul_one]

end GlobalTheory.InertParity
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj.ProdLin

def CjN (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x y : ℂ) : Prop := x ∈ M ∧ y = cj M ρ x

theorem CjN.add {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {x y x' y' : ℂ} (h : CjN M ρ x x')
    (h' : CjN M ρ y y') : CjN M ρ (x + y) (x' + y') :=
  ⟨add_mem h.1 h'.1, by rw [cj_add ρ h.1 h'.1, h.2, h'.2]⟩

theorem CjN.mul {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {x y x' y' : ℂ} (h : CjN M ρ x x')
    (h' : CjN M ρ y y') : CjN M ρ (x * y) (x' * y') :=
  ⟨mul_mem h.1 h'.1, by rw [cj_mul ρ h.1 h'.1, h.2, h'.2]⟩

theorem CjN.rat (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (q : ℚ) : CjN M ρ (q : ℂ) (q : ℂ) := by
  have h : (q : ℂ) ∈ M := SubfieldClass.ratCast_mem M q
  refine ⟨h, ?_⟩
  rw [cj_mem ρ h]
  have : (⟨(q : ℂ), h⟩ : M) = (q : M) := by apply Subtype.ext; simp
  rw [this, map_ratCast]

inductive Rel {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : I → E)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : (E → ℂ) → (E → ℂ) → Prop
  | const (c c' : ℂ) : CjN M ρ c c' → Rel v M ρ (fun _ => c) (fun _ => c')
  | base (g g' : ℂ → ℂ) (L L' : E →L[ℂ] ℂ) : Differentiable ℂ g → Differentiable ℂ g' →
      (∀ n, CjN M ρ (iteratedDeriv n g 0) (iteratedDeriv n g' 0)) →
      (∀ k, CjN M ρ (L (v k)) (L' (v k))) → Rel v M ρ (fun z => g (L z)) (fun z => g' (L' z))
  | add (F F' G G' : E → ℂ) : Rel v M ρ F F' → Rel v M ρ G G' →
      Rel v M ρ (fun z => F z + G z) (fun z => F' z + G' z)
  | mul (F F' G G' : E → ℂ) : Rel v M ρ F F' → Rel v M ρ G G' →
      Rel v M ρ (fun z => F z * G z) (fun z => F' z * G' z)

variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {v : I → E}
  {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

theorem Rel.contDiff {F F' : E → ℂ} (h : Rel v M ρ F F') :
    ContDiff ℂ ⊤ F ∧ ContDiff ℂ ⊤ F' := by
  induction h with
  | const c c' _ => exact ⟨contDiff_const, contDiff_const⟩
  | base g g' L L' hg hg' _ _ => exact ⟨hg.contDiff.comp L.contDiff, hg'.contDiff.comp L'.contDiff⟩
  | add F F' G G' _ _ h1 h2 => exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩
  | mul F F' G G' _ _ h1 h2 => exact ⟨h1.1.mul h2.1, h1.2.mul h2.2⟩

theorem Rel.diff {F F' : E → ℂ} (h : Rel v M ρ F F') :
    Differentiable ℂ F ∧ Differentiable ℂ F' :=
  ⟨h.contDiff.1.differentiable (by simp), h.contDiff.2.differentiable (by simp)⟩

theorem Rel.at_zero {F F' : E → ℂ} (h : Rel v M ρ F F') : CjN M ρ (F 0) (F' 0) := by
  induction h with
  | const c c' h => exact h
  | base g g' L L' _ _ h _ => simpa using h 0
  | add F F' G G' _ _ h1 h2 => exact h1.add h2
  | mul F F' G G' _ _ h1 h2 => exact h1.mul h2

theorem fderiv_base {g : ℂ → ℂ} (hg : Differentiable ℂ g) (L : E →L[ℂ] ℂ) (w : E) :
    (fun z => fderiv ℂ (fun z => g (L z)) z w) = fun z => L w * deriv g (L z) := by
  funext z
  have := ((hg (L z)).hasDerivAt.comp_hasFDerivAt z L.hasFDerivAt).fderiv
  change fderiv ℂ (g ∘ L) z w = _
  rw [this]; simp [mul_comm]

theorem fderiv_add' {F G : E → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : E) :
    (fun z => fderiv ℂ (fun z => F z + G z) z w) = fun z => fderiv ℂ F z w + fderiv ℂ G z w := by
  funext z
  rw [fderiv_fun_add (hF z) (hG z)]; simp

theorem fderiv_mul' {F G : E → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : E) :
    (fun z => fderiv ℂ (fun z => F z * G z) z w) =
      fun z => F z * fderiv ℂ G z w + G z * fderiv ℂ F z w := by
  funext z
  rw [fderiv_fun_mul (hF z) (hG z)]; simp

theorem Rel.fderiv {F F' : E → ℂ} (h : Rel v M ρ F F') (k : I) :
    Rel v M ρ (fun z => fderiv ℂ F z (v k)) (fun z => fderiv ℂ F' z (v k)) := by
  induction h with
  | const c c' h =>
    have := Rel.const (v := v) _ _ (CjN.rat M ρ 0)
    simpa using this
  | base g g' L L' hg hg' h hL =>
    rw [fderiv_base hg, fderiv_base hg']
    refine Rel.mul _ _ _ _ (Rel.const _ _ (hL k))
      (Rel.base (deriv g) (deriv g') L L' hg.deriv hg'.deriv (fun n => ?_) hL)
    rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
    exact h (n + 1)
  | add F F' G G' hF hG h1 h2 =>
    rw [fderiv_add' hF.diff.1 hG.diff.1, fderiv_add' hF.diff.2 hG.diff.2]
    exact Rel.add _ _ _ _ h1 h2
  | mul F F' G G' hF hG h1 h2 =>
    rw [fderiv_mul' hF.diff.1 hG.diff.1, fderiv_mul' hF.diff.2 hG.diff.2]
    exact Rel.add _ _ _ _ (Rel.mul _ _ _ _ hF h2) (Rel.mul _ _ _ _ hG h1)

theorem iteratedFDeriv_step {F : E → ℂ} (hF : ContDiff ℂ ⊤ F) (n : ℕ) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℂ (n + 1) F 0 m =
      iteratedFDeriv ℂ n (fun z => fderiv ℂ F z (m (Fin.last n))) 0 (Fin.init m) := by
  rw [iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_clm_apply_const_apply (n := ⊤) (hF.fderiv_right (m := ⊤) le_top) le_top]

theorem Rel.iterated (n : ℕ) : ∀ {F F' : E → ℂ}, Rel v M ρ F F' → ∀ k : Fin n → I,
    CjN M ρ (iteratedFDeriv ℂ n F 0 fun i => v (k i)) (iteratedFDeriv ℂ n F' 0 fun i => v (k i)) := by
  induction n with
  | zero => intro F F' h k; simpa using h.at_zero
  | succ n ih =>
    intro F F' h k
    rw [iteratedFDeriv_step h.contDiff.1, iteratedFDeriv_step h.contDiff.2]
    exact ih (h.fderiv (k (Fin.last n))) (Fin.init k)

theorem Rel.prod {ι : Type} (s : Finset ι) {F F' : ι → E → ℂ} (h : ∀ i, Rel v M ρ (F i) (F' i)) :
    Rel v M ρ (fun z => ∏ i ∈ s, F i z) (fun z => ∏ i ∈ s, F' i z) := by
  induction s using Finset.induction_on with
  | empty =>
    have := Rel.const (v := v) _ _ (CjN.rat M ρ 1)
    simpa using this
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact Rel.mul _ _ _ _ (h i) ih

theorem Rel.cjF {D : D7} {N N' : ℕ} {F F' : VC D N N' → ℂ} (h : Rel (coordV D) M ρ F F') :
    CjF D M ρ F F' := by
  refine ⟨h.diff.1, h.diff.2, fun α => ?_⟩
  have h1 := (Rel.iterated _ h (fun i : Fin (Multiset.card α.toMultiset) =>
    α.toMultiset.toList.get ⟨i, by rw [Multiset.length_toList]; exact i.2⟩)).mul
      (CjN.rat M ρ (α.prod fun _ n => (n.factorial : ℚ))⁻¹)
  have h2 : (((α.prod fun _ n => (n.factorial : ℚ))⁻¹ : ℚ) : ℂ) =
      (α.prod fun _ n => (n.factorial : ℂ))⁻¹ := by
    simp [Finsupp.prod]
  rw [h2] at h1
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  simp only [div_eq_mul_inv]
  exact h1

def linF (D : D7) {N N' : ℕ} (l : VC D N N') : VC D N N' →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ∑ τ, ∑ a, ∑ c, z τ a c * l τ a c
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum, mul_assoc] }

theorem linF_apply (D : D7) {N N' : ℕ} (l z : VC D N N') :
    linF D l z = ∑ τ, ∑ a, ∑ c, z τ a c * l τ a c := rfl

theorem linF_coordV (D : D7) {N N' : ℕ} (l : VC D N N') (k : D.what₂.Tau × Fin N' × Fin N) :
    linF D l (coordV D k) = l k.1 k.2.1 k.2.2 := by
  rw [linF_apply]
  simp [coordV, ite_and]

theorem cjF_prod : ∀ (D : D7) (N N' r : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (g g' : Fin r → ℂ → ℂ) (l l' : Fin r → VC D N N'), (∀ j, Differentiable ℂ (g j)) →
    (∀ j, Differentiable ℂ (g' j)) →
    (∀ j n, coef1 (g j) n ∈ M ∧ coef1 (g' j) n = cj M ρ (coef1 (g j) n)) →
    (∀ j τ a c, l j τ a c ∈ M ∧ l' j τ a c = cj M ρ (l j τ a c)) →
    CjF D M ρ (fun z : VC D N N' => ∏ j, g j (∑ τ, ∑ a, ∑ c, z τ a c * l j τ a c))
      (fun z : VC D N N' => ∏ j, g' j (∑ τ, ∑ a, ∑ c, z τ a c * l' j τ a c)) := by
  intro D N N' r M ρ g g' l l' hg hg' hc hl
  refine Rel.cjF (Rel.prod Finset.univ fun j =>
    Rel.base (g j) (g' j) (linF D (l j)) (linF D (l' j)) (hg j) (hg' j) (fun n => ?_) fun k => ?_)
  · have h1 := CjN.mul (hc j n) (CjN.rat M ρ (n.factorial : ℚ))
    have h0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simpa only [coef1, Rat.cast_natCast, div_mul_cancel₀ _ h0] using h1
  · rw [linF_coordV, linF_coordV]; exact hl j _ _ _

end GlobalTheory.ThetaConj.ProdLin
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

theorem rationalLatticePoint_add {Λ : AddSubgroup ℂ} {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, h⟩ := hx
  obtain ⟨n, hn, h'⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have : ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [this]
  exact add_mem (nsmul_mem h n) (nsmul_mem h' m)

theorem rationalLatticePoint_neg {Λ : AddSubgroup ℂ} {x : ℂ} (hx : InRationalLattice Λ x) : InRationalLattice Λ (-x) := by
  obtain ⟨m, hm, h⟩ := hx
  exact ⟨m, hm, by rw [mul_neg]; exact neg_mem h⟩

theorem rationalLatticePoint_div_natCast {Λ : AddSubgroup ℂ} {w : ℂ} (hw : w ∈ Λ) {m : ℕ} (hm : 0 < m) : InRationalLattice Λ (w / m) := by
  refine ⟨m, hm, ?_⟩
  have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [mul_div_cancel₀ _ this]; exact hw

theorem Good.embV_nsmul {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ} (k : ℕ)
    (A : Matrix (Fin N') (Fin N) D.host.E) : embV D T (k • A) = (k : ℂ) • embV D T A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (h.embHom N N') k A

theorem Good.embV_sum {D : D7} {T : Tor D} (h : Good D T) {N N' r : ℕ} (a : Fin r → D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    embV D T (∑ j, a j • b j) = ∑ j, D.host.φ₀ (a j : D.host.E) • embV D T (b j) := by
  have := map_sum (h.embHom N N') (fun j => a j • b j) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
  exact h.embV_smul _ _

theorem Good.smul_embV_mem {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ}
    {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} {w : ℂ} (hw : w ∈ T.abelian₂)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ AddSubgroup.closure Y) :
    w • embV D T y ∈ LaS D T Y := by
  change w • h.embHom N N' y ∈ _
  induction hy using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure ⟨w, hw, x, hx, rfl⟩
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

theorem corr_lattice : ∀ (D : D7) (T T' : Tor D), Good D T → Good D T' → (∀ a : 𝓞 D.host.K, ∀ w ∈ T.abelian₂, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ T.abelian₂) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.Orthonormal D b → ∀ (S : ℂ → ℂ → Prop), (∀ t, InRationalLattice T.abelian₂ t → ∃ t', S t t') → (∀ t t₁ t₂, S t t₁ → S t t₂ → t₁ - t₂ ∈ T'.abelian₂) → (∀ t t' u u', S t t' → S u u' → S (t + u) (t' + u')) → (∀ (a : 𝓞 D.host.K) t t', S t t' → S (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t) (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t')) → (∀ (m : ℕ) t t', S t t' → (m : ℂ) * t ∈ T.abelian₂ → (m : ℂ) * t' ∈ T'.abelian₂) → ∀ (n k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < n → 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧ x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧ ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y) ∧ ∀ c c' : Fin r → ℂ, (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) → ∑ j, c j • embV D T (b j) ∈ LaS D T Y → ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
  intro D T T' hT hT' hO N N' r b hb S hex huniq hadd hmul hint n k Y hn hk hkn hC
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hS0 : S 0 0 := by
    obtain ⟨t', ht'⟩ := hex 0 ⟨1, one_pos, by simp⟩
    simpa using hmul 0 _ _ ht'
  have hneg : ∀ t t', S t t' → S (-t) (-t') := fun t t' h => by
    simpa using hmul (-1) _ _ h
  have first : ∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧
      x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧
      ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, y, hy, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hC.1 y hy
      obtain ⟨u', hu'⟩ := hex _ (rationalLatticePoint_div_natCast hw (Nat.mul_pos hn hk))
      have hnk : ((n * k : ℕ) : ℂ) * u' ∈ T'.abelian₂ := by
        refine hint _ _ _ hu' ?_
        rw [mul_div_cancel₀ _ (by push_cast; exact mul_ne_zero hn0 hk0)]; exact hw
      have e1 := hT.embV_sum (fun j => (a j : D.host.K)) b
      have e2 := hT'.embV_sum (fun j => (a j : D.host.K)) b
      rw [← ha, hT.embV_nsmul] at e1
      rw [← ha, hT'.embV_nsmul] at e2
      refine ⟨fun j => D.host.φ₀ ((a j : D.host.K) : D.host.E) * w / k,
        fun j => n * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u'),
        fun j => rationalLatticePoint_div_natCast (hO _ _ hw) hk, ?_, fun j => ?_, ?_⟩
      · have : w • embV D T y = (w / k) • ((k : ℂ) • embV D T y) := by
          rw [smul_smul, div_mul_cancel₀ _ hk0]
        rw [this, e1, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]; congr 1; ring
      · have := hmul (a j) _ _ hu'
        convert this using 1
        · push_cast; field_simp
        · field_simp
      · have : ∑ j, ((n : ℂ) * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u')) • embV D T' (b j)
            = (((n * k : ℕ) : ℂ) * u') • embV D T' y := by
          have h2 : (((n * k : ℕ) : ℂ) * u') • embV D T' y
              = ((n : ℂ) * u') • ((k : ℂ) • embV D T' y) := by
            rw [smul_smul]; congr 1; push_cast; ring
          rw [h2, e2, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]; congr 1; ring
        rw [this]
        exact AddSubgroup.subset_closure ⟨_, hnk, y, hy, rfl⟩
    | zero =>
      refine ⟨0, 0, fun j => ⟨1, one_pos, by simp⟩, by simp, fun j => by simpa using hS0, ?_⟩
      simp
    | add x y _ _ hx hy =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      obtain ⟨d, d', g1, g2, g3, g4⟩ := hy
      refine ⟨c + d, c' + d', fun j => rationalLatticePoint_add (h1 j) (g1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, g2, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_smul]
      · simp only [Pi.add_apply, add_div]; exact hadd _ _ _ _ (h3 j) (g3 j)
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; exact add_mem h4 g4
    | neg x _ hx =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      refine ⟨-c, -c', fun j => rationalLatticePoint_neg (h1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, ← Finset.sum_neg_distrib]; simp only [Pi.neg_apply, neg_smul]
      · simp only [Pi.neg_apply, neg_div]; exact hneg _ _ (h3 j)
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]; exact neg_mem h4
  refine ⟨first, fun c c' hS hc => ?_⟩
  obtain ⟨d, d', -, h2, h3, h4⟩ := first _ hc
  have hcd : c = d := by
    funext j
    rw [← hT.coordB_sum hb c j, h2, hT.coordB_sum hb]
  subst hcd
  obtain ⟨m, hm⟩ := hkn
  have key : ∀ j, (c' j - d' j) • embV D T' (b j) ∈ LaS D T' Y := fun j => by
    have h5 := nsmul_mem (huniq _ _ _ (hS j) (h3 j)) m
    have h6 := hT'.smul_embV_mem h5 (hC.2 j)
    rw [hT'.embV_nsmul, smul_smul] at h6
    convert h6 using 2
    have hm' : (n : ℂ) = k * m := by rw [hm]; push_cast; rfl
    rw [nsmul_eq_mul, ← sub_div, mul_right_comm, mul_comm (m : ℂ), ← hm', mul_div_cancel₀ _ hn0]
  have : ∑ j, c' j • embV D T' (b j)
      = ∑ j, d' j • embV D T' (b j) + ∑ j, (c' j - d' j) • embV D T' (b j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [this]
  exact add_mem h4 (sum_mem fun j _ => key j)

end GlobalTheory.ThetaConj
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_normOne_scalar_avoiding_matrix_eigenvalues : ∀ (D : D7) (n : ℕ) (γ : Matrix (Fin n) (Fin n) D.host.E), ∃ z : D.host.E, z * D.host.conj z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  first | exact @GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero | exact GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero | (intros; apply GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.compactCoverUn_hcModule_finiteDim_irreducible : ∀ (n : ℕ), 1 ≤ n → ∀ (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H), IrrU τ → IsHCMod τ M j → Nontrivial M.V → FiniteDimensional ℂ M.V ∧ IrrGK M ∧ (∀ h v, ∃ v', j v' = τ.π h (j v)) ∧ ∀ N : Submodule ℂ M.V, (∀ h, ∀ v ∈ N, ∀ v', j v' = τ.π h (j v) → v' ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.CompactCoverIrr.hcMod_finite_irr | exact GlobalTheory.CompactCoverIrr.hcMod_finite_irr | (intros; apply GlobalTheory.CompactCoverIrr.hcMod_finite_irr <;> assumption)
end
