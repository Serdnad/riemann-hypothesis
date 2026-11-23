module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.Connected
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

section

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

noncomputable def mvPolynomialOnLine {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) :
    Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (a i) + Polynomial.C (b i - a i) * Polynomial.X) q

theorem eval_mvPolynomialOnLine {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) (t : ℂ) :
    (mvPolynomialOnLine q a b).eval t = MvPolynomial.eval (a + t • (b - a)) q := by
  unfold mvPolynomialOnLine
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => rw [map_add (f := _), Polynomial.eval_add, hp, hr, map_add (f := _)]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

theorem finite_zeros_on_line {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ)
    (hb : MvPolynomial.eval b q ≠ 0) :
    {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}.Finite := by
  have hP : mvPolynomialOnLine q a b ≠ 0 := by
    intro h
    apply hb
    have := eval_mvPolynomialOnLine q a b 1
    simpa [h] using this.symm
  convert Polynomial.finite_setOfPred_isRoot hP using 1
  ext t
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, eval_mvPolynomialOnLine]

private theorem mvPolynomial_exists_eval_ne_zero {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (hq : q ≠ 0) :
    ∃ x : Fin d → ℂ, MvPolynomial.eval x q ≠ 0 := by
  by_contra h
  push Not at h
  exact hq (MvPolynomial.funext fun x => by simp [h x])

private theorem joinedIn_setOf_eval_ne_zero {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ)
    (ha : MvPolynomial.eval a q ≠ 0) (hb : MvPolynomial.eval b q ≠ 0) :
    JoinedIn {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} a b := by
  have hZ := finite_zeros_on_line q a b hb
  have hpc : IsPathConnected {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ :=
    hZ.countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)
  have h0 : (0 : ℂ) ∈ {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ := by simpa using ha
  have h1 : (1 : ℂ) ∈ {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ := by simpa using hb
  have hf : Continuous fun t : ℂ => a + t • (b - a) := by fun_prop
  have hj := (hpc.joinedIn 0 h0 1 h1).map hf.continuousOn
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at hj
  refine hj.mono ?_
  rintro _ ⟨t, ht, rfl⟩
  exact ht

theorem isConnected_and_dense_compl_hypersurface :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 →
      IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧
        Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) := by
  intro d q hq
  obtain ⟨b, hb⟩ := mvPolynomial_exists_eval_ne_zero q hq
  refine ⟨(isPathConnected_iff.2 ⟨⟨b, hb⟩, fun x hx y hy => joinedIn_setOf_eval_ne_zero q x y hx hy⟩).isConnected,
    fun x => ?_⟩
  have hf : Continuous fun t : ℂ => x + t • (b - x) := by fun_prop
  have hlim : Tendsto (fun t : ℂ => x + t • (b - x)) (𝓝[≠] (0 : ℂ)) (𝓝 x) := by
    have := hf.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine mem_closure_of_tendsto hlim ?_
  have hZ := finite_zeros_on_line q x b hb
  have hcl : IsClosed ({t : ℂ | MvPolynomial.eval (x + t • (b - x)) q = 0} \ {0}) :=
    (hZ.subset Set.sdiff_subset).isClosed
  have e1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      t ∉ ({t : ℂ | MvPolynomial.eval (x + t • (b - x)) q = 0} \ {0}) :=
    nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp))
  have e2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
  filter_upwards [e1, e2] with t ht1 ht2
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not] at ht1
  show MvPolynomial.eval (x + t • (b - x)) q ≠ 0
  exact fun h => ht2 (ht1 h)

end GlobalTheory
end

section

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

noncomputable def evalPair {d : ℕ} (z : (Fin d → ℂ) × ℂ) :
    Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ :=
  Polynomial.eval₂RingHom (MvPolynomial.eval z.1) z.2

theorem evalPair_eq {d : ℕ} (z : (Fin d → ℂ) × ℂ) (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    evalPair z r = (r.map (MvPolynomial.eval z.1)).eval z.2 := by
  simp [evalPair, Polynomial.eval_map]

@[simp] theorem evalPair_C {d : ℕ} (z : (Fin d → ℂ) × ℂ) (s : MvPolynomial (Fin d) ℂ) :
    evalPair z (Polynomial.C s) = MvPolynomial.eval z.1 s := by
  simp [evalPair]

@[simp] theorem evalPair_X {d : ℕ} (z : (Fin d → ℂ) × ℂ) :
    evalPair z Polynomial.X = z.2 := by
  simp [evalPair]

theorem continuous_evalPair {d : ℕ} (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    Continuous fun z : (Fin d → ℂ) × ℂ => evalPair z r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | monomial n s =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, evalPair_C, evalPair_X]
    exact ((MvPolynomial.continuous_eval s).comp continuous_fst).mul (continuous_snd.pow n)

theorem points_eq_image_hypersurface {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q q' : MvPolynomial (Fin d) ℂ)
    (hp : ∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r)
    (r : A → Polynomial (MvPolynomial (Fin d) ℂ))
    (hr : ∀ b, j q * b = (r b).eval₂ j.toRingHom a) :
    {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (j (q * q')) ≠ 0} =
      (fun (z : (Fin d → ℂ) × ℂ) (b : A) => evalPair z (r b) / MvPolynomial.eval z.1 q) ''
        {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 (q * q') ≠ 0 ∧
          (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} := by
  set E : Polynomial (MvPolynomial (Fin d) ℂ) →+* A :=
    Polynomial.eval₂RingHom j.toRingHom a with hE
  have hEr : ∀ b, E (r b) = j q * b := fun b => (hr b).symm
  have hEC : ∀ s, E (Polynomial.C s) = j s := fun s => by simp [hE]
  ext x
  constructor
  · rintro ⟨φ, rfl, hφ⟩
    let z : (Fin d → ℂ) × ℂ := (fun i => φ (j (MvPolynomial.X i)), φ a)
    have h1 : ∀ s, φ (j s) = MvPolynomial.eval z.1 s := by
      intro s
      induction s using MvPolynomial.induction_on with
      | C c =>
        have : (MvPolynomial.C c : MvPolynomial (Fin d) ℂ) = algebraMap ℂ _ c := rfl
        rw [MvPolynomial.eval_C, this, AlgHom.commutes, AlgHom.commutes]; rfl
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
      | mul_X s i hs => simp only [map_mul, hs, MvPolynomial.eval_X, z]
    have h2 : ∀ s, φ (E s) = evalPair z s := by
      intro s
      induction s using Polynomial.induction_on' with
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
      | monomial n s =>
        have hX : E Polynomial.X = a := by simp [hE]
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_mul, map_pow, map_pow,
          map_pow, evalPair_C, evalPair_X, hEC, h1, hX]
    have hne : MvPolynomial.eval z.1 (q * q') ≠ 0 := by rwa [← h1]
    have hq : MvPolynomial.eval z.1 q ≠ 0 := by
      rw [map_mul] at hne; exact left_ne_zero_of_mul hne
    refine ⟨z, ⟨hne, ?_⟩, ?_⟩
    · have : E p = 0 := (hp p).2 dvd_rfl
      rw [← evalPair_eq, ← h2, this, map_zero]
    · funext b
      simp only
      rw [← h2, hEr, map_mul, h1]
      field_simp
  · rintro ⟨z, ⟨hne, hz⟩, rfl⟩
    have hq : MvPolynomial.eval z.1 q ≠ 0 := by
      rw [map_mul] at hne; exact left_ne_zero_of_mul hne
    rw [← evalPair_eq] at hz
    have key : ∀ s t, E s = E t → evalPair z s = evalPair z t := by
      intro s t hst
      have h0 : E (s - t) = 0 := by rw [map_sub, hst, sub_self]
      obtain ⟨u, hu⟩ := (hp (s - t)).1 h0
      rw [← sub_eq_zero, ← map_sub, hu, map_mul, hz, zero_mul]
    have hj : ∀ s, evalPair z (r (j s)) / MvPolynomial.eval z.1 q = MvPolynomial.eval z.1 s := by
      intro s
      rw [key (r (j s)) (Polynomial.C (q * s)) (by rw [hEr, hEC, map_mul]), evalPair_C, map_mul]
      field_simp
    let φ : A →ₐ[ℂ] ℂ :=
      { toFun := fun b => evalPair z (r b) / MvPolynomial.eval z.1 q
        map_one' := by simpa using hj 1
        map_zero' := by simpa using hj 0
        map_mul' := by
          intro b c
          have := key (r (b * c) * Polynomial.C q) (r b * r c)
            (by simp only [map_mul, hEr, hEC]; ring)
          simp only [map_mul, evalPair_C] at this
          field_simp
          exact this
        map_add' := by
          intro b c
          have := key (r (b + c)) (r b + r c) (by simp only [map_add (f := _), hEr]; ring)
          rw [this, map_add (f := _), add_div]
        commutes' := by
          intro c
          have := hj (algebraMap ℂ _ c)
          rw [AlgHom.commutes] at this
          rw [this]
          simp }
    refine ⟨φ, rfl, ?_⟩
    simp only
    rw [hj]
    exact hne

theorem exists_isConnected_principalOpen :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), p.Monic → Irreducible p → q ≠ 0 → (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 → (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) → IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → ∃ h : A, h ≠ 0 ∧ IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (h * f) ≠ 0}) := by
  intro H1 H2 A _ _ _ _ f hf
  obtain ⟨d, j, a, p, q, -, hinj, hfin, hmon, hirr, hp, hq, hspan, hr⟩ := H1 A
  choose r hr using hr
  obtain ⟨q', hq', f', hf'⟩ : ∃ q' : MvPolynomial (Fin d) ℂ, q' ≠ 0 ∧ f ∣ j q' := by
    letI : Algebra (MvPolynomial (Fin d) ℂ) A := j.toRingHom.toAlgebra
    haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
    have hint : IsIntegral (MvPolynomial (Fin d) ℂ) f := Algebra.IsIntegral.isIntegral f
    exact hint.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)
  have hmul : j q * f' * f = j (q * q') := by rw [map_mul, hf']; ring
  have hqq : q * q' ≠ 0 := mul_ne_zero hq hq'
  refine ⟨j q * f', ?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hmul
    exact hqq (hinj (by rw [← hmul, map_zero]))
  · rw [hmul, points_eq_image_hypersurface j a p q q' hp r hr]
    refine (H2 d p (q * q') hmon hirr hqq ?_).image _ ?_
    · intro x y hx hy hd
      obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hspan
      have h := congrArg (evalPair (x, y)) huv
      rw [Polynomial.derivative_map] at hd
      simp only [map_add (f := _), map_mul, evalPair_C] at h
      rw [evalPair_eq _ p, evalPair_eq _ p.derivative, hy, hd, mul_zero, mul_zero, add_zero] at h
      rw [map_mul, ← h, zero_mul] at hx
      exact hx rfl
    · refine continuousOn_pi.2 fun b => ContinuousOn.div (continuous_evalPair _).continuousOn
        ((MvPolynomial.continuous_eval q).comp continuous_fst).continuousOn ?_
      intro z hz
      have := hz.1
      rw [map_mul] at this
      exact left_ne_zero_of_mul this

end GlobalTheory
end

section

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem exists_localFrame_compatible_cube :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (i₀ : ι), 0 ∈ W i₀ → ∀ F : (Fin 3 → Fin g → ℂ) → ℂ, F = T (fun _ => i₀) → (∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) → (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∃ (r : ℝ) (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  intro H1 H2 g ι W c hW hcov hcd hc0 hcoc T hTd hT0 hTc Λ hΛd hΛs hWp hcp hTp
  obtain ⟨i₀, hi₀⟩ := hcov 0
  obtain ⟨F, hF⟩ : ∃ F, F = T (fun _ => i₀) := ⟨_, rfl⟩
  let U : Set (Fin 3 → Fin g → ℂ) := {x | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W i₀}
  have hUo : IsOpen U := by
    have e : U = ⋂ I : Finset (Fin 3), (fun x : Fin 3 → Fin g → ℂ => ∑ a ∈ I, x a) ⁻¹' W i₀ := by
      ext x
      simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun I =>
      (hW i₀).preimage (continuous_finsetSum I fun a _ => continuous_apply a)
  have hU0 : (0 : Fin 3 → Fin g → ℂ) ∈ U := fun I => by simpa using hi₀
  have hUn : U ∈ 𝓝 (0 : Fin 3 → Fin g → ℂ) := hUo.mem_nhds hU0
  have hFa : AnalyticAt ℂ F 0 := hF ▸ GlobalTheory.SCV.analyticAt_of_differentiableOn (hTd _) hUn
  have hF0 : F 0 ≠ 0 := hF ▸ hT0 _ 0 hU0
  have hcube := H1 g W c hW hcov hcd hc0 hcoc T hTd hT0 hTc Λ hΛd hΛs hWp hcp hTp i₀ hi₀ F hF
  obtain ⟨k, hka, -, hkF⟩ := H2 g F hFa hF0 hcube
  obtain ⟨ε, hε, hkε⟩ : ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Fin g → ℂ) ε, DifferentiableAt ℂ k z :=
    Metric.eventually_nhds_iff_ball.1 (hka.eventually_analyticAt.mono fun z hz => hz.differentiableAt)
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.1 (hW i₀) 0 hi₀
  have hrW : ∀ z ∈ Metric.ball (0 : Fin g → ℂ) (min ε δ), z ∈ W i₀ := fun z hz =>
    hδW (Metric.ball_subset_ball (min_le_right _ _) hz)
  refine ⟨min ε δ, fun i z => c i i₀ z * cexp (k z), F 0, lt_min hε hδ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    show DifferentiableOn ℂ (fun z => c i i₀ z * cexp (k z)) _
    refine DifferentiableOn.mul ((hcd i i₀).mono ?_) ?_
    · rintro z ⟨hz1, hz2⟩
      exact ⟨hz1, hrW z hz2⟩
    · intro z hz
      exact (hkε z (Metric.ball_subset_ball (min_le_left _ _) hz.2)).cexp.differentiableWithinAt
  · intro i z hz hzr
    exact mul_ne_zero (hc0 i i₀ z hz (hrW z hzr)) (Complex.exp_ne_zero _)
  · intro i j z hzi hzj hzr
    show c i i₀ z * cexp (k z) = c i j z * (c j i₀ z * cexp (k z))
    rw [← mul_assoc, hcoc i j i₀ z hzi hzj (hrW z hzr)]
  · filter_upwards [hkF, hUn] with x hx hxU
    intro j hj
    rw [hTc j (fun _ => i₀) x hj hxU, ← hF, hx]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    ring

end GlobalTheory
end

section

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def doublingIterate (h : E → ℂ) : ℕ → E → ℂ
  | 0 => fun z => h ((2 : ℂ)⁻¹ • z)
  | n + 1 => fun z =>
      3 * doublingIterate h n ((2 : ℂ)⁻¹ • z) + doublingIterate h n (-((2 : ℂ)⁻¹ • z))

private theorem norm_half_smul (z : E) : ‖(2 : ℂ)⁻¹ • z‖ = ‖z‖ / 2 := by
  rw [norm_smul, norm_inv]
  simp [div_eq_inv_mul]

private theorem half_mem_ball {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    (2 : ℂ)⁻¹ • z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_half_smul]
  linarith [norm_nonneg z]

private theorem neg_mem_ball' {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    -z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rwa [norm_neg]

theorem differentiableOn_doublingIterate {h : E → ℂ} {r : ℝ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 r)) (n : ℕ) :
    DifferentiableOn ℂ (doublingIterate h n) (Metric.ball 0 r) := by
  induction n with
  | zero => exact hh.comp (by fun_prop) fun z hz => half_mem_ball hz
  | succ n ih =>
    have h1 : DifferentiableOn ℂ (fun z : E => doublingIterate h n ((2 : ℂ)⁻¹ • z))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => half_mem_ball hz
    have h2 : DifferentiableOn ℂ (fun z : E => doublingIterate h n (-((2 : ℂ)⁻¹ • z)))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => neg_mem_ball' (half_mem_ball hz)
    exact (h1.const_mul 3).add h2

theorem norm_doublingIterate_le {h : E → ℂ} {r C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3) (n : ℕ) :
    ∀ z ∈ Metric.ball (0 : E) r, ‖doublingIterate h n z‖ ≤ (1 / 2) ^ n * (C * ‖z‖ ^ 3) := by
  induction n with
  | zero =>
    intro z hz
    have h1 := hh _ (half_mem_ball hz)
    rw [norm_half_smul] at h1
    have h2 : 0 ≤ C * ‖z‖ ^ 3 := by positivity
    change ‖h ((2 : ℂ)⁻¹ • z)‖ ≤ _
    nlinarith
  | succ n ih =>
    intro z hz
    have h1 := ih _ (half_mem_ball hz)
    have h2 := ih _ (neg_mem_ball' (half_mem_ball hz))
    rw [norm_neg] at h2
    rw [norm_half_smul] at h1 h2
    change ‖3 * doublingIterate h n ((2 : ℂ)⁻¹ • z)
      + doublingIterate h n (-((2 : ℂ)⁻¹ • z))‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h3 : ‖(3 : ℂ)‖ = 3 := by simp
    rw [h3]
    calc _ ≤ 3 * ((1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3)) + (1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3) := by
          gcongr
      _ = _ := by ring

theorem exists_doubling_solution [FiniteDimensional ℂ E] (h : E → ℂ) (ha : AnalyticAt ℂ h 0)
    (hO : h =O[𝓝 0] (fun z => ‖z‖ ^ 3)) :
    ∃ k : E → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
      ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z := by
  obtain ⟨C, hC, hO⟩ := hO.exists_nonneg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hO.bound.and ha.eventually_analyticAt)
  have hd : DifferentiableOn ℂ h (Metric.ball 0 r) :=
    fun z hz => (hball z hz).2.differentiableAt.differentiableWithinAt
  have hb : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3 := fun z hz => by
    simpa using (hball z hz).1
  have hB := norm_doublingIterate_le hC hb
  have hgeom : ∀ c : ℝ, HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * c) (2 * c) :=
    fun c => hasSum_geometric_two.mul_right c
  have hS : ∀ z ∈ Metric.ball (0 : E) r, Summable fun n => doublingIterate h n z :=
    fun z hz => Summable.of_norm_bounded (hgeom _).summable fun n => hB n z hz
  refine ⟨fun z => ∑' n, doublingIterate h n z, ?_, ?_, ?_⟩
  · refine SCV.analyticAt_of_differentiableOn (s := Metric.ball 0 r)
      (SCV.differentiableOn_tsum_of_locally_normal Metric.isOpen_ball
        (differentiableOn_doublingIterate hd) fun x hx =>
          ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds hx, _, (hgeom (C * r ^ 3)).summable,
            fun n z hz => (hB n z hz).trans ?_⟩) (Metric.ball_mem_nhds 0 hr)
    have := (mem_ball_zero_iff.mp hz).le
    gcongr
  · refine Asymptotics.IsBigO.of_bound (2 * C) ?_
    filter_upwards [Metric.ball_mem_nhds 0 hr] with z hz
    refine (tsum_of_norm_bounded (hgeom _) fun n => hB n z hz).trans_eq ?_
    simp [mul_assoc]
  · filter_upwards [Metric.ball_mem_nhds (0 : E) (half_pos hr)] with z hz
    rw [mem_ball_zero_iff] at hz
    have hz1 : z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff]
      linarith
    have hz2 : (2 : ℂ) • z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff, norm_smul]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]
      linarith
    have e : (2 : ℂ)⁻¹ • (2 : ℂ) • z = z := inv_smul_smul₀ two_ne_zero z
    rw [(hS _ hz2).tsum_eq_zero_add]
    simp only [doublingIterate, e]
    rw [((hS z hz1).mul_left 3).tsum_add (hS _ (neg_mem_ball' hz1)), tsum_mul_left]
    ring

end

theorem exists_doubling_solution_pi :
    ∀ (g : ℕ) (h : (Fin g → ℂ) → ℂ), AnalyticAt ℂ h 0 → h =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
        ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z :=
  fun _ h ha hO => exists_doubling_solution h ha hO

end GlobalTheory
end
