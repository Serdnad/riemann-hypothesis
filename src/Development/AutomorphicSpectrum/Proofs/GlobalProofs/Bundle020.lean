module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem _root_.GlobalTheory.T.partial_zeta_prime_twist_summable : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔠 A B : Ideal (𝓞 F)), (Ideal.absNorm 𝔠).Prime →
  ∀ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} ≃
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠}, (∀ J, (e J).1 = 𝔠 * J.1) →
  ∀ (s : ℂ) (t : ℂ), 1 < s.re →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) →
    HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) t →
    ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (1 - s) *
        (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) -
      (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) = t := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classWeight_relation | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classWeight_relation | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classWeight_relation <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem _root_.GlobalTheory.T.partial_zeta_ray_class_summable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

def LineDeg {r : ℕ} (i : Fin r) (d : ℕ) (g : (Fin r → ℕ) → ℂ) : Prop :=
  ∀ m : Fin r → ℕ, ∃ q : Polynomial ℂ, q.degree < (d : WithBot ℕ) ∧
    ∀ t : ℕ, g (m + t • (Pi.single i 1 : Fin r → ℕ)) = q.eval (t : ℂ)

theorem degree_shift_sub_lt (q : Polynomial ℂ) (d : ℕ) (hq : q.degree < ((d + 1 : ℕ) : WithBot ℕ)) :
    (q.comp (Polynomial.X + 1) - q).degree < (d : WithBot ℕ) := by
  by_cases h0 : q.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    simp
  · have hq0 : q ≠ 0 := fun h => h0 (by simp [h])
    have hX : (Polynomial.X + 1 : Polynomial ℂ).natDegree = 1 := Polynomial.natDegree_X_add_C 1
    have hnat : (q.comp (Polynomial.X + 1)).natDegree = q.natDegree := by
      rw [Polynomial.natDegree_comp, hX, mul_one]
    have hlc : (q.comp (Polynomial.X + 1)).leadingCoeff = q.leadingCoeff := by
      have hm : (Polynomial.X + 1 : Polynomial ℂ).Monic := Polynomial.monic_X_add_C 1
      rw [Polynomial.leadingCoeff_comp (by rw [hX]; exact one_ne_zero), hm.leadingCoeff, one_pow, mul_one]
    have hp0 : q.comp (Polynomial.X + 1) ≠ 0 := by
      intro h
      apply hq0
      rw [← Polynomial.leadingCoeff_eq_zero, ← hlc, h, Polynomial.leadingCoeff_zero]
    have hdeg : (q.comp (Polynomial.X + 1)).degree = q.degree := by
      rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0, hnat]
    have hlt := Polynomial.degree_sub_lt hdeg hp0 hlc
    rw [hdeg, Polynomial.degree_eq_natDegree hq0] at hlt
    rw [Polynomial.degree_eq_natDegree hq0] at hq
    have h1 : q.natDegree < d + 1 := by exact_mod_cast hq
    have h2 : q.natDegree ≤ d := Nat.lt_succ_iff.mp h1
    exact lt_of_lt_of_le hlt (by exact_mod_cast h2)

theorem LineDeg.fd_self {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ}
    (h : LineDeg i (d + 1) g) : LineDeg i d (fd i g) := by
  intro m
  obtain ⟨q, hq, hg⟩ := h m
  refine ⟨q.comp (Polynomial.X + 1) - q, degree_shift_sub_lt q d hq, fun t => ?_⟩
  have e1 : m + t • (Pi.single i 1 : Fin r → ℕ) + Pi.single i 1 =
      m + (t + 1) • (Pi.single i 1 : Fin r → ℕ) := by
    rw [add_smul, one_smul, add_assoc]
  simp only [fd]
  rw [e1, hg, hg, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Nat.cast_add, Nat.cast_one]

theorem LineDeg.fd_any {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ} (k : Fin r)
    (h : LineDeg i d g) : LineDeg i d (fd k g) := by
  intro m
  obtain ⟨q₁, hq₁, hg₁⟩ := h (m + Pi.single k 1)
  obtain ⟨q₂, hq₂, hg₂⟩ := h m
  refine ⟨q₁ - q₂, lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hq₁ hq₂), fun t => ?_⟩
  simp only [fd]
  rw [add_right_comm, hg₁, hg₂, Polynomial.eval_sub]

theorem LineDeg.eq_zero {r : ℕ} {i : Fin r} {g : (Fin r → ℕ) → ℂ}
    (h : LineDeg i 0 g) (m : Fin r → ℕ) : g m = 0 := by
  obtain ⟨q, hq, hg⟩ := h m
  have hq0 : q = 0 := by
    by_contra hne
    rw [Polynomial.degree_eq_natDegree hne] at hq
    have : q.natDegree < 0 := by exact_mod_cast hq
    omega
  have := hg 0
  simp only [zero_smul, add_zero, hq0, Polynomial.eval_zero] at this
  exact this

theorem LineDeg.DL {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ} (h : LineDeg i d g)
    (cs : List (Fin r)) : LineDeg i (d - cs.count i) (DL cs g) := by
  induction cs with
  | nil => simpa [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL] using h
  | cons c cs ih =>
    have e : GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL (c :: cs) g = fd c (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL cs g) := rfl
    rw [e]
    by_cases hc : c = i
    · rw [hc, List.count_cons_self]
      rcases Nat.eq_zero_or_pos (d - cs.count i) with h0 | hpos
      · have h3 : d - (cs.count i + 1) = 0 := by omega
        rw [h3]
        rw [h0] at ih
        exact ih.fd_any i
      · obtain ⟨e', he⟩ : ∃ e', d - cs.count i = e' + 1 := ⟨d - cs.count i - 1, by omega⟩
        have h3 : d - (cs.count i + 1) = e' := by omega
        rw [h3]
        rw [he] at ih
        exact ih.fd_self
    · have h3 : (c :: cs).count i = cs.count i := by simp [List.count_cons, hc]
      rw [h3]
      exact ih.fd_any c

theorem lineDeg_coneTerm (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (i : Fin r)
    (p : ℕ) : LineDeg i (Fintype.card ι * p + 1) (coneTerm a b (-(p : ℂ))) := by
  classical
  intro m
  let c : ι → ℂ := fun j => ((b j + ∑ k, a j k * (m k : ℝ) : ℝ) : ℂ)
  refine ⟨∏ j, (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p, ?_, fun t => ?_⟩
  · have hnd : (∏ j, (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p).natDegree ≤
        Fintype.card ι * p := by
      have hj : ∀ j, ((Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p).natDegree ≤ p := by
        intro j
        calc _ ≤ p * (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)).natDegree :=
              Polynomial.natDegree_pow_le
          _ ≤ p * 1 := Nat.mul_le_mul_left _ Polynomial.natDegree_linear_le
          _ = p := mul_one p
      refine (Polynomial.natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun j _ => hj j).trans ?_)
      simp
    calc _ ≤ _ := Polynomial.degree_le_natDegree
      _ < _ := by exact_mod_cast Nat.lt_succ_of_le hnd
  · rw [Polynomial.eval_prod]
    simp only [coneTerm, neg_neg, Complex.cpow_natCast, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    simp only [c, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero, mul_add, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    push_cast
    ring

theorem DL_coneTerm_neg_natCast_eq_zero : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (cs : List (Fin r)) (i : Fin r) (N p : ℕ), cs.count i = N → Fintype.card ι * p < N →
  ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = 0 := by
  intro ι _ r a b cs i N p hN hlt m
  have h := (lineDeg_coneTerm ι r a b i p).DL cs
  rw [hN, show Fintype.card ι * p + 1 - N = 0 by omega] at h
  exact h.eq_zero m

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_coneTerm_neg_nat_rational :
    ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ), (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∀ cs : List (Fin r), ∃ ρ : (Fin r → ℕ) → ℚ, ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = (ρ m : ℂ) := by
  intro ι _ r a b p h cs
  induction cs with
  | nil =>
    choose q hq using h
    refine ⟨q, fun m => ?_⟩
    show GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm a b (-(p : ℂ)) m = _
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm, neg_neg, Complex.cpow_natCast]
    rw [← Complex.ofReal_ratCast, ← hq m]
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  | cons c cs ih =>
    obtain ⟨ρ, hρ⟩ := ih
    refine ⟨fun m => ρ (m + Pi.single c 1) - ρ m, fun m => ?_⟩
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL, List.foldr_cons, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.fd] at hρ ⊢
    rw [hρ, hρ, Rat.cast_sub]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem cast_add_single_one {r : ℕ} (m : Fin r → ℕ) (c : Fin r) :
    (fun i => (((m + Pi.single c 1 : Fin r → ℕ) i : ℕ) : ℝ)) =
      (fun i => (m i : ℝ)) + Pi.single c 1 := by
  funext i
  by_cases h : i = c
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem DL_coneTerm_eq_DLR : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  intro ι _ r a b s cs m
  induction cs generalizing m with
  | nil => simp [DL, DLR, coneTerm, Fr, linF]
  | cons c cs ih =>
    have h1 : DL (c :: cs) (coneTerm a b s) m =
        DL cs (coneTerm a b s) (m + Pi.single c 1) - DL cs (coneTerm a b s) m := rfl
    have h2 : ∀ x : Fin r → ℝ, DLR (c :: cs) (Fr a b s 0) x =
        DLR cs (Fr a b s 0) (x + Pi.single c 1) - DLR cs (Fr a b s 0) x := fun _ => rfl
    rw [h1, h2, ih, ih, cast_add_single_one]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem coneTerm_differentiable_in_s_alt {ι : Type} [Fintype ι] {r : ℕ} {a : ι → Fin r → ℝ} {b : ι → ℝ}
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (m : Fin r → ℕ) :
    Differentiable ℂ (fun s => coneTerm a b s m) := by
  unfold GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm
  refine Differentiable.fun_finsetProd fun j _ => ?_
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  have hpos : 0 < b j + ∑ i, a j i * (m i : ℝ) :=
    add_pos_of_pos_of_nonneg (hb j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (Nat.cast_nonneg _))
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

theorem DL_coneTerm_differentiable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (cs : List (Fin r)) (m : Fin r → ℕ),
      Differentiable ℂ (fun s => DL cs (coneTerm a b s) m) := by
  intro ι _ r a b ha hb cs
  induction cs with
  | nil => intro m; exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_differentiable_in_s_alt ha hb m
  | cons c cs ih =>
    intro m
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL, List.foldr_cons, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.fd] at ih ⊢
    exact (ih (m + Pi.single c 1)).sub (ih m)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem sum_equivFin_symm {F M : Type} [AddCommMonoid M] (s : Finset F) (f : F → M) :
    ∑ i : Fin s.card, f (s.equivFin.symm i : F) = ∑ y ∈ s, f y := by
  rw [← Finset.sum_coe_sort s f]
  exact Equiv.sum_comp s.equivFin.symm (fun y : s => f (y : F))

theorem openCone_equivFin {F : Type} [Field F] [CharZero F] (s : Finset F) :
    openCone (fun i : Fin s.card => (s.equivFin.symm i : F)) = coneOn s := by
  classical
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun y => if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1, ?_, ?_⟩
    · intro y hy
      simp only [dif_pos hy]
      exact ht _
    · rw [← sum_equivFin_symm s (fun y => (if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1 : ℚ) • y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hm : (s.equivFin.symm i : F) ∈ s := (s.equivFin.symm i).2
      simp only [dif_pos hm, Subtype.coe_eta, Equiv.apply_symm_apply]
      rw [Rat.smul_def]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t (s.equivFin.symm i : F), fun i => ht _ (s.equivFin.symm i).2, ?_⟩
    rw [← sum_equivFin_symm s (fun y => t y • y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def]

theorem tile_family {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F) (h : Tile P Q C) :
    (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) := by
  induction h with
  | empty =>
    intro _
    exact ⟨Empty, inferInstance, fun c => c.elim, fun c => c.elim, fun c => c.elim, fun c => c.elim,
      fun c => c.elim, fun c => c.elim, fun x hx => hx.elim⟩
  | cone s hli hP hQ =>
    intro h0
    have hcone := openCone_equivFin s
    refine ⟨Unit, inferInstance, fun _ => s.card, fun _ i => (s.equivFin.symm i : F), ?_, ?_, ?_, ?_, ?_⟩
    · intro _
      refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_)
      rintro rfl
      exact h0 ⟨fun _ => 0, by simp, by simp⟩
    · intro _
      have hinj : Function.Injective (fun i : Fin s.card => (⟨(s.equivFin.symm i : F), (s.equivFin.symm i).2⟩ : (s : Set F))) := by
        intro i j hij
        exact s.equivFin.symm.injective (Subtype.ext (congrArg Subtype.val hij))
      exact LinearIndependent.comp hli _ hinj
    · intro _ i
      exact hP (s.equivFin.symm i).2
    · intro _
      exact hcone.le
    · intro x hx
      exact ⟨(), hcone.ge hx, fun _ _ => rfl⟩
  | @union A B _ _ hAB ihA ihB =>
    intro h0
    obtain ⟨ι₁, f₁, r₁, v₁, hr₁, hl₁, hp₁, hs₁, hu₁⟩ := ihA (fun h => h0 (Or.inl h))
    obtain ⟨ι₂, f₂, r₂, v₂, hr₂, hl₂, hp₂, hs₂, hu₂⟩ := ihB (fun h => h0 (Or.inr h))
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim r₁ r₂,
      fun c => match c with
        | Sum.inl a => v₁ a
        | Sum.inr b => v₂ b, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (a | b)
      · exact hr₁ a
      · exact hr₂ b
    · rintro (a | b)
      · exact hl₁ a
      · exact hl₂ b
    · rintro (a | b) i
      · exact hp₁ a i
      · exact hp₂ b i
    · rintro (a | b)
      · exact (hs₁ a).trans Set.subset_union_left
      · exact (hs₂ b).trans Set.subset_union_right
    · rintro x (hx | hx)
      · obtain ⟨a, ha, hu⟩ := hu₁ x hx
        refine ⟨Sum.inl a, ha, ?_⟩
        rintro (a' | b') h'
        · exact congrArg Sum.inl (hu a' h')
        · exact (Set.disjoint_left.mp hAB hx (hs₂ b' h')).elim
      · obtain ⟨b, hb, hu⟩ := hu₂ x hx
        refine ⟨Sum.inr b, hb, ?_⟩
        rintro (a' | b') h'
        · exact (Set.disjoint_left.mp hAB (hs₁ a' h') hx).elim
        · exact congrArg Sum.inr (hu b' h')

theorem tile_family_closed : ∀ {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F), Tile P Q C → (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) :=
  fun P Q C h => tile_family P Q C h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

end

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.shintani_cone_decomposition : ∀ {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F), Tile P Q C → (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.tile_family_closed <;> assumption)

end
end
