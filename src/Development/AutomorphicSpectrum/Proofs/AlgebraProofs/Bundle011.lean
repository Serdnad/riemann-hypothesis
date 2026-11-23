module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsMonogenicSeparating
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CharZeroFreeModule
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle003
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem charpoly_condition_gives_free_char_zero : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [CharZero k] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ :=
  PositivityTheory.Xgn.char_zero_free_module

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem finite_int_of_finite_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] : Module.Finite ℤ L :=
  Module.Finite.trans (𝓞 E) L

theorem free_int_of_projective_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Free ℤ L := by
  haveI : Module.Finite ℤ L := finite_int_of_finite_ringOfIntegers E L
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) L)
  have hinj : Function.Injective s := fun x y hxy => by
    have := congrArg (Finsupp.linearCombination (𝓞 E) id) hxy
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  haveI : Module.IsTorsionFree ℤ (L →₀ 𝓞 E) := inferInstance
  haveI : Module.IsTorsionFree ℤ L :=
    hinj.moduleIsTorsionFree (R := ℤ) s fun r m => by simp
  infer_instance

end GlobalTheory.CompanionTheory.Ar
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem block_monogenic_of_residual_character : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  exact @PositivityTheory.Xgn.exists_monogenic_separating

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_mul_complexConj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (x : E) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : x * IsCMField.complexConj E x = 1 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  have h1 : ‖φ x‖ = 1 := by
    have h : ‖φ x‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  rw [map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h1]
  simp

theorem root_eq_one_of_halfLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ (I : Ideal (𝓞 E)) (M : ℕ), 3 ≤ M → I * I.map (bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)} → I ⊔ I.map (bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∀ (u : 𝓞 E) (n : ℕ), 0 < n → u ^ n = 1 → u - 1 ∈ I → u = 1 := by
  intro E _ _ _ bar hbar I M hM hI hco u n hn hu h1
  have hub : u * bar u = 1 := by
    apply RingOfIntegers.ext
    have hx : (u : E) ^ n = 1 := by
      have := congrArg (fun a : 𝓞 E => (a : E)) hu
      simpa using this
    have := root_mul_complexConj_eq_one (u : E) n hn hx
    rw [← hbar] at this
    simpa using this
  have h2 : bar u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (bar : 𝓞 E →+* 𝓞 E) h1
    simpa using this
  have h3 : u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have e : u - 1 = (-u) * (bar u - 1) := by linear_combination hub
    rw [e]
    exact Ideal.mul_mem_left _ _ h2
  have h4 : u - 1 ∈ Ideal.span {(M : 𝓞 E)} := by
    rw [← hI, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 hco)]
    exact ⟨h1, h3⟩
  exact GlobalTheory.CompanionTheory.Ar.Flat.root_of_unity_eq_one_of_dvd_sub_one E u n M hn hu hM (Ideal.mem_span_singleton.1 h4)

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_range_of_integral_at_heightOne_over :
    ∀ (B K : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
      [Field K] [Algebra B K] [IsFractionRing B K] (ϖ : B) (x : K), ϖ ≠ 0 →
      (∃ (N : ℕ) (b : B), algebraMap B K b = algebraMap B K ϖ ^ N * x) →
      (∀ P : Ideal B, P.IsPrime → P.height = 1 → ϖ ∈ P →
        ∃ (b c : B), c ∉ P ∧ algebraMap B K b = algebraMap B K c * x) →
      ∃ b : B, algebraMap B K b = x := by
  intro B K _ _ _ _ _ _ _ ϖ x _ hN hP
  obtain ⟨N, b, hb⟩ := hN
  obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := B) (K := K) x
    (fun p hp h1 => by
      by_cases hm : ϖ ∈ p
      · obtain ⟨b', c, hc, hbc⟩ := hP p hp h1 hm
        exact ⟨b', c, hc, by rw [hbc, mul_comm]⟩
      · exact ⟨b, ϖ ^ N, fun h => hm (hp.mem_of_pow_mem N h), by rw [hb, map_pow, mul_comm]⟩)
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.HeightOneFrame

theorem integral_of_integral_at_height_one :
    ∀ (A Ω : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field Ω]
      [Algebra A Ω] [IsFractionRing A Ω] (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ)
      (b b' : Fin r → E), LinearIndependent Ω b →
      (∀ P : PrimeSpectrum A, P.asIdeal.height = 1 → ∀ i, ∃ (s : A) (c : Fin r → A),
        s ∉ P.asIdeal ∧ algebraMap A Ω s • b' i = ∑ k, algebraMap A Ω (c k) • b k) →
      (∀ i, b' i ∈ Submodule.span Ω (Set.range b)) →
      ∀ i, ∃ c : Fin r → A, b' i = ∑ k, algebraMap A Ω (c k) • b k := by
  intro A Ω _ _ _ _ _ _ _ E _ _ r b b' hb hP hspan i
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).mp (hspan i)
  have key : ∀ k, x k ∈ Set.range (algebraMap A Ω) := by
    intro k
    refine GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := A) (K := Ω) (x k) ?_
    intro p hp h1
    obtain ⟨s, c, hs, hc⟩ := hP ⟨p, hp⟩ h1 i
    refine ⟨c k, s, hs, ?_⟩
    have h0 : ∑ j, (algebraMap A Ω s * x j - algebraMap A Ω (c j)) • b j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
      rw [hx, hc, sub_self]
    have h2 := (Fintype.linearIndependent_iff.mp hb) _ h0 k
    have h3 : algebraMap A Ω s * x k = algebraMap A Ω (c k) := sub_eq_zero.mp h2
    rw [← h3, mul_comm]
  choose c hc using key
  refine ⟨c, ?_⟩
  rw [← hx]
  simp only [hc]

end GlobalTheory.CompanionTheory.HeightOneFrame
end
