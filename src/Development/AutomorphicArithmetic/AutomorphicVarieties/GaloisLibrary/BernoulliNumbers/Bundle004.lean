module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
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

@[expose] public section

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_ratprod :
    ∀ {N : ℕ} [NeZero N] (P : Set (Subgroup (ZMod N)ˣ)) (F : ∀ (Ω : Type) [Field Ω] [CharZero Ω], DirichletCharacter Ω N → Ω), (∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [CharZero Ω] (f : K →+* Ω) (χ : DirichletCharacter K N), f (F K χ) = F Ω (χ.ringHomComp f)) → ∃ q : ℚ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)], ∏ᶠ χ ∈ charSet Ω P, F Ω χ = (q : Ω) := by
  intro N _ P F hF
  set e := Monoid.exponent (ZMod N)ˣ with he_def
  haveI he : NeZero e := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : NeZero (e : ℚ) := ⟨by exact_mod_cast he.out⟩
  haveI hcyc : IsCyclotomicExtension {e} ℚ (CyclotomicField e ℚ) :=
    CyclotomicField.isCyclotomicExtension e ℚ
  haveI : IsGalois ℚ (CyclotomicField e ℚ) := IsCyclotomicExtension.isGalois {e} ℚ _
  haveI : FiniteDimensional ℚ (CyclotomicField e ℚ) :=
    IsCyclotomicExtension.finiteDimensional {e} ℚ _
  have hζ := IsCyclotomicExtension.zeta_spec e ℚ (CyclotomicField e ℚ)
  haveI : HasEnoughRootsOfUnity (CyclotomicField e ℚ) e :=
    ⟨⟨_, hζ⟩, rootsOfUnity.isCyclic (CyclotomicField e ℚ) e⟩
  have hfin : ∀ (Ω : Type) [Field Ω], (charSet Ω P).Finite := fun Ω _ => Set.toFinite _
  have hfix : ∀ σ : CyclotomicField e ℚ ≃ₐ[ℚ] CyclotomicField e ℚ,
      σ (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) =
        ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ := by
    intro σ
    have h1 := (σ.toRingHom.toMonoidHom).map_finprod_mem
      (fun χ => F (CyclotomicField e ℚ) χ) (hfin (CyclotomicField e ℚ))
    refine h1.trans ?_
    exact finprod_mem_eq_of_bijOn _ (b_charbij σ.toRingHom P)
      (fun χ _ => hF _ _ σ.toRingHom χ)
  have hbot := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hbot
  refine ⟨q, fun Ω _ _ _ => ?_⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω e
  have hmin : Polynomial.aeval ω (minpoly ℚ (hζ.powerBasis ℚ).gen) = 0 := by
    rw [IsPrimitiveRoot.powerBasis_gen, ← hζ.minpoly_eq_cyclotomic_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos e)), Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hω.isRoot_cyclotomic (NeZero.pos e)
  let g := (hζ.powerBasis ℚ).lift ω hmin
  calc ∏ᶠ χ ∈ charSet Ω P, F Ω χ
      = ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, g.toRingHom (F (CyclotomicField e ℚ) χ) :=
        (finprod_mem_eq_of_bijOn _ (b_charbij g.toRingHom P)
          (fun χ _ => hF _ _ g.toRingHom χ)).symm
    _ = g.toRingHom (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) :=
        (g.toRingHom.toMonoidHom.map_finprod_mem _ (hfin _)).symm
    _ = (q : Ω) := by
        rw [← hq]
        exact g.commutes q |>.trans (eq_ratCast _ q)
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_raabe :
    ∀ (N m k a : ℕ), 0 < N → 0 < m → bcoef N k a = ∑ j ∈ range m, bcoef (N * m) k (a + j * N) := by
  intro N m k a hN hm
  let F : ℕ → ℕ → PowerSeries ℚ := fun M c => PowerSeries.mk fun i => bcoef M i c / (i.factorial : ℚ)
  let y : PowerSeries ℚ := PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ)
  let E : PowerSeries ℚ := PowerSeries.rescale ((N * m : ℕ) : ℚ) (PowerSeries.exp ℚ) - 1
  have hpow : ∀ j : ℕ, y ^ j = PowerSeries.rescale ((j : ℚ) * N) (PowerSeries.exp ℚ) := by
    intro j
    simp only [y]
    rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
  have hE : E = (∑ j ∈ range m, y ^ j) * (y - 1) := by
    rw [geom_sum_mul, hpow]
    simp only [E]
    push_cast
    rw [mul_comm (m : ℚ)]
  have hE0 : E ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h1
    rcases h1 with h1 | h1
    · exact hN.ne' h1
    · exact hm.ne' h1
  suffices h : F N a = ∑ j ∈ range m, F (N * m) (a + j * N) by
    have h2 := congrArg (PowerSeries.coeff k) h

    rw [map_sum] at h2
    simp only [F, PowerSeries.coeff_mk] at h2
    rw [← Finset.sum_div, div_left_inj' (by positivity)] at h2
    exact h2
  apply mul_right_cancel₀ hE0
  calc F N a * E = F N a * (y - 1) * ∑ j ∈ range m, y ^ j := by rw [hE]; ring
    _ = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) * ∑ j ∈ range m, y ^ j := by
        rw [b_egf N a hN]
    _ = ∑ j ∈ range m, PowerSeries.X * PowerSeries.rescale ((a + j * N : ℕ) : ℚ) (PowerSeries.exp ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpow, mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]
        push_cast
        rfl
    _ = ∑ j ∈ range m, F (N * m) (a + j * N) * E := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [b_egf (N * m) (a + j * N) (Nat.mul_pos hN hm)]
    _ = (∑ j ∈ range m, F (N * m) (a + j * N)) * E := by rw [Finset.sum_mul]
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primmap :
    ∀ {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ (k : ℕ) (χ : DirichletCharacter R N), f (Bprim k χ) = Bprim k (χ.ringHomComp f) := by
  intro R S _ _ _ _ N _ f hf k χ
  obtain ⟨hcond, hval, -⟩ := b_condmap f hf χ

  rw [Bprim_eq, Bprim_eq, hcond, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, hval a, RingHom.map_rat_algebraMap]
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_denint :
    ∀ (N k a : ℕ), 0 < N → ∃ z : ℤ, (den N k : ℚ) * bcoef N k a = z := by
  intro N k a hN
  suffices h : (den N k : ℚ) * bcoef N k a ∈ (Int.castRingHom ℚ).range by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, hz.symm⟩
  rw [b_expand N k a hN, Finset.mul_sum]
  refine Subring.sum_mem _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨z, hz⟩ := b_primden k j hjk
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : (N : ℚ) * (N : ℚ) ^ ((j : ℤ) - 1) = (N : ℚ) ^ j := by
    rw [← zpow_one_add₀ hN', add_sub_cancel, zpow_natCast]
  refine ⟨(k.choose j : ℤ) * z * (N : ℤ) ^ j * (a : ℤ) ^ (k - j), ?_⟩
  unfold den
  rw [eq_intCast]
  push_cast
  rw [← hz, ← hpow]
  ring
end

section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_upper :
    ∀ {N : ℕ} (k : ℕ) (Φ : ZMod N → ℂ), 0 < N → (∀ a, ‖Φ a‖ ≤ 1) → ‖genB k Φ‖ ≤ 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro N k Φ hN hΦ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k with hC
  have hterm : ∀ a ∈ Icc 1 N,
      ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ ≤ (N : ℝ) ^ ((k : ℤ) - 1) * C := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hx0 : (0 : ℚ) ≤ (a : ℚ) / N := by positivity
    have hx1 : (a : ℚ) / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast ha.2
    have hb : ‖algebraMap ℚ ℂ (bcoef N k a)‖ =
        (N : ℝ) ^ ((k : ℤ) - 1) * |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, bcoef]
      push_cast
      rw [abs_mul, abs_of_pos (zpow_pos hNr _)]
    rw [norm_mul, hb]
    have hp := b_polybound k ((a : ℚ) / N) hx0 hx1
    calc ‖Φ (a : ZMod N)‖ * ((N : ℝ) ^ ((k : ℤ) - 1) *
          |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)|)
        ≤ 1 * ((N : ℝ) ^ ((k : ℤ) - 1) * C) := by
          apply mul_le_mul (hΦ _) _ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hp (zpow_pos hNr _).le
      _ = (N : ℝ) ^ ((k : ℤ) - 1) * C := one_mul _
  calc ‖genB k Φ‖ ≤ ∑ a ∈ Icc 1 N, ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a ∈ Icc 1 N, (N : ℝ) ^ ((k : ℤ) - 1) * C := Finset.sum_le_sum hterm
    _ = 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          zpow_sub_one₀ hNr.ne', zpow_natCast, hC]
        field_simp
end
