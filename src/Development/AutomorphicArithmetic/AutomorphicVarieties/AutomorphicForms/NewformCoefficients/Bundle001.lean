module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd Filter Topology
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (aff 1 x) = aff 1 (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.GeneralLinearGroup.map]

private theorem aff_comm {R : Type} [CommRing R] (x y : R) : aff 1 x * aff 1 y = aff 1 y * aff (1 : Rˣ) x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem aff_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem continuous_aff {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R => aff (1 : Rˣ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · change Continuous fun x : R => (!![(((1 : Rˣ)⁻¹ : Rˣ) : R), -((((1 : Rˣ)⁻¹ : Rˣ) : R) * x); 0, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem unip_eq {R : Type} [CommRing R] (x : BlockIx 2 1 → R) : unip x = aff 1 (x ⟨(0, 1), by decide⟩) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (1 + nilM x : Matrix (Fin 2) (Fin 2) R) i j = _
  fin_cases i <;> fin_cases j <;> simp [aff, nilM]

end UpperTheory.V.Af.Nf

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.autPer :
    UpperTheory.V.Af.Nf.AutPer := by
  intro φ hl ho g
  set t : GL (Fin 2) (Af ℚ) := Matrix.GeneralLinearGroup.map (pFin ℚ) g with ht
  have hc : Continuous fun x : Af ℚ => t⁻¹ * aff 1 x * t := (continuous_const.mul continuous_aff).mul continuous_const
  have h0 : t⁻¹ * aff 1 (0 : Af ℚ) * t ∈ {u | TR.finRep ℚ 2 u φ = φ} := by
    simp [aff_zero]
  obtain ⟨n, hn⟩ := (((hc.tendsto 0).comp (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ)).eventually
    (ho.mem_nhds h0)).exists
  refine ⟨n.factorial, n.factorial_pos, fun x => ?_⟩
  set N : ℕ := n.factorial with hN
  have hn' : ∀ g, φ.1 (g * finGL ℚ 2 (t⁻¹ * aff 1 (N : Af ℚ) * t)) = φ.1 g := fun g => congrFun (congrArg Subtype.val hn) g
  have e1 : g * finGL ℚ 2 (t⁻¹ * aff 1 (N : Af ℚ) * t) = finGL ℚ 2 (aff 1 (N : Af ℚ)) * g :=
    TR.ga_ext (by simp) (by simp [← ht, mul_assoc])
  have e2 : unip x * finGL ℚ 2 (aff 1 (N : Af ℚ)) = finGL ℚ 2 (aff 1 (N : Af ℚ)) * unip x :=
    TR.ga_ext (by simp) (by simp [unip_eq, map_aff, aff_comm])
  have e3 : ratGL ℚ 2 (aff 1 (N : ℚ)) = upR (aff 1 (N : ℝ)) * finGL ℚ 2 (aff 1 (N : Af ℚ)) := by
    rw [ratGL_eq, toR, toF, map_aff, map_aff, map_natCast, map_natCast]
  rw [← hn', ← hl (aff 1 (N : ℚ)) (unip x * g), e3, mul_assoc, mul_assoc, e1, mul_assoc, ← mul_assoc (unip x), e2, mul_assoc]
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af.Nf

private theorem memO {x : Af ℚ} :
    x ∈ Ohat ℚ ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), x v ∈ v.adicCompletionIntegers ℚ := by
  rw [Ohat, Subring.mem_iInf]
  rfl

private theorem int_of_integers (x : 𝓞 ℚ) : ∃ n : ℤ, (x : ℚ) = n :=
  ⟨Rat.ringOfIntegersEquiv x, (Rat.ringOfIntegersEquiv_apply_coe x).symm⟩

private theorem dense_int (M : ℕ) (hM : 1 ≤ M) (x : Af ℚ) (hx : x ∈ Ohat ℚ) :
    ∃ d : ℤ, ∃ y ∈ Ohat ℚ, x - d = M * y := by
  obtain ⟨r, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat ℚ M hM).2 x (memO.1 hx)
  obtain ⟨n, hn⟩ := int_of_integers r
  refine ⟨n, a, memO.2 ha, ?_⟩
  rw [e, hn, map_intCast, nsmul_eq_mul]
  ring

private theorem exists_den (y : Af ℚ) : ∃ N : ℕ, 1 ≤ N ∧ (N : Af ℚ) * y ∈ Ohat ℚ := by
  obtain ⟨r, a, ha, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat ℚ 1 one_pos).1 y
  refine ⟨r.den, r.den_pos, ?_⟩
  have h : (r.den : Af ℚ) * algebraMap ℚ (Af ℚ) r = (r.num : Af ℚ) := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, Rat.den_mul_eq_num, map_intCast]
  rw [e, mul_add, h, one_smul]
  exact add_mem (intCast_mem _ _) (mul_mem (natCast_mem _ _) (memO.2 ha))

private theorem class_one (y : (Af ℚ)ˣ) : ∃ (r : ℚˣ) (u : (Af ℚ)ˣ), 0 < (r : ℚ) ∧ IsZU u ∧
    y = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u := by
  classical
  obtain ⟨N, hN, ha⟩ := exists_den (y : Af ℚ)
  obtain ⟨M, hM, hb⟩ := exists_den ((y⁻¹ : (Af ℚ)ˣ) : Af ℚ)
  set a : Af ℚ := N * y with ha'
  set b : Af ℚ := M * ((y⁻¹ : (Af ℚ)ˣ) : Af ℚ) with hb'
  have hab : a * b = ((N * M : ℕ) : Af ℚ) := by
    rw [ha', hb', mul_mul_mul_comm, Units.mul_inv, mul_one, Nat.cast_mul]
  let I : Ideal ℤ :=
    { carrier := {n | ∃ w ∈ Ohat ℚ, (n : Af ℚ) = a * w}
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      add_mem' := by
        rintro m n ⟨w, hw, e⟩ ⟨w', hw', e'⟩
        exact ⟨w + w', add_mem hw hw', by rw [Int.cast_add, e, e', mul_add]⟩
      smul_mem' := by
        rintro c n ⟨w, hw, e⟩
        exact ⟨c * w, mul_mem (intCast_mem _ _) hw, by rw [smul_eq_mul, Int.cast_mul, e]; ring⟩ }
  obtain ⟨d₀, hd₀⟩ := (IsPrincipalIdealRing.principal I).principal
  have hI : I = Ideal.span {|d₀|} := by
    rw [hd₀, Ideal.submodule_span_eq, Ideal.span_singleton_abs]
  set d : ℤ := |d₀| with hd
  have hL : ((N * M : ℕ) : ℤ) ∈ I := ⟨b, hb, by rw [hab, Int.cast_natCast]⟩
  obtain ⟨w, hw, hdw⟩ : d ∈ I := hI ▸ Ideal.mem_span_singleton_self d
  obtain ⟨n, z, hz, hn⟩ := dense_int (N * M) (Nat.mul_pos hN hM) a ha
  have hnI : n ∈ I := ⟨1 - b * z, sub_mem (one_mem _) (mul_mem hb hz), by
    rw [← hab] at hn; linear_combination -hn⟩
  rw [hI, Ideal.mem_span_singleton] at hL hnI
  obtain ⟨l, hl⟩ := hL
  obtain ⟨k, hk⟩ := hnI
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, zero_mul, Nat.cast_eq_zero] at hl
    exact (Nat.mul_pos hN hM).ne' hl
  have hdpos : (0 : ℚ) < d := by exact_mod_cast lt_of_le_of_ne (abs_nonneg d₀) hd0.symm
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hl' : ((N * M : ℕ) : Af ℚ) = d * l := by
    rw [← Int.cast_natCast, hl, Int.cast_mul]
  have hau : a = d * ((k : Af ℚ) + l * z) := by
    rw [hk, hl', Int.cast_mul] at hn
    linear_combination hn
  have hdi : algebraMap ℚ (Af ℚ) (d : ℚ)⁻¹ * d = 1 := by
    rw [← map_intCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hdpos.ne', map_one]
  have hNi : algebraMap ℚ (Af ℚ) (N : ℚ)⁻¹ * N = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hNpos.ne', map_one]
  have huw : ((k : Af ℚ) + l * z) * w = 1 := by
    rw [hau] at hdw
    linear_combination (-algebraMap ℚ (Af ℚ) (d : ℚ)⁻¹) * hdw + (1 - ((k : Af ℚ) + l * z) * w) * hdi
  refine ⟨Units.mk0 (d / N) (div_pos hdpos hNpos).ne', ⟨(k : Af ℚ) + l * z, w, huw, by rw [mul_comm, huw]⟩,
    div_pos hdpos hNpos, ⟨add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hz), hw⟩, Units.ext ?_⟩
  change (y : Af ℚ) = algebraMap ℚ (Af ℚ) ((d : ℚ) / N) * ((k : Af ℚ) + l * z)
  rw [div_eq_mul_inv, map_mul, map_intCast]
  rw [ha'] at hau
  linear_combination (algebraMap ℚ (Af ℚ) (N : ℚ)⁻¹) * hau - (y : Af ℚ) * hNi

private theorem val_le (K : Type) [Field K] [NumberField K] (r : K) (v : HeightOneSpectrum (𝓞 K))
    (h : algebraMap K (Af K) r v ∈ v.adicCompletionIntegers K) : v.valuation K r ≤ 1 :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r).symm.trans_le h

private theorem rat_int (r : ℚ) (hr : algebraMap ℚ (Af ℚ) r ∈ Ohat ℚ) : ∃ n : ℤ, r = n := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ r fun v =>
    val_le ℚ r v (memO.1 hr v)
  obtain ⟨n, hn⟩ := int_of_integers x
  exact ⟨n, hx.symm.trans hn⟩

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.ratAd :
    UpperTheory.V.Af.Nf.RatAd :=
  ⟨UpperTheory.V.Af.Nf.class_one, UpperTheory.V.Af.Nf.dense_int, UpperTheory.V.Af.Nf.rat_int⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

private theorem ord_diff (w : HeightOneSpectrum (𝓞 ℚ)) : ordI w (differentIdeal ℤ (𝓞 ℚ)) = 0 := by
  have h : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), discr_rat]; rfl
  rw [h, ordI, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one, Associates.count_zero w.associates_irreducible]

private theorem eq_of_ord {I J : Ideal (𝓞 ℚ)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ w, ordI w I = ordI w J) : I = J := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI, ← Ideal.finprod_heightOneSpectrum_factorization hJ]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (h w)

private theorem val_unit {u : (Af ℚ)ˣ} (hu : IsZU u) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (pLoc ℚ w (u : Af ℚ)) = 1 := by
  have h1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.1 w
  have h2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.2 w
  have h3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm h1 ?_
  calc 1 = _ := h3.symm
    _ ≤ Valued.v (pLoc ℚ w (u : Af ℚ)) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

private theorem genD_iff (q : ℚ) {u : (Af ℚ)ˣ} (hu : IsZU u) (𝔪 : Ideal (𝓞 ℚ)) :
    GenD (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) 𝔪 ↔
      𝔪 ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), w.valuation ℚ q = WithZero.exp (-(ordI w 𝔪 : ℤ)) := by
  refine and_congr_right fun _ => forall_congr' fun w => ?_
  have h : Valued.v (pLoc ℚ w (algebraMap ℚ (Af ℚ) q)) = w.valuation ℚ q :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q
  rw [map_mul, map_mul, val_unit hu, mul_one, h, ord_diff, Nat.cast_zero, zero_sub]

private theorem val_nat {n : ℕ} (hn : n ≠ 0) (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ (n : ℚ) = WithZero.exp (-(ordI w (Ideal.span {(n : 𝓞 ℚ)}) : ℤ)) := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) ℚ) n, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg w (Nat.cast_ne_zero.2 hn)]
  rfl

theorem UpperTheory.V.Af.Nf.coefAt :
    UpperTheory.V.Af.Nf.CoefAt := by
  intro a q hq u hu
  by_cases hd : q.den = 1
  · rw [if_pos hd]
    have hnum : 0 < q.num := Rat.num_pos.2 hq
    have hn : q.num.toNat ≠ 0 := by omega
    have hqn : q = (q.num.toNat : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]
      exact ((Rat.den_eq_one_iff q).1 hd).symm
    have hb : Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hn
    have hv : ∀ w : HeightOneSpectrum (𝓞 ℚ),
        w.valuation ℚ q = WithZero.exp (-(ordI w (Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)}) : ℤ)) := fun w => by
      rw [← val_nat hn w, ← hqn]
    have hex : ∃ 𝔪, GenD (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) 𝔪 := ⟨_, (genD_iff q hu _).2 ⟨hb, hv⟩⟩
    obtain ⟨h1, h2⟩ := (genD_iff q hu _).1 hex.choose_spec
    have he : hex.choose = Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)} := eq_of_ord h1 hb fun w => by
      have := WithZero.exp_injective ((h2 w).symm.trans (hv w))
      omega
    rw [UpperTheory.V.Sd.coefAt, dite_eq_left hex, he, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  · rw [if_neg hd, UpperTheory.V.Sd.coefAt, dite_eq_right]
    rintro ⟨𝔪, h⟩
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ q fun w => by
      rw [((genD_iff q hu _).1 h).2 w, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    obtain ⟨m, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective r
    apply hd
    rw [← hr, eq_intCast Rat.ringOfIntegersEquiv.symm m, map_intCast]
    rfl
end

section

open UpperHalfPlane hiding I
open scoped Manifold

namespace UpperTheory.V.Af.Nf

private noncomputable def cR (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i)

private noncomputable def cC (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cR i j)

private theorem cR_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cR i j x = x i j := rfl
private theorem cC_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cC i j x = (x i j : ℂ) := rfl

private theorem key (k : ℕ) (F : ℂ → ℂ) (F' : ℂ) (hF : HasDerivAt F F' Complex.I) (x0 : Fin 2 → Fin 2 → ℝ)
    (h00 : x0 0 0 = 1) (h01 : x0 0 1 = 0) (h10 : x0 1 0 = 0) (h11 : x0 1 1 = 1) :
    ∃ L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ,
      HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ =>
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) *
          F (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹)) L x0 ∧
      ∀ v : Fin 2 → Fin 2 → ℝ, L v = (k : ℂ) / 2 * (v 0 0 + v 1 1) * F Complex.I - k * (v 1 0 * Complex.I + v 1 1) * F Complex.I +
        (v 0 0 * Complex.I + v 0 1 + v 1 0 - v 1 1 * Complex.I) * F' := by
  have r : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => x i j) (cR i j) x0 := fun i j => (cR i j).hasFDerivAt
  have c : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => (x i j : ℂ)) (cC i j) x0 := fun i j => (cC i j).hasFDerivAt
  have hd := ((r 0 0).fun_mul (r 1 1)).fun_sub ((r 0 1).fun_mul (r 1 0))
  have hd2 := hd.rpow_const (p := (k : ℝ) / 2) (Or.inl (by simp [h00, h01, h10, h11]))
  have hd3 := Complex.ofRealCLM.hasFDerivAt.comp x0 hd2
  have hden := ((c 1 0).mul_const Complex.I).fun_add (c 1 1)
  have hnum := ((c 0 0).mul_const Complex.I).fun_add (c 0 1)
  have hne : (x0 1 0 : ℂ) * Complex.I + x0 1 1 ≠ 0 := by simp [h10, h11]
  have hz := (hasDerivAt_zpow (-(k : ℤ)) _ (Or.inl hne)).comp_hasFDerivAt x0 hden
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt x0 hden
  have hq := hnum.fun_mul hi
  have hF2 : HasDerivAt F F' (((x0 0 0 : ℂ) * Complex.I + x0 0 1) * ((x0 1 0 : ℂ) * Complex.I + x0 1 1)⁻¹) := by
    simpa [h00, h01, h10, h11] using hF
  have hc := hF2.comp_hasFDerivAt x0 hq
  refine ⟨_, (hd3.fun_mul hz).fun_mul hc, fun v => ?_⟩
  simp [h00, h01, h10, h11, cR_apply, cC_apply]
  linear_combination (-(v 1 0 : ℂ) * F') * Complex.I_mul_I

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.archDer :
    UpperTheory.V.Af.Nf.ArchDer := by
  intro k f hf D hD
  have hF : DifferentiableAt ℂ (f ∘ ofComplex) Complex.I :=
    (UpperHalfPlane.mdifferentiable_iff.1 hf).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simp))
  obtain ⟨L, hL, hv⟩ := key k (f ∘ ofComplex) _ hF.hasDerivAt (Matrix.of.symm 1) (by simp) (by simp) (by simp) (by simp)
  have hpos : ∀ᶠ x : Fin 2 → Fin 2 → ℝ in nhds (Matrix.of.symm 1), 0 < x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
    have hc : Continuous fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0 := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (by simp)
  have hA : HasFDerivAt (arch k f) L (Matrix.of.symm 1) := by
    refine hL.congr_of_eventuallyEq (hpos.mono fun x hx => ?_)
    simp only [arch, nsl, Matrix.det_fin_two, Matrix.of_apply, abs_of_pos hx, sign_pos hx, Function.comp, coe_I,
      div_eq_mul_inv]
    simp
  have hI : (f ∘ ofComplex) Complex.I = f UpperHalfPlane.I := by
    rw [← coe_I, Function.comp, ofComplex_apply]
  simp only [hD, hA.fderiv, hv, hI]
  simp [Matrix.single]
  refine ⟨Or.inl (mul_comm _ _), ?_⟩
  linear_combination (k * f UpperHalfPlane.I) * Complex.I_mul_I
end

section

open MeasureTheory
open scoped Pointwise

theorem UpperTheory.V.Af.Nf.avgZero :
    UpperTheory.V.Af.Nf.AvgZero := by
  intro G _ _ _ _ _ _ _ Γ _ μ 𝓕 hμ h𝓕 ψ hψ hinv e he N hN havg
  by_cases hint : IntegrableOn ψ 𝓕 μ
  swap
  · exact integral_undef hint
  have hΓ : ∀ (g : Γ) (x : G), ψ (g +ᵥ x) = ψ x := fun g x => hinv g g.2 x
  have hF : ∀ a : G, IsAddFundamentalDomain Γ ((fun x => a + x) '' 𝓕) μ := fun a => h𝓕.vadd_of_comm a
  have hmp : ∀ a : G, MeasurePreserving (fun x => a + x) μ μ := fun a => measurePreserving_add_left μ a
  have hem : ∀ a : G, MeasurableEmbedding (fun x : G => a + x) := fun a => measurableEmbedding_addLeft a
  have h1 : ∀ a : G, ∫ x in 𝓕, ψ (a + x) ∂μ = ∫ x in 𝓕, ψ x ∂μ := fun a => by
    rw [← (hmp a).setIntegral_image_emb (hem a) ψ 𝓕]
    exact (hF a).setIntegral_eq h𝓕 hΓ
  have h2 : ∀ a : G, ∫ x in 𝓕, ‖ψ (a + x)‖ ∂μ = ∫ x in 𝓕, ‖ψ x‖ ∂μ := fun a => by
    rw [← (hmp a).setIntegral_image_emb (hem a) (fun x => ‖ψ x‖) 𝓕]
    exact (hF a).setIntegral_eq h𝓕 fun g x => by rw [hΓ]
  have h3 : ∀ a : G, IntegrableOn (fun x => ψ (a + x)) 𝓕 μ := fun a =>
    ((hmp a).integrableOn_image (hem a)).1 (((hF a).integrableOn_iff h𝓕 hΓ).2 hint)
  have hc : Continuous (Function.uncurry fun (t : ℝ) (x : G) => ψ (e t + x)) :=
    hψ.comp ((he.comp continuous_fst).add continuous_snd)
  have hI : Integrable (Function.uncurry fun (t : ℝ) (x : G) => ψ (e t + x))
      ((volume.restrict (Set.Ioc (0 : ℝ) N)).prod (μ.restrict 𝓕)) := by
    rw [integrable_prod_iff hc.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun t => h3 (e t), ?_⟩
    simp only [Function.uncurry_apply_pair, h2]
    exact integrable_const _
  have hs := integral_integral_swap hI
  simp only [h1, ← intervalIntegral.integral_of_le hN.le, havg, integral_zero, intervalIntegral.integral_const,
    sub_zero, smul_eq_zero, hN.ne', false_or] at hs
  exact hs
end

section

open UpperHalfPlane

namespace UpperTheory.V.Af.Nf

end UpperTheory.V.Af.Nf

private theorem lower_row_mul_add_ne_zero_of_det_ne_zero (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (w : ℍ) :
    (x 1 0 : ℂ) * (w : ℂ) + (x 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with h1 | h1
  · apply hx
    rw [Matrix.det_fin_two]
    simp [h1] at hre
    simp [h1, hre]
  · exact absurd h1 w.im_pos.ne'

private theorem im_mobius_pos_of_det_pos (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) (z : ℍ) :
    0 < (((y 0 0 : ℂ) * z + y 0 1) / ((y 1 0 : ℂ) * z + y 1 1)).im := by
  have hj := lower_row_mul_add_ne_zero_of_det_ne_zero y hy.ne' z
  rw [Complex.div_im]
  have hn : 0 < Complex.normSq ((y 1 0 : ℂ) * z + y 1 1) := Complex.normSq_pos.mpr hj
  rw [← sub_div]
  apply div_pos _ hn
  have hd := hy
  rw [Matrix.det_fin_two] at hd
  simp
  nlinarith [z.im_pos]

open UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.nslMul :
    UpperTheory.V.Af.Nf.NslMul := by
  intro k f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    funext z
    have hjy := lower_row_mul_add_ne_zero_of_det_ne_zero y hy.ne' z
    have hm := im_mobius_pos_of_det_pos y hy z
    set m := ((y 0 0 : ℂ) * z + y 0 1) / ((y 1 0 : ℂ) * z + y 1 1) with hmdef
    simp only [nsl]
    rw [sign_pos hy, Matrix.det_mul, sign_mul, sign_pos hy, mul_one, abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    simp only [SignType.coe_one, Int.cast_one, Complex.ofReal_one, one_mul]
    rw [← hmdef, UpperHalfPlane.ofComplex_apply_of_im_pos hm]
    simp only [UpperHalfPlane.coe_mk, Matrix.mul_apply, Fin.sum_univ_two]
    have hJ : ((↑(x 1 0 * y 0 0 + x 1 1 * y 1 0) : ℂ) * z + ↑(x 1 0 * y 0 1 + x 1 1 * y 1 1)) =
        ((x 1 0 : ℂ) * m + x 1 1) * ((y 1 0 : ℂ) * z + y 1 1) := by
      rw [hmdef, add_mul, mul_assoc, div_mul_cancel₀ _ hjy]
      push_cast
      ring
    have hN : ((↑(x 0 0 * y 0 0 + x 0 1 * y 1 0) : ℂ) * z + ↑(x 0 0 * y 0 1 + x 0 1 * y 1 1)) =
        ((x 0 0 : ℂ) * m + x 0 1) * ((y 1 0 : ℂ) * z + y 1 1) := by
      rw [hmdef, add_mul, mul_assoc, div_mul_cancel₀ _ hjy]
      push_cast
      ring
    rw [hJ, hN, mul_div_mul_right _ _ hjy, mul_zpow]
    push_cast
    ring
  · intro x
    funext z
    simp only [nsl, eps, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    have h1 : -(x 0 0 * x 1 1) + x 0 1 * x 1 0 = -(x 0 0 * x 1 1 - x 0 1 * x 1 0) := by ring
    rw [h1, abs_neg, Left.sign_neg]
    congr 3
    push_cast
    ring
  · intro t x ht
    funext z
    simp only [nsl, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
    have h1 : t * x 0 0 * (t * x 1 1) - t * x 0 1 * (t * x 1 0) =
        t ^ 2 * (x 0 0 * x 1 1 - x 0 1 * x 1 0) := by ring
    rw [h1]
    set d := x 0 0 * x 1 1 - x 0 1 * x 1 0
    have h2 : SignType.sign (t ^ 2 * d) = SignType.sign d := by
      rw [sign_mul, sign_pos (by positivity), one_mul]
    have h3 : |t ^ 2 * d| ^ ((k : ℝ) / 2) = t ^ k * |d| ^ ((k : ℝ) / 2) := by
      rw [abs_mul, Real.mul_rpow (by positivity) (abs_nonneg _),
        abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
      congr 1
      rw [show (t ^ 2 : ℝ) = t ^ (2:ℝ) by norm_cast, ← Real.rpow_mul ht.le,
        show (2:ℝ) * (k / 2) = k by ring, Real.rpow_natCast]
    have hj : ((↑(t * x 1 0) : ℂ) * ↑z + ↑(t * x 1 1)) = (t : ℂ) * ((x 1 0 : ℂ) * z + x 1 1) := by
      push_cast
      ring
    have hn : ((↑(t * x 0 0) : ℂ) * ↑z + ↑(t * x 0 1)) = (t : ℂ) * ((x 0 0 : ℂ) * z + x 0 1) := by
      push_cast
      ring
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [h2, h3, hj, hn, mul_div_mul_left _ _ ht']
    congr 1
    push_cast
    rw [mul_zpow, zpow_neg, zpow_neg, zpow_natCast]
    field_simp
  · intro c x
    funext z
    simp only [nsl, Pi.smul_apply, smul_eq_mul]
    ring
end
