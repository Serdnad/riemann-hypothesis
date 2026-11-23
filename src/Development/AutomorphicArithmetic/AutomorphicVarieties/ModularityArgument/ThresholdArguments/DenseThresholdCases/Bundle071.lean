module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.HasHTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle067
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle028
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle063
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CongNum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobeniusTraceCountBoundOfCmEigensystemCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformOfAdmissibleTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PotOfPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle068
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.PowMemOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Desc.P
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.P.dense_threshold_bc_of_prop : _root_.UpperTheory.V.Z.J.D.BcOfAlt := by
  intro H E Ω _ _ _ _ _ _ hE l _ hl ι n hn σ hσ R hRc hRi hR
  obtain ⟨r, HT, hc, hs, -, -, hL, -, hQ⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl ι n hn σ hσ
  have hss : Formalism.MainNotions.N.IsSSRep R := by
    intro M hM
    rcases hRi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hRi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have hunram : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsUnramU σ w := by
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    let L : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at *
          rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at *
          conv_lhs => rw [← ha]
          rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel,
            map_one, one_apply_eq_self] }
    have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary
      E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hAway : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.mpr (not_not.1 hw)
  have hAgree : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      IsSplitAt w → ∃ B, FrobEig ι R w B ∧ FrobEig ι r w B := by
    filter_upwards [hR, hAway, hunram] with w h1 hw hu hsp
    obtain ⟨τ, -, h2, h3⟩ := GlobalTheory.DefU.exists_locComp_split E n ⟨σ, hσ⟩ w hsp
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h3.1 hu)
    obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
    have k : _root_.UpperTheory.V.Z.Win.LocGlobT ι r w τ := (hL w hsp τ h2).1
    exact ⟨_, _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n R hRc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (h1 hsp τ h2) hw),
      _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n r hc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT k hw)⟩
  have hiso : RepIso R r := by
    have hChar : ∀ g : G E Ω, (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
        (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
      intro g
      ext i
      have hRcoeff : Continuous fun g : G E Ω =>
          (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hRc.comp continuous_inv))
      have hrcoeff : Continuous fun g : G E Ω =>
          (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hc.comp continuous_inv))
      refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob
        (Filter.eventually_cofinite.1 hAgree) hRcoeff hrcoeff ?_) g
      intro w hw hd A hA s hFrob
      have hSplit := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
      obtain ⟨B, hB, hB'⟩ := not_not.1 hw hSplit
      have h := ((hB A hA).2 s hFrob).trans ((hB' A hA).2 s hFrob).symm
      have h' := Polynomial.map_injective ι.toRingHom ι.injective h
      rw [h']
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix R r hss hs
      (fun g => by simpa only [inv_inv] using hChar g⁻¹)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hirr : IsIrr r := by
    obtain ⟨P, hP⟩ := hiso
    refine ⟨hRi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T : (Fin n → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) :=
      (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hInv : Formalism.MainNotions.N.IsInv R (M.comap T.toLinearMap) := by
      intro g v hv
      have hComm : T ((R g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) =
          (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) := by
        rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
        simp only [← Matrix.GeneralLinearGroup.coe_mul, mul_assoc, inv_mul_cancel, mul_one]
      show T _ ∈ M
      rw [hComm]
      exact hM g _ hv
    have hMap := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hRi.2.2 _ le_top hInv with h | h
    · left
      rw [hMap, h, Submodule.map_bot]
    · right
      rw [hMap, h, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, h1, h2, -, h4, h5, h6⟩ := hQ hirr
  refine ⟨π, h1, h2, ?_, h4, h5⟩
  filter_upwards [(_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).2] with w ⟨B, hB⟩ hsp
  obtain ⟨τ, hτ⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact ⟨τ, B, h6 w hsp τ hτ, ((_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).1 w τ hτ B).1 hB, hB⟩
end
end

section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing



section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br
namespace UpperTheory.GalN.V.Win.N
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.CongNum
section
private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have h : normV w = Ideal.absNorm w.asIdeal := (Ideal.absNorm_eq_natCard w.asIdeal).symm
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [h]
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top
private theorem est {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) {t z₁ z₂ z₃ : ℂ} (h1 : ‖z₁‖ = 1) (h2 : ‖z₂‖ = 1) (h3 : ‖z₃‖ = 1)
    (ht : ‖t‖ ≤ 3 * (Real.sqrt p * (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) + (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) :
    t - eis4 p e z₁ z₂ z₃ ≠ 0 ∧ ‖t - eis4 p e z₁ z₂ z₃‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2) with hx
  set y : ℝ := (p : ℝ) ^ e with hy
  have hx0 : 0 ≤ x := by positivity
  have hxx : x * x = p * y := by
    rw [hx, ← Real.rpow_add (by linarith), hy, ← pow_succ', ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hy2 : (p : ℝ) ^ 2 ≤ y := pow_le_pow_right₀ (by linarith) he
  have hy0 : 0 ≤ y := by positivity
  have hxy : 2 * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0, mul_nonneg (show (0:ℝ) ≤ p - 4 by linarith) (mul_nonneg (show (0:ℝ) ≤ p by linarith) hy0)]
  have hsx : Real.sqrt p * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    rw [mul_pow, Real.sq_sqrt (by linarith), pow_two x, hxx]
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0]
  replace ht : ‖t‖ ≤ 7 / 2 * y := by linarith
  have n1 : ‖(p : ℂ) ^ (e + 1) * z₁‖ = p * y := by simp [h1, hy, pow_succ']
  have n2 : ‖(p : ℂ) ^ e * z₂‖ = y := by simp [h2, hy]
  have n3 : ‖(p : ℂ) * z₃‖ = p := by simp [h3]
  have hr : ‖t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)‖ ≤ 7 / 2 * y + (y + p + 1) := by
    refine (norm_sub_le _ _).trans (add_le_add ht ?_)
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, ← n2, ← n3]
    have := norm_add_le ((p : ℂ) ^ e * z₂) ((p : ℂ) * z₃)
    simpa using this
  have hE : t - eis4 p e z₁ z₂ z₃ = (t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)) - (p : ℂ) ^ (e + 1) * z₁ := by
    rw [eis4]; ring
  have hlt : 7 / 2 * y + (y + p + 1) < p * y := by nlinarith
  constructor
  · intro h0
    rw [hE, sub_eq_zero] at h0
    rw [h0, n1] at hr
    linarith
  · rw [hE]
    refine (norm_sub_le _ _).trans ?_
    rw [n1, mul_comm 2, pow_mul, pow_succ' (p : ℝ) e, ← hy]
    have : (2 : ℝ) ≤ p * y := by nlinarith
    nlinarith
private theorem size {c A M e N d p : ℕ} (hN : N ≤ c * (M * (e + 1 + 1)) ^ A) (hM : 1 ≤ M) (hp : 5 ≤ p) :
    ((N * d : ℕ) : ℝ) * Real.log ((p : ℝ) ^ (2 * (e + 1))) ≤
      ((c * 2 ^ A * 2 : ℕ) : ℝ) * d * ((M : ℝ) * (e + 1)) ^ (A + 1) * Real.log p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h1 : N * d * (2 * (e + 1)) ≤ c * 2 ^ A * 2 * d * (M * (e + 1)) ^ (A + 1) := by
    have a1 : (M * (e + 1 + 1)) ^ A ≤ 2 ^ A * (M * (e + 1)) ^ A := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) _
    have a2 : e + 1 ≤ M * (e + 1) := Nat.le_mul_of_pos_left _ hM
    calc N * d * (2 * (e + 1)) ≤ c * (2 ^ A * (M * (e + 1)) ^ A) * d * (2 * (M * (e + 1))) := by
          gcongr
          exact hN.trans (by gcongr)
      _ = _ := by ring
  rw [Real.log_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  exact_mod_cast h1
end
open UpperTheory.V.Af in
theorem number_sp4_of_admissible_to_admissible_n :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.LevelPNAlt → _root_.UpperTheory.GalN.V.AdmResNAlt →
    (∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin 4 → ℤ) (wt : ℤ)
      (r : G ℚ Ω →* GL (Fin 4) (Qbar l)), _root_.UpperTheory.V.Af.AdmRAlt ι M m wt r → _root_.UpperTheory.GalN.V.AdmRNAlt ι M m wt r) →
    _root_.UpperTheory.V.Af.NumberSp4Alt := by
  intro hP hLP hA hR
  obtain ⟨c, A, hc⟩ := _root_.UpperTheory.GalN.V.Win.N.countQ_alt hP hLP hA 4 (by norm_num)
  refine ⟨c * 2 ^ A * 2, A + 1, fun e he M hM p w hp hw h5 hpM k hk z₁ z₂ z₃ h1 h2 h3 => ?_⟩
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨D, hD, hcl⟩ := hc ![(e : ℤ) + 1, e, 1, 0] (e + 1)
    (by
      rw [Fin.strictAnti_iff_succ_lt]
      intro i; fin_cases i <;> simp <;> omega)
    (by intro i; fin_cases i <;> simp [Fin.rev] <;> omega) (e + 1)
    (by intro i; fin_cases i <;> simp [abs_le] <;> omega) M hM p w hp hw hpM
  haveI := D.fin
  letI := Fintype.ofFinite D.S
  let f : D.S × (ZMod k)ˣ → ℂ := fun x =>
    (D.β x.1).sum - eis4 p e (z₁ ^ (x.2 : ZMod k).val) (z₂ ^ (x.2 : ZMod k).val) (z₃ ^ (x.2 : ZMod k).val)
  have hzi : ∀ z : ℂ, z ^ k = 1 → IsIntegral ℤ z := fun z hz => IsIntegral.of_pow hk (hz ▸ isIntegral_one)
  have hzn : ∀ z : ℂ, z ^ k = 1 → ∀ a : ℕ, ‖z ^ a‖ = 1 := fun z hz a => by
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hz hk.ne', one_pow]
  have hi : ∀ x, IsIntegral ℤ (f x) := fun x => by
    have hpi : IsIntegral ℤ (p : ℂ) := isIntegral_natCast p
    refine IsIntegral.sub (IsIntegral.multiset_sum fun b hb => ?_) ?_
    · simpa using D.int 0 (by intro i; fin_cases i <;> simp <;> omega) x.1 b hb
    · exact ((((hpi.pow _).mul ((hzi _ h1).pow _)).add ((hpi.pow _).mul ((hzi _ h2).pow _))).add
        (hpi.mul ((hzi _ h3).pow _))).add isIntegral_one
  have hconj : ∀ σ : ℂ ≃+* ℂ, ∃ u : D.S × (ZMod k)ˣ ≃ D.S × (ZMod k)ˣ, ∀ x, f (u x) = σ (f x) := fun σ => by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨b, hb⟩ := exists_unit_pow k σ
    refine ⟨u.prodCongr (Equiv.mulLeft b), fun x => ?_⟩
    simp only [f, eis4, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hu, Equiv.coe_mulLeft, Units.val_mul, map_sub,
      map_add, map_mul, map_pow, map_one, map_natCast, map_multiset_sum, hb _ h1, hb _ h2, hb _ h3,
      pow_val_mul h1, pow_val_mul h2, pow_val_mul h3]
  have hest : ∀ x, f x ≠ 0 ∧ ‖f x‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := fun x => by
    refine est h5 he (hzn _ h1 _) (hzn _ h2 _) (hzn _ h3 _) ?_
    simpa only [Nat.cast_ofNat] using WinC.sum_le (D.pure x.1) (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _) (n := 3) (D.card _)
  obtain ⟨NN, hNN⟩ := exists_int_prod f hi hconj
  obtain ⟨h0, hlog⟩ := log_abs_le f NN hNN (fun x => (hest x).1) _ fun x => (hest x).2
  refine ⟨NN, h0, hlog.trans ?_, fun l _ hl2 hlp Ω _ _ _ ι B hB σ hσ X hX hX' => ?_⟩
  · rw [Fintype.card_prod, ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact size hD hM h5
  replace hX := fun r hr => hR Ω l ι _ _ _ r (hX r hr)
  obtain ⟨cl, hinj, hfr⟩ := hcl l hl2 hlp Ω ι
  have hone : ∀ z : ℂ, z ^ k = 1 → z ^ (((1 : (ZMod k)ˣ) : ZMod k)).val = z := fun z hz => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  have key : ∀ (r) (hr : r ∈ X), (r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace - ι.symm (eis4 p e z₁ z₂ z₃) =
      ι.symm (f (cl ⟨r, hX r hr⟩, 1)) := fun r hr => by
    have h := (hfr ⟨r, hX r hr⟩ B hB).2 σ (by rwa [normV_rat hp w hw])
    rw [map_inv] at h
    rw [trace_eq_sum_of_inv ι _ _ h]
    simp only [f, hone _ h1, hone _ h2, hone _ h3, map_sub]
  refine ⟨fun r hr h => ?_, ?_⟩
  · have := key r hr
    rw [h, sub_self, eq_comm, map_eq_zero_iff _ ι.symm.injective] at this
    exact (hest _).1 this
  · have := norm_le_prod ι f hi NN hNN (fun r : X => (cl ⟨r.1, hX r.1 r.2⟩, (1 : (ZMod k)ˣ))) fun r r' h =>
      Subtype.ext (hX' _ r.2 _ r'.2 (hinj _ _ (congrArg Prod.fst h)))
    refine this.trans_eq ?_
    rw [← Finset.prod_coe_sort X]
    exact Finset.prod_congr rfl fun r _ => by rw [key r.1 r.2]
end
end UpperTheory.GalN.V.Win.N
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
private theorem isGSp_map_coefficients {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) :
    IsGSp (f ν) (g.map f) := by
  have a : adj (g.map f) = (adj g).map f := by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  unfold IsGSp at h ⊢
  rw [a, ← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]
theorem UpperTheory.V.Th.local_zero_of_modular_p :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
        X.LocZero J (y : X.A →+* PadicAlgCl l) := by
  intro hU hA Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ y hs q hq hqy
  obtain ⟨w, κ, π, a, k, hgap, hw, hκ, hk, hev, hκw, hreg, hatt⟩ := hs.aut
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Even (w 0 + n) := ⟨(w 0).natAbs, by
    rcases Int.natAbs_eq (w 0) with e | e <;> exact Int.even_iff.2 (by omega)⟩
  obtain ⟨d0, h0, e0⟩ := hgap 0
  obtain ⟨d1, h1, e1⟩ := hgap 1
  obtain ⟨d2, h2, e2⟩ := hgap 2
  replace e0 : w 0 = w 1 + 2 * d0 := e0
  replace e1 : w 1 = w 2 + 2 * d1 := e1
  replace e2 : w 2 = w 3 + 2 * d2 := e2
  rw [Int.even_iff] at hn hev
  obtain ⟨φ', hφ'⟩ := (_root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link hU D T hF hD c' h K X n).2 B
  obtain ⟨m, hm, hmk⟩ := Pt.ptWts K X B n φ' hφ' y w (fun i => Int.even_iff.2 (by fin_cases i <;> simp <;> omega)) hw
  have hg : ∀ v i j, i < j → m v j + 2 ≤ m v i := fun v i j hij => by
    have := hm v i j
    fin_cases i <;> fin_cases j <;> simp at hij this ⊢ <;> omega
  obtain ⟨hi, hi'⟩ := Pt.ptIrr K n _ hs.irr
  have hc := Pt.rho_cont K n (Pt.pt_cont X y hi)
  have hrep : (Link.pt φ' y).IsRep (K.rhoQ n _) := auRep D T c' h K X B n φ' hφ' y _ fun _ => rfl
  have hmul : ∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g))))
      ((X.P.map (y : X.A →+* PadicAlgCl l)).r g) := fun g => by
    rw [← y.commutes]
    exact isGSp_map_coefficients (y : X.A →+* PadicAlgCl l) (X.pair.mult g)
  have hunr := Pt.ptUnr K n (X.P.map (y : X.A →+* PadicAlgCl l)).r fun g hg => by
    change (y : X.A →+* PadicAlgCl l).mapMatrix (X.P.r g) = 1
    rw [X.pair.kill g hg, map_one]
  have hfl := Pt.ptFlag K X B n φ' hφ' y
  obtain ⟨Pp, hPp⟩ := Pt.ptPair K n _ hmul
  have haut := _root_.UpperTheory.V.Z.Win.Birth.ptAutR'_alt hU.pr K n ι _ hmul κ π a k hκ hk (Int.even_iff.2 (by omega)) hκw hreg hatt
    (Z.ImaginaryQuadraticEtaCharacter.potOfPair l T.L Ω K.s 4 _ _ Pp hPp _ m hg hfl hmk)
  have hJx := _root_.UpperTheory.V.Ws.Pt.point_representation_weights hU.pr l T.L Ω K.s K.V c' 4 K.r B ι J₀ hM.pt _ _ m (by norm_num) (by norm_num) hrep hc haut hunr hg hfl hmk
  rw [← _root_.UpperTheory.V.Ws.hida_modular_ideal_map hU D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ', Ideal.map_le_iff_le_comap]
  exact _root_.UpperTheory.V.Th.eigenbasis_rank_four hU hA l T.L Ω K.s K.V K.hV K.noMu c' K.large K.r B Λ ι J₀ hM.toHidaProps K.v0 (P1.condC D T hF hD c' h K)
    (P1.condD D T hF hD c' h K) _ _ m hJx hrep hc haut hunr hi' hg hfl hmk
    _ (hq.comap φ') fun b hb => hqy _ hb
end
end
