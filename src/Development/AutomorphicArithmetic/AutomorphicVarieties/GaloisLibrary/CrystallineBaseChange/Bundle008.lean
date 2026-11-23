module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle001
public import GroundTheory.AutomorphicForms.GL2Classical.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd Matrix CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

private theorem loc_unit {R : Type} [CommRing R] [IsLocalRing R] {d N : R} (h : IsCoprime d N) : ∃ y, IsUnit (d + N * y) := by
  by_cases hd : IsUnit d
  · exact ⟨0, by simpa using hd⟩
  · obtain ⟨a, b, e⟩ := h
    have hN : IsUnit N := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one e with h | h
      · exact absurd (isUnit_of_mul_isUnit_right h) hd
      · exact isUnit_of_mul_isUnit_right h
    refine ⟨1, ?_⟩
    have : IsUnit ((d + N * 1) + -d) := by simpa using hN
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h | h
    · exact h
    · exact absurd h.neg (by simpa using hd)

private noncomputable def jj : (∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) →+* Af ℚ where
  toFun x := ⟨fun v => (x v : v.adicCompletion ℚ), Filter.Eventually.of_forall fun v => (x v).2⟩
  map_one' := FiniteAdeleRing.ext _ fun _ => rfl
  map_mul' _ _ := FiniteAdeleRing.ext _ fun _ => rfl
  map_zero' := FiniteAdeleRing.ext _ fun _ => rfl
  map_add' _ _ := FiniteAdeleRing.ext _ fun _ => rfl

private theorem jj_mem (x) : jj x ∈ Ohat ℚ := by
  rw [Ohat, Subring.mem_iInf]
  exact fun v => (x v).2

private theorem ex_unit {d : ℤ} {N : ℕ} (h : IsCoprime d (N : ℤ)) :
    ∃ u, IsZU u ∧ ∃ y ∈ Ohat ℚ, (u : Af ℚ) - d = N * y := by
  choose y hy using fun v : HeightOneSpectrum (𝓞 ℚ) =>
    loc_unit (h.map (Int.castRingHom (v.adicCompletionIntegers ℚ)))
  have hu : IsUnit ((d : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) + N * y) :=
    Pi.isUnit_iff.2 fun v => by simpa using hy v
  obtain ⟨w, hw⟩ := hu
  refine ⟨Units.map jj.toMonoidHom w, ⟨jj_mem _, jj_mem _⟩, jj y, jj_mem _, ?_⟩
  change jj w - d = _
  rw [hw]
  simp

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem ex_K {N : ℕ} (δ : SL(2, ℤ)) (hδ0 : δ ∈ Gamma0 N) : ∃ u, IsZU u ∧
    (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ K1G N ∧
    ∃ y ∈ Ohat ℚ, (u : Af ℚ) - (δ 1 1 : ℤ) = N * y := by
  obtain ⟨c, hc⟩ : (N : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hδ0)
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  obtain ⟨u, hu, y, hy, hd⟩ := ex_unit (d := δ 1 1) (N := N) ⟨δ 0 0, -(δ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩
  have hI : ∀ n : ℤ, (n : Af ℚ) ∈ Ohat ℚ := fun n => intCast_mem _ n
  have hδ : ∀ (δ : SL(2, ℤ)) a b, (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ)).val a b = ((δ a b : ℤ) : Af ℚ) := by
    intro δ a b
    show algebraMap ℚ (Af ℚ) (algebraMap ℤ ℚ (δ a b)) = _
    simp
  have e1 : ∀ a b, ((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u).val a b
      = (((δ⁻¹ : SL(2, ℤ)) a b : ℤ) : Af ℚ) * u := by
    intro a b
    rw [← map_inv, ← map_inv, Units.val_mul, ← hδ]
    simp
  have e2 : ∀ a b, (((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹).val a b
      = (u⁻¹ : (Af ℚ)ˣ) * ((δ a b : ℤ) : Af ℚ) := by
    intro a b
    rw [_root_.mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, ← hδ]
    generalize u⁻¹ = v
    simp
  have i10 : (δ⁻¹ : SL(2, ℤ)) 1 0 = -δ 1 0 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have i11 : (δ⁻¹ : SL(2, ℤ)) 1 1 = δ 0 0 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have hdet' : ((δ 0 0 : ℤ) : Af ℚ) * (δ 1 1 : ℤ) - (δ 0 1 : ℤ) * (N * c) = 1 := by
    rw [hc] at hdet
    exact_mod_cast congrArg (Int.cast : ℤ → Af ℚ) hdet
  refine ⟨u, hu, (memK N _).2 ⟨fun a b => ?_, fun a b => ?_, ⟨-(c * u), neg_mem (mul_mem (hI _) hu.1), ?_⟩,
    (δ 0 0 : ℤ) * y + (δ 0 1 : ℤ) * c, add_mem (mul_mem (hI _) hy) (mul_mem (hI _) (hI _)), ?_⟩, y, hy, hd⟩
  · rw [e1]; exact mul_mem (hI _) hu.1
  · rw [e2]; exact mul_mem hu.2 (hI _)
  · rw [e1, i10, hc]; push_cast; ring
  · rw [e1, i11]; linear_combination ((δ 0 0 : ℤ) : Af ℚ) * hd + hdet'

private theorem nsl_aff (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    nsl k f (aff (Units.mk0 z.im z.im_pos.ne') z.re).val UpperHalfPlane.I = ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f z := by
  have e : (aff (Units.mk0 z.im z.im_pos.ne') z.re).val = !![z.im, z.re; 0, 1] := rfl
  have hd : (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = z.im := by simp
  have hz : (z.im : ℂ) * Complex.I + z.re = z := by
    rw [add_comm]; exact Complex.re_add_im z
  rw [e, nsl, hd, abs_of_pos z.im_pos, sign_pos z.im_pos]
  simp [hz]

theorem UpperTheory.V.Br.downChar :
    UpperTheory.V.Br.DownChar := by
  intro k N hN χ ω hω f φ hφ hc δ hδ
  obtain ⟨u, hu, hK, hd⟩ := ex_K δ hδ
  set β := Matrix.SpecialLinearGroup.mapGL ℚ δ with hβ
  have h2 := hω.unit u hu _ hd
  have s3 : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) = finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) u) :=
    (corner_sc _ u).symm
  have hβ' : (toR β).val = δ.1.map (Int.cast : ℤ → ℝ) := by
    ext i j
    change (Rat.castHom ℝ) (algebraMap ℤ ℚ (δ i j)) = _
    simp
  have key : ∀ x : GL (Fin 2) ℝ, nsl k f x.val UpperHalfPlane.I =
      ((ω.1 (finId ℚ u) : ℂˣ) : ℂ) * nsl k f (toR β * x).val UpperHalfPlane.I := by
    intro x
    have e : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) * (ratGL ℚ 2 1 * (upR (toR β * x) * finGL ℚ 2 1)) =
        ratGL ℚ 2 β * (upR x * finGL ℚ 2 ((toF β)⁻¹ * GeneralLinearGroup.scalar (Fin 2) u)) := by
      have c : ∀ (x : GL (Fin 2) ℝ) (y : GL (Fin 2) (Af ℚ)) (w : GA ℚ 2), finGL ℚ 2 y * (upR x * w) = upR x * (finGL ℚ 2 y * w) :=
        fun x y w => by rw [← mul_assoc, ← upR_comm, mul_assoc]
      rw [s3, ratGL_eq β, map_one, one_mul]
      simp only [mul_assoc, c]
      simp only [mul_assoc, map_mul, map_inv, mul_inv_cancel_left, map_one, mul_one]
    rw [← hφ β x _ hK, ← e, hc, hφ 1 _ 1 (one_mem _)]
  funext z
  have h := key (aff (Units.mk0 z.im z.im_pos.ne') z.re)
  have hdet : 0 < (aff (Units.mk0 z.im z.im_pos.ne') z.re).val.det := by
    have e : (aff (Units.mk0 z.im z.im_pos.ne') z.re).val = !![z.im, z.re; 0, 1] := rfl
    rw [e]
    simpa using z.im_pos
  rw [Units.val_mul, ← (nslMul k f).1 _ _ (toR β).det_ne_zero hdet, hβ', (nslSl k f).1, nsl_aff, nsl_aff] at h
  have hne : ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos z.im_pos _).ne'
  refine mul_left_cancel₀ hne ?_
  rw [Pi.smul_apply, smul_eq_mul]
  linear_combination (-χ ((δ 1 1 : ℤ) : ZMod N)) * h - (((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (f ∣[(k : ℤ)] δ) z) * h2
end

section

open Filter Topology Asymptotics Function
open scoped Real

private theorem UpperTheory.V.Br.per_tendsto {g : ℂ → ℂ} {h : ℝ} (hh : 0 < h) (hp : Periodic g h)
    (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z) (C : ℝ) (m : ℕ)
    (hb : ∀ z : ℂ, 1 ≤ z.im → |z.re| ≤ h → ‖g z‖ ≤ C * z.im ^ m) :
    ∃ c, Tendsto g (comap Complex.im atTop) (𝓝 c) := by
  have hb' : ∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ C * z.im ^ m := by
    intro z hz
    have h1 := hp.sub_int_mul_eq (x := z) ⌊z.re / h⌋
    have h2 := Int.sub_floor_div_mul_nonneg z.re hh
    have h3 := Int.sub_floor_div_mul_lt z.re hh
    have h4 := hb (z - (⌊z.re / h⌋ : ℤ) * (h : ℂ)) (by simpa using hz)
      (by simp only [Complex.sub_re, Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
            Complex.intCast_im, Complex.ofReal_im, mul_zero, sub_zero]
          rw [abs_of_nonneg h2]; exact h3.le)
    rw [h1] at h4
    simpa using h4
  have hev : ∀ A : ℝ, ∀ᶠ z : ℂ in comap Complex.im atTop, A ≤ z.im := fun A =>
    tendsto_comap.eventually (eventually_ge_atTop A)
  have hD := Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hp
    ((hev 1).mono fun z hz => hd z (by linarith))
  have hO : Periodic.cuspFunction h g =O[𝓝[≠] 0] fun q : ℂ => |Real.log ‖q‖| ^ (m : ℝ) := by
    refine IsBigO.of_bound (|C| * (h / (2 * π)) ^ m) ?_
    filter_upwards [(Periodic.invQParam_tendsto hh).eventually (hev 1), self_mem_nhdsWithin] with q hq hq0
    rw [Periodic.cuspFunction_eq_of_nonzero h g hq0]
    refine (hb' _ hq).trans ((le_abs_self _).trans (le_of_eq ?_))
    have : 0 < h / (2 * π) := by positivity
    rw [Periodic.im_invQParam, abs_mul, abs_pow, abs_mul, neg_div, abs_neg, abs_of_pos this,
      Real.rpow_natCast, Real.norm_eq_abs, abs_pow, abs_abs, mul_pow, mul_assoc]
  have ho : (fun q : ℂ => |Real.log ‖q‖| ^ (m : ℝ)) =o[𝓝[≠] 0] fun q : ℂ => (q - 0)⁻¹ := by
    have := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (m : ℝ) (s := -1) (by norm_num)).comp_tendsto
      (tendsto_norm_nhdsNE_zero (E := ℂ))
    refine IsLittleO.of_norm_right ?_
    simpa [Function.comp_def, Real.rpow_neg_one] using this
  have hc : (fun _ : ℂ => Periodic.cuspFunction h g 0) =o[𝓝[≠] 0] fun q : ℂ => (q - 0)⁻¹ := by
    refine isLittleO_const_left.2 (Or.inr ?_)
    simpa [Function.comp_def] using (tendsto_inv_nhdsGT_zero.comp (tendsto_norm_nhdsNE_zero (E := ℂ)))
  have hT := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hD
    ((hO.trans_isLittleO ho).sub hc)
  exact ⟨_, by
    simpa only [Function.comp_def, Periodic.eq_cuspFunction hh.ne' hp] using
      hT.comp (Periodic.qParam_tendsto hh)⟩

theorem UpperTheory.V.Br.perZero :
    UpperTheory.V.Br.PerZero := by
  intro f N hN hf hper ⟨C, m, hb⟩ hint
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine GroundTheory.Automorphic.GL2Classical.isZeroAtImInfty_of_integral_vadd_eq_zero hN' hper hf ?_ hint
  obtain ⟨c, hc⟩ := UpperTheory.V.Br.per_tendsto hN'
    (GroundTheory.Automorphic.GL2Classical.periodic_comp_ofComplex_of_vadd hper)
    (fun z hz => (UpperHalfPlane.mdifferentiable_iff.1 hf).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)) C m
    (fun z hz hr => by
      have h0 : 0 < z.im := by linarith
      have := hb ⟨z, h0⟩ hz hr
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h0] using this)
  have h2 : Tendsto f UpperHalfPlane.atImInfty (𝓝 c) := by
    have := hc.comp (show Tendsto ((↑) : UpperHalfPlane → ℂ) UpperHalfPlane.atImInfty
      (comap Complex.im atTop) from tendsto_comap_iff.2 tendsto_comap)
    simpa [Function.comp_def] using this
  exact h2.isBigO_one ℝ
end
