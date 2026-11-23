module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRealMatrixForLatticeAndDualWithDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.PoissonSummationGaussianConstantOnEvenBlocks
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle004
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
import Mathlib.RingTheory.Etale.Weakly
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.WCos
open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

noncomputable def sg (v : InfinitePlace F) : F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).comp rhom

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x :=
  ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).1 v x).symm

theorem cmp_wm (c : Fˣ) (v : InfinitePlace F) (i j : Fin 2) :
    ((HilbertThetaSeries.cmp v (toInf (wm c)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = sg v (((wm c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem sg_ne (c : Fˣ) (v : InfinitePlace F) : sg v (c : F) ≠ 0 := (map_ne_zero _).2 c.ne_zero

theorem denom_wm (c : Fˣ) (v : InfinitePlace F) (z : ℂ) :
    denom (HilbertThetaSeries.cmp v (toInf (wm c))) z = (sg v (c : F) : ℂ) * z := by
  unfold denom
  rw [cmp_wm, cmp_wm]
  simp [wm]

theorem act_wm (c : Fˣ) (z : Hn F) (v : InfinitePlace F) :
    ((act (toInf (wm c)) z v : ℍ) : ℂ) = -((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ))⁻¹ := by
  have hc : (sg v (c : F) : ℂ) ≠ 0 := by exact_mod_cast sg_ne c v
  have hz : ((z v : ℍ) : ℂ) ≠ 0 := (z v).ne_zero
  unfold HilbertThetaSeries.act
  rw [coe_smul_of_det_pos, denom_wm]
  · unfold num
    rw [cmp_wm, cmp_wm]
    simp [wm]
    field_simp
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, cmp_wm, cmp_wm, cmp_wm, cmp_wm]
    simp [wm]

theorem ez_QF {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (e : (κ → F) →+ (InfinitePlace F × κ → ℝ))
    (he : ∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) (b : F) (x : κ → F) (w : Hn F) :
    ez (b * QF G x) w = Complex.exp (Real.pi * Complex.I * ∑ j : InfinitePlace F × κ,
      ((sg j.1 b : ℂ) * (w j.1 : ℂ)) * ((e x j : ℝ) : ℂ) ^ 2) := by
  unfold ez QF
  congr 1
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [reAt_eq, map_mul, map_div₀, map_ofNat, ← reAt_eq v (BF G x x), ← he]
  dsimp only
  rw [← Finset.mul_sum]
  push_cast
  simp only [sq]
  ring

theorem et_BF {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (e : (κ → F) →+ (InfinitePlace F × κ → ℝ))
    (he : ∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) (x y : κ → F) :
    et (BF G x y) = Complex.exp (2 * Real.pi * Complex.I * ∑ j : InfinitePlace F × κ, ((e x j * e y j : ℝ) : ℂ)) := by
  unfold et
  congr 2
  rw [← Complex.ofReal_ratCast, ← ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).2.2.2.2 (BF G x y)).2, ← Complex.ofReal_sum,
    Fintype.sum_prod_type]
  simp only [he]

theorem const_eq (k t : ℕ) (a : F) (c : Fˣ) (z : Hn F) (d : ℝ)
    (hd : d = ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (2 * k) * ((discr F).natAbs : ℝ) ^ k * (t : ℝ) ^ Module.finrank ℚ F) :
    (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ))⁻¹ ^ k * ((d : ℂ)⁻¹ * (∏ v, -Complex.I * ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ))) ^ k)
      = wC k t a (c : F) := by
  have hP : (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => mul_ne_zero (by exact_mod_cast sg_ne c v) (z v).ne_zero
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]
  have hN : (∏ v, (sg v (c : F) : ℂ)) = ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, ← ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).2.2.2.2 (c : F)).1, Complex.ofReal_prod]
    simp only [reAt_eq]
  have h : (∏ v, -Complex.I * ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)))
      = (-Complex.I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) * ∏ v, (sg v (c : F) : ℂ) * (z v : ℂ) := by
    rw [← hN, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  rw [h, hd, wC]
  generalize (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ)) = P at hP
  push_cast
  rw [mul_pow _ P, mul_pow, ← pow_mul, mul_comm (Module.finrank ℚ F) k, div_eq_mul_inv, inv_pow]
  have : (P ^ k)⁻¹ * P ^ k = 1 := inv_mul_cancel₀ (pow_ne_zero _ hP)
  generalize (P ^ k)⁻¹ = Q at this
  generalize (_ * _ * _ : ℂ)⁻¹ = R
  linear_combination (R * ((-Complex.I) ^ (k * Module.finrank ℚ F) * ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) ^ k)) * this

theorem wcos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a : F) (c : Fˣ) (x₀ : κ → F), a ≠ 0 → sl0 k (toInf (wm c)) (th G fun x => open Classical in if x - x₀ ∈ aL κ a then 1 else 0) = th G (wT G k t a c {x₀} fun _ => 1) := by
  intro F _ _ _ κ _ _ G hG t ht k hk a c x₀ ha
  letI : DecidableEq (InfinitePlace F) := Classical.decEq _
  obtain ⟨e, B, α, β, he, hα, hβ, hB, hdet⟩ := GlobalTheory.T.exists_realMatrix_for_lattice_and_dual_with_det F κ G hG t ht k hk a ha
  have hsm := (GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hG).2.1
  have hc : (c : F) ≠ 0 := c.ne_zero
  funext z
  have hz : ∀ v, 0 < ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)).im := fun v => by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
    exact mul_pos (sq_pos_of_ne_zero (sg_ne c v)) (z v).im_pos
  have hP := GlobalTheory.T.poisson_summation_gaussian_constant_on_even_blocks (InfinitePlace F) κ k hk B hB (e x₀) (fun v => (sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)) hz
  have hL : ∀ Φ : (κ → F) → ℂ, (∀ x, x - x₀ ∈ aL κ a → Φ x = 1) → (∀ x, x - x₀ ∉ aL κ a → Φ x = 0) →
      th G Φ (HilbertThetaSeries.act (toInf (wm c)) z)
      = ∑' m : InfinitePlace F × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-((sg j.1 (c : F) : ℂ) ^ 2 * (z j.1 : ℂ))⁻¹)
        * (((B *ᵥ fun i => (m i : ℝ)) j + e x₀ j : ℝ) : ℂ) ^ 2) := by
    intro Φ h1 h0
    unfold th
    have hinj : Function.Injective fun m : InfinitePlace F × κ → ℤ => (α m : κ → F) + x₀ := fun m n h =>
      α.injective (Subtype.ext (add_right_cancel h))
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun m => ?_
      rw [h1 _ (by rw [add_sub_cancel_right]; exact (α m).2), one_mul, ← one_mul (QF G _), ez_QF G e he, map_add (f := _), hα]
      simp only [act_wm, map_one, Complex.ofReal_one, one_mul, Pi.add_apply]
    · intro x hx
      have hx' : x - x₀ ∈ aL κ a := by
        by_contra h
        exact hx (by simp [h0 x h])
      exact ⟨α.symm ⟨_, hx'⟩, by simp⟩
  have hR : th G (wT G k t a c {x₀} fun _ => 1) z = wC k t a (c : F) *
      ∑' m : InfinitePlace F × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, ((sg j.1 (c : F) : ℂ) ^ 2 * (z j.1 : ℂ))
        * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * e x₀ j : ℝ) : ℂ)) := by
    unfold th
    have hinj : Function.Injective fun m : InfinitePlace F × κ → ℤ => (c : F) • (β m : κ → F) := fun m n h =>
      β.injective (Subtype.ext (smul_right_injective _ hc h))
    rw [← hinj.tsum_eq, ← tsum_mul_left]
    · refine tsum_congr fun m => ?_
      have h1 : (a / (c : F)) • (c : F) • (β m : κ → F) ∈ dualL F G := by
        rw [smul_smul, div_mul_cancel₀ _ hc]
        exact (β m).2
      rw [wT, if_pos h1, Finset.sum_singleton, one_mul, (hsm _ _ x₀).1, (hsm _ _ x₀).2.1, mul_div_cancel_left₀ _ hc,
        ez_QF G e he, et_BF G e he, hβ, mul_assoc, mul_comm (Complex.exp _)]
      simp only [map_pow, Complex.ofReal_pow]
    · intro y hy
      have hy' : (a / (c : F)) • y ∈ dualL F G := by
        by_contra h
        exact hy (by simp [wT, h])
      refine ⟨β.symm ⟨(c : F)⁻¹ • y, by rwa [smul_smul, ← div_eq_mul_inv]⟩, ?_⟩
      simp [smul_smul, hc]
  unfold sl0
  simp only [denom_wm]
  rw [hL _ (fun x h => if_pos h) (fun x h => if_neg h), hP, hR, ← mul_assoc, const_eq k t a c z _ hdet]

end GlobalTheory.WCos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.hilbertThetaSeries_coset_inversion_formula : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a : F) (c : Fˣ) (x₀ : κ → F), a ≠ 0 → sl0 k (toInf (wm c)) (th G fun x => open Classical in if x - x₀ ∈ aL κ a then 1 else 0) = th G (wT G k t a c {x₀} fun _ => 1) := by
  first | exact @GlobalTheory.WCos.wcos | exact GlobalTheory.WCos.wcos | (intros; apply GlobalTheory.WCos.wcos <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.LiftCpt

open UpperHalfPlane hiding I

theorem rot_smul_I (x : GL (Fin 2) ℝ) (h1 : x.val 0 0 ^ 2 + x.val 0 1 ^ 2 = 1) (hc : x.val 1 0 = -x.val 0 1)
    (hd : x.val 1 1 = x.val 0 0) : x • UpperHalfPlane.I = UpperHalfPlane.I := by
  have hdet : x.val.det = 1 := by rw [Matrix.det_fin_two, hc, hd]; linear_combination h1
  have hp : 0 < x.val.det := by rw [hdet]; exact one_pos
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by simpa using hp), div_eq_iff (denom_ne_zero _ _), num, denom, hc, hd, coe_I]
  push_cast
  linear_combination (x.val 0 1 : ℂ) * Complex.I_sq

theorem orth_cases {a b c d : ℝ} (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1)
    (h3 : a * c + b * d = 0) : (c = -b ∧ d = a) ∨ (c = b ∧ d = -a) := by
  have hD : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    linear_combination (c ^ 2 + d ^ 2) * h1 + h2 - (a * c + b * d) * h3
  rcases mul_eq_zero.1 hD with h | h
  · exact Or.inl ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩
  · exact Or.inr ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩

variable {F : Type} [Field F] [NumberField F]

def sg (s : InfinitePlace F → Bool) : InfinitePlace F → ℝ := fun v => if s v then 1 else -1

omit [NumberField F] in
theorem sg_mul (s : InfinitePlace F → Bool) : sg s * sg s = 1 := by
  funext v
  simp only [sg, Pi.mul_apply, Pi.one_apply]
  split_ifs <;> norm_num

def epsG (s : InfinitePlace F → Bool) : GL (Fin 2) (InfinitePlace F → ℝ) where
  val := !![sg s, 0; 0, 1]
  inv := !![sg s, 0; 0, 1]
  val_inv := by simp [sg_mul, Matrix.one_fin_two]
  inv_val := by simp [sg_mul, Matrix.one_fin_two]

variable [IsTotallyReal F]

theorem rot_rt (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2) (hφ : IsLift k Ψ φ.1)
    (x : GL (Fin 2) (InfinitePlace F → ℝ)) (h1 : ∀ v, x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2 = 1)
    (hc : ∀ v, x.val 1 0 v = -x.val 0 1 v) (hd : ∀ v, x.val 1 1 v = x.val 0 0 v) :
    ∃ c : ℂ, TR.rt F 2 (TR.infGL F 2 x) φ = c • φ := by
  have hp : Pos x := fun v => by
    rw [Matrix.det_fin_two]
    simp only [Pi.sub_apply, Pi.mul_apply, hc v, hd v]
    nlinarith [h1 v]
  have ha : act x (fun _ => UpperHalfPlane.I) = fun _ => UpperHalfPlane.I :=
    funext fun v => rot_smul_I (cmp v x) (h1 v) (hc v) (hd v)
  refine ⟨sl k x (fun _ => 1) (fun _ => UpperHalfPlane.I), Subtype.ext (funext fun g => ?_)⟩
  have hF : ∀ f : Hn F → ℂ, sl k x f (fun _ => UpperHalfPlane.I) =
      sl k x (fun _ => 1) (fun _ => UpperHalfPlane.I) * f (fun _ => UpperHalfPlane.I) := fun f => by
    simp only [sl, sl0, ha]
    ring
  rw [← TR.infGL_mul_finGL g]
  generalize Matrix.GeneralLinearGroup.map (TR.pInf F) g = y
  generalize Matrix.GeneralLinearGroup.map (pFin F) g = u
  obtain ⟨τ, hτ⟩ := (GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin F 1).2 y
  have e : ∀ y : GL (Fin 2) (InfinitePlace F → ℝ), φ.1 (TR.infGL F 2 y * finGL F 2 u) =
      φ.1 (TR.infGL F 2 (toInf τ * y) * finGL F 2 (toFin τ * u)) := fun y => by
    rw [← hφ.1 τ, (GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin F τ).1, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (finGL F 2 (toFin τ)),
      ← TR.infGL_comm, mul_assoc]
  obtain ⟨q1, -, -, q2, -⟩ := SlashCocycle.slash_cocycle F k (toInf τ * y) x (Ψ (toFin τ * u)) hτ hp
  rw [TR.rt_apply]
  change _ = _ * φ.1 _
  rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, ← map_mul, e, e y, ← mul_assoc, hφ.2 _ q1, hφ.2 _ hτ, q2, hF]

theorem lift_cpt_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2), IsLift k Ψ φ.1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => TR.cptRep F 2 r φ)) := by
  intro F _ _ _ k Ψ φ hφ
  classical
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s => TR.rt F 2 (TR.infGL F 2 (epsG s)) φ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℂ (Set.range fun s => TR.rt F 2 (TR.infGL F 2 (epsG s)) φ)) (Submodule.span_le.2 ?_)
  rintro _ ⟨r, rfl⟩
  set x : GL (Fin 2) (InfinitePlace F → ℝ) := Unitary.toUnits r with hx
  have e : TR.cptRep F 2 r φ = TR.rt F 2 (TR.infGL F 2 x) φ := rfl
  have hr : ∀ v i j, x.val i 0 v * x.val j 0 v + x.val i 1 v * x.val j 1 v = if i = j then 1 else 0 := by
    intro v i j
    have h := congrArg (fun m => m i j v) r.2.2
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply, Pi.add_apply, Pi.mul_apply,
      star_trivial] at h
    rw [ite_apply] at h
    exact h
  have h1 : ∀ v, x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2 = 1 := fun v => by
    have := hr v 0 0; simp only [if_true] at this; linear_combination this
  have h2 : ∀ v, x.val 1 0 v ^ 2 + x.val 1 1 v ^ 2 = 1 := fun v => by
    have := hr v 1 1; simp only [if_true] at this; linear_combination this
  have h3 : ∀ v, x.val 0 0 v * x.val 1 0 v + x.val 0 1 v * x.val 1 1 v = 0 := fun v => by simpa using hr v 0 1
  change TR.cptRep F 2 r φ ∈ _
  rw [e]
  clear_value x
  let s : InfinitePlace F → Bool := fun v => decide (x.val 1 0 v = -x.val 0 1 v ∧ x.val 1 1 v = x.val 0 0 v)
  have hv : (epsG s * x).val = !![sg s * x.val 0 0, sg s * x.val 0 1; x.val 1 0, x.val 1 1] := by
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [epsG, Matrix.mul_apply, Fin.sum_univ_two]
  have hs : ∀ v, x.val 1 0 v = -(sg s v * x.val 0 1 v) ∧ x.val 1 1 v = sg s v * x.val 0 0 v := fun v => by
    by_cases h : x.val 1 0 v = -x.val 0 1 v ∧ x.val 1 1 v = x.val 0 0 v
    · have : sg s v = 1 := by simp only [sg, s, decide_eq_true_eq]; exact if_pos h
      rw [this, one_mul, one_mul]
      exact h
    · have : sg s v = -1 := by simp only [sg, s, decide_eq_true_eq]; exact if_neg h
      rw [this]
      have := (orth_cases (h1 v) (h2 v) (h3 v)).resolve_left h
      exact ⟨by linear_combination this.1, by linear_combination this.2⟩
  obtain ⟨c, hc⟩ := rot_rt k Ψ φ hφ (epsG s * x)
    (fun v => by
      have q : sg s v * sg s v = 1 := congrFun (sg_mul s) v
      rw [hv]
      change (sg s v * x.val 0 0 v) ^ 2 + (sg s v * x.val 0 1 v) ^ 2 = 1
      linear_combination (x.val 0 0 v ^ 2 + x.val 0 1 v ^ 2) * q + h1 v)
    (fun v => by rw [hv]; exact (hs v).1) (fun v => by rw [hv]; exact (hs v).2)
  have e2 : x = epsG s * (epsG s * x) := by
    rw [← mul_assoc, show epsG s * epsG s = 1 from Units.ext (epsG s).val_inv, one_mul]
  rw [e2, map_mul, map_mul, Module.End.mul_apply, hc, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

end GlobalTheory.HilbertThetaSeries.LiftCpt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.adelic_lift_kFinite_of_isLift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : TR.Sm F 2), IsLift k Ψ φ.1 → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => TR.cptRep F 2 r φ)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite | exact GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite | (intros; apply GlobalTheory.HilbertThetaSeries.LiftCpt.lift_cpt_finite <;> assumption)
end
