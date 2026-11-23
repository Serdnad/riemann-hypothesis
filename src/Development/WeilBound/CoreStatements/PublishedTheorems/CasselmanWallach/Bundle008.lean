module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle001

@[expose] public section

section

open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

private theorem exp_smul_diagonal_I_single_eq_diagonal_exp {n : ℕ} (a : Fin n) (t : ℝ) :
    NormedSpace.exp (t • (Matrix.diagonal fun j : Fin n => if j = a then Complex.I else 0)) =
      Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext j
  by_cases h : j = a
  · simp [h, ← Complex.exp_eq_exp_ℂ, Complex.real_smul]
  · simp [h]

theorem c3b : HighestWeightIntegral := by
  intro n ε H _ _ _ σ hU _ E hE v a x hv hx
  set Y : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => if j = a then Complex.I else 0 with hY
  have hYG : Y ∈ lieSet ε := by
    show Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0
    rw [hY, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext j
    by_cases h : j = a
    · subst h
      simp only [ite_true, Pi.star_apply]
      split_ifs <;> simp
    · simp [h]
  have hact : ReciprocityTheory.ChartRestriction.DS.actM E Y = Complex.I • E a a := by
    simp [ReciprocityTheory.ChartRestriction.DS.actM, hY, Matrix.diagonal_apply, ite_smul]
  have hv' : (v : H) ≠ 0 := by simpa using hv
  have hD : dRep σ Y (v : H) = (Complex.I * x) • (v : H) := by
    rw [← hE Y hYG v, hact]
    simp only [hx, LinearMap.smul_apply, Submodule.coe_smul]
    rw [mul_smul]
  set u : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 with hu
  have hexp : ∀ t : ℝ, NormedSpace.exp (t • Y) = u t := fun t => exp_smul_diagonal_I_single_eq_diagonal_exp a t
  have huU : ∀ t, u t ∈ UJset ε := by
    intro t
    show (u t)ᴴ * Formalism.REAL.Jm ε * u t = Formalism.REAL.Jm ε
    rw [hu, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = a
    · subst h
      simp only [ite_true, Pi.star_apply]
      rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        mul_comm _ (if ε j = true then (1 : ℂ) else -1), mul_assoc, ← Complex.exp_add]
      simp
    · simp [h]
  have hmul : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    simp only [hu, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = a
    · simp [h, add_mul, Complex.exp_add]
    · simp [h]
  have hu0 : u 0 = 1 := by simp [hu]
  have hu2 : u (2 * Real.pi) = 1 := by
    simp only [hu]
    rw [← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases h : j = a
    · simp [h, Complex.exp_two_pi_mul_I]
    · simp [h]
  set F : ℝ → H := fun t => σ (u t) (v : H) with hFdef
  have hF : ∀ s t, F (s + t) = σ (u s) (F t) := by
    intro s t
    simp only [hFdef, hmul, hU.1.2 _ (huU s) _ (huU t), ContinuousLinearMap.comp_apply]
  have hx0 : x ≠ 0 → HasDerivAt F ((Complex.I * x) • (v : H)) 0 := by
    intro hx0
    have h1 : deriv F 0 = (Complex.I * x) • (v : H) := by
      have : F = fun t : ℝ => σ (NormedSpace.exp (t • Y)) (v : H) := by
        funext t
        simp only [hFdef, hexp]
      rw [this]
      exact hD
    have hne : deriv F 0 ≠ 0 := by
      rw [h1]
      exact smul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hx0)) hv'
    have hd : DifferentiableAt ℝ F 0 := by
      by_contra hnd
      exact hne (deriv_zero_of_not_differentiableAt hnd)
    rw [← h1]
    exact hd.hasDerivAt
  by_cases hx00 : x = 0
  · exact ⟨0, by simp [hx00]⟩
  have hder0 := hx0 hx00
  set c : ℂ := Complex.I * x with hc
  have hderF : ∀ s, HasDerivAt F (c • F s) s := by
    intro s
    have h2 : HasDerivAt (fun r => F (r - s)) (c • (v : H)) s := by
      have := HasDerivAt.comp_sub_const (f := F) (f' := c • (v : H)) s s (by simpa using hder0)
      simpa using this
    have h3 := ((σ (u s)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2
    have heq : (fun r => σ (u s) (F (r - s))) = F := by
      funext r
      have := hF s (r - s)
      simp only [add_sub_cancel] at this
      exact this.symm
    have h4 : σ (u s) (c • (v : H)) = c • F s := by
      rw [map_smul]
    have h5 : HasDerivAt (fun r => σ (u s) (F (r - s))) (c • F s) s := by
      convert h3 using 1
      · rfl
      · exact h4.symm
    rwa [heq] at h5
  set G : ℝ → H := fun t => Complex.exp (-c * t) • F t with hG
  have hGd : ∀ t, HasDerivAt G 0 t := by
    intro t
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (-c * y)) (Complex.exp (-c * t) * (-c)) t := by
      have := (((hasDerivAt_id (t : ℂ)).const_mul (-c)).cexp).comp_ofReal
      simpa using this
    have := h1.smul (hderF t)
    convert this using 1
    symm
    rw [smul_smul, ← add_smul, show Complex.exp (-c * t) * c + Complex.exp (-c * t) * -c = 0 by ring,
      zero_smul]
  have hGc := is_const_of_deriv_eq_zero (fun t => (hGd t).differentiableAt)
    (fun t => (hGd t).deriv) (2 * Real.pi) 0
  have hG0 : G 0 = (v : H) := by
    simp only [hG, hFdef, hu0, hU.1.1, one_apply_eq_self, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul]
  have hG2 : G (2 * Real.pi) = Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) • (v : H) := by
    simp only [hG, hFdef, hu2, hU.1.1, one_apply_eq_self]
  rw [hG2, hG0] at hGc
  have hexp1 : Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have : (Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) - 1) • (v : H) = 0 := by
      rw [sub_smul, hGc, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv'
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
  refine ⟨-m, ?_⟩
  have h2 : ((x + m : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
    rw [hc] at hm
    push_cast at hm ⊢
    linear_combination (-1 : ℂ) * hm
  rcases mul_eq_zero.1 h2 with h | h
  · have : x + m = 0 := by exact_mod_cast h
    push_cast
    linarith
  · exact absurd h Complex.two_pi_I_ne_zero

end PositivityTheory.CW
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW.ExponentialKSet

variable {n : ℕ}

theorem exp_mem_kset' {ε : Fin n → Bool} {X : Mx n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have hs : (t • X)ᴴ = -(t • X) := by
      rw [Matrix.conjTranspose_smul, h1]
      simp
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
      ← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • X)).neg_left), neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((h2.smul_left t).exp_left).eq

theorem lie_of {ε : Fin n → Bool} {X : Mx n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) : X ∈ lieSet ε := by
  show Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0
  rw [h1, Matrix.neg_mul, h2.eq, neg_add_cancel]

theorem commute_Jm {ε : Fin n → Bool} {X : Mx n} (h : ∀ i j, X i j ≠ 0 → ε i = ε j) :
    Commute X (Formalism.REAL.Jm ε) := by
  show X * Jm ε = Jm ε * X
  ext i j
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul]
  by_cases hx : X i j = 0
  · simp [hx]
  · rw [h i j hx, mul_comm]

theorem single_conjTranspose (a b : Fin n) (c : ℂ) : (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]

theorem single_neg' (a b : Fin n) (c : ℂ) : Matrix.single a b (-c) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.single_apply, Matrix.neg_apply]
  split_ifs <;> simp

theorem hasDerivAt_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H)
    {f : ℝ → S} {f' : S} (h : HasDerivAt (fun t => (f t : H)) (f' : H) 0) : HasDerivAt f f' 0 := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  convert h using 2 with t
  show ‖((f t - f 0 - (t - 0) • f' : S) : H)‖ = _
  rw [Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul_of_tower]

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (c : ℂ) :
    actM E (Matrix.single a b c) = c • E a b := by
  classical
  simp [actM, Matrix.single_apply, ite_smul, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem actM_add (E : Fin n → Fin n → Module.End ℂ V) (X Y : Mx n) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

end Act

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

theorem key (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ} (hB : KInv ε σ B) {X : Mx n}
    (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (v y : kfin ε σ) :
    B (actM E X v) y = - B v (actM E X y) := by
  have hX : X ∈ lieSet ε := lie_of h1 h2
  have hKt : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Kset ε := exp_mem_kset' h1 h2
  have hKU : ∀ k ∈ Kset ε, k ∈ UJset ε := by
    rintro k ⟨hu, hc⟩
    have h1' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    show kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε
    calc kᴴ * Formalism.REAL.Jm ε * k = star k * (k * Formalism.REAL.Jm ε) := by
          rw [Matrix.mul_assoc, ← hc]; rfl
      _ = Formalism.REAL.Jm ε := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hkinv : ∀ t : ℝ, ∀ w : H,
      σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((-t) • X)) w) = w := by
    intro t w
    rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ (hKU _ (hKt t)) _ (hKU _ (hKt (-t))),
      ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left t).smul_right (-t)),
      ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero, hU.1.1]
    rfl
  obtain ⟨Sv, fv, hv, stv⟩ : IsKFin ε σ (v : H) := v.2
  obtain ⟨Sy, fy, hy, sty⟩ : IsKFin ε σ (y : H) := y.2
  let W : Submodule ℂ H := Sv ⊔ Sy
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_sup Sv Sy
  have stW : ∀ g ∈ Kset ε, ∀ x ∈ W, σ g x ∈ W := by
    intro g hg x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (stv g hg a ha) (sty g hg b hb)
  have hWk : W ≤ kfin ε σ := fun x hx => ⟨W, inferInstance, hx, stW⟩
  have hclosed : IsClosed (W : Set H) := Submodule.closed_of_finiteDimensional W
  have hvW : (v : H) ∈ W := Submodule.mem_sup_left hv
  have hyW : (y : H) ∈ W := Submodule.mem_sup_right hy
  have hder : ∀ x : kfin ε σ,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) x) ((actM E X x : H)) 0 := by
    intro x
    rw [hE X hX x]
    exact GlobalTheory.LowTypeDetermined.hasDerivAt_dRep (G := Formalism.REAL.Jm ε) (hD.1 _ x.2) hX
  have hmemW : ∀ x : kfin ε σ, (x : H) ∈ W → (actM E X x : H) ∈ W := by
    intro x hx
    refine hclosed.mem_of_tendsto (hder x).tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
    exact W.smul_mem _ (W.sub_mem (stW _ (hKt _) _ hx) (stW _ (hKt _) _ hx))
  let cv : ℝ → W := fun t => ⟨σ (NormedSpace.exp (t • X)) v, stW _ (hKt t) _ hvW⟩
  let cy : ℝ → W := fun t => ⟨σ (NormedSpace.exp (t • X)) y, stW _ (hKt t) _ hyW⟩
  have hcv : HasDerivAt cv ⟨_, hmemW v hvW⟩ 0 := hasDerivAt_sub W (hder v)
  have hcy : HasDerivAt cy ⟨_, hmemW y hyW⟩ (-0) := by
    rw [neg_zero]
    exact hasDerivAt_sub W (hder y)
  let ι : W →ₗ[ℂ] kfin ε σ := Submodule.inclusion hWk
  let ℓ1 : W →ₗ[ℝ] ℂ :=
    { toFun := fun w => B (ι w) y
      map_add' := fun a b => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
        simp [Complex.coe_smul] }
  let ℓ2 : W →ₗ[ℝ] ℂ := ((B v).comp ι).restrictScalars ℝ
  let L1 : W →L[ℝ] ℂ := ⟨ℓ1, LinearMap.continuous_of_finiteDimensional ℓ1⟩
  let L2 : W →L[ℝ] ℂ := ⟨ℓ2, LinearMap.continuous_of_finiteDimensional ℓ2⟩
  have d1 := L1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcv
  have d2 := L2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hcy.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ)))
  have heq : (L1 ∘ cv) = (L2 ∘ (cy ∘ Neg.neg)) := by
    funext t
    show B (ι (cv t)) y = B v (ι (cy (-t)))
    exact hB _ (hKt t) v (ι (cy (-t))) (ι (cv t)) y rfl (hkinv t y).symm
  rw [heq] at d1
  have hu := d2.unique d1
  rw [neg_one_smul] at hu
  have e1 : ι ⟨_, hmemW v hvW⟩ = actM E X v := Subtype.ext rfl
  have e2 : ι ⟨_, hmemW y hyW⟩ = actM E X y := Subtype.ext rfl
  change B v (ι (-⟨_, hmemW y hyW⟩)) = B (ι ⟨_, hmemW v hvW⟩) y at hu
  rw [map_neg, map_neg, e1, e2] at hu
  rw [← hu]

theorem compact_pair (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ} (hB : KInv ε σ B) (a b : Fin n) (hab : ε a = ε b)
    (v y : kfin ε σ) : B (E a b v) y = B v (E b a y) := by
  have hsup : ∀ (c d : ℂ) (i j : Fin n),
      (Matrix.single a b c + Matrix.single b a d) i j ≠ 0 → ε i = ε j := by
    intro c d i j h
    by_contra hne
    apply h
    have e1 : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ hab)
    have e2 : ¬ (b = i ∧ a = j) := fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ hab.symm)
    simp [Matrix.single_apply, e1, e2]
  have s1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
      -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
    rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
    simp only [star_one, star_neg, single_neg']
    abel
  have s2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
    simp only [Complex.star_def, Complex.conj_I, single_neg']
    abel
  have k1 := key hU hD hE hB s1 (commute_Jm (hsup 1 (-1))) v y
  have k2 := key hU hD hE hB s2 (commute_Jm (hsup Complex.I Complex.I)) v y
  rw [actM_add, actM_single, actM_single] at k1 k2
  simp only [one_smul, neg_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    map_add, map_neg, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Complex.conj_I, smul_eq_mul,
    RingHom.id_apply, LinearMap.add_apply, LinearMap.neg_apply] at k1 k2
  linear_combination (1 / 2 : ℂ) * k1 + (Complex.I / 2) * k2 +
    ((B (E a b v) y - B v (E a b y) - B v (E b a y) + B (E b a v) y) / 2) * Complex.I_sq

end PositivityTheory.CW.ExponentialKSet

namespace PositivityTheory.CW

open ExponentialKSet in
theorem e2a : E2a := by
  unfold E2a AllIrr
  intro n ε H _ _ _ σ hU hI hD E hE B hB v y
  have hterm : ∀ a b, ε b = ε a → B ((E a b * E b a) v) y = B v ((E a b * E b a) y) := by
    intro a b h
    rw [Module.End.mul_apply, Module.End.mul_apply, compact_pair hU hD hE hB a b h.symm,
      compact_pair hU hD hE hB b a h]

  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
    hterm a b (Finset.mem_filter.mp hb).2

end PositivityTheory.CW

end
end

section

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegativeSymmetric

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hU a b (E b a x) y, hU b a x (E b a y)]
  simp [adjSign, hab]

theorem re_inner_casK_nonneg (hU : IsInfUnitary ε E) (x : V) : 0 ≤ (⟪x, casimirK ε E x⟫_ℂ).re := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply,
    inner_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b hb => ?_
  have hb' : ε b = ε a := (Finset.mem_filter.1 hb).2
  have h := hU b a x (E b a x)
  simp only [ReciprocityTheory.ChartRestriction.DS.adjSign, hb', if_true, one_mul] at h
  rw [← h]
  simpa using (inner_self_nonneg (𝕜 := ℂ) (x := E b a x))

theorem eig_nonneg (hU : IsInfUnitary ε E) {μ : ℝ} {v : V} (hv : v ≠ 0) (h : Eig ε E μ v) : 0 ≤ μ := by
  have h2 := re_inner_casK_nonneg hU v
  rw [show casimirK ε E v = (μ : ℂ) • v from h, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : 0 ≤ μ * ‖v‖ ^ 2 := by simpa [← Complex.ofReal_pow] using h2
  have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  by_contra hμ
  push_neg at hμ
  nlinarith [mul_neg_of_neg_of_pos hμ hn]

end PositivityTheory.CW.CasimirNonnegativeSymmetric

namespace PositivityTheory.CW

open CasimirNonnegativeSymmetric in
theorem e3a : CasimirPowerSurjectiveSymmetric := by
  intro k ε V _ _ E _ hU hM m
  set a := 1 + casimirK ε E with ha_def
  have ha : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ := by
    intro x y
    simp only [ha_def, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right,
      casK_symm hU]
  have hsymm : ∀ j : ℕ, ∀ x y : V, ⟪(a ^ j) x, y⟫_ℂ = ⟪x, (a ^ j) y⟫_ℂ := by
    intro j
    induction j with
    | zero => intro x y; simp
    | succ j ih =>
      intro x y
      calc ⟪(a ^ (j + 1)) x, y⟫_ℂ = ⟪(a ^ j) (a x), y⟫_ℂ := by rw [pow_succ, Module.End.mul_apply]
        _ = ⟪a x, (a ^ j) y⟫_ℂ := ih _ _
        _ = ⟪x, a ((a ^ j) y)⟫_ℂ := ha _ _
        _ = ⟪x, (a ^ (j + 1)) y⟫_ℂ := by rw [pow_succ', Module.End.mul_apply]
  refine ⟨?_, hsymm m⟩
  have hrange : LinearMap.range (a ^ m) = ⊤ := by
    rw [eq_top_iff, ← hM.span, Submodule.span_le]
    rintro v ⟨μ, hv⟩
    show v ∈ LinearMap.range (a ^ m)
    by_cases h0 : v = 0
    · rw [h0]; exact Submodule.zero_mem _
    have hμ : 0 ≤ μ := eig_nonneg hU h0 hv
    have h1 : a v = (1 + (μ : ℂ)) • v := by
      simp [ha_def, add_smul, show casimirK ε E v = (μ : ℂ) • v from hv]
    have hav : ∀ j : ℕ, (a ^ j) v = ((1 + (μ : ℂ)) ^ j) • v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, ← pow_succ']
    have hne1 : (1 + (μ : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add]
      exact_mod_cast (by linarith : (0 : ℝ) < 1 + μ).ne'
    have hne : (1 + (μ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ hne1
    refine LinearMap.mem_range.2 ⟨((1 + (μ : ℂ)) ^ m)⁻¹ • v, ?_⟩
    rw [map_smul, hav, smul_smul, inv_mul_cancel₀ hne, one_smul]
  exact LinearMap.range_eq_top.1 hrange

end PositivityTheory.CW
end

section

namespace PositivityTheory.CW

theorem c3c : KStableHighestWeightVector := by
  intro n ε V _ _ E hgl hun S hfd hS hne
  obtain ⟨w, hw, hw0, μ, hμ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_khw hgl (ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary hun) hfd hS hne
  exact ⟨w, μ, hw, hw0, hμ⟩

end PositivityTheory.CW
end
