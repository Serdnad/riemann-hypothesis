module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) :
    actM E Z x ∈ S := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hne : (if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1) ≠ 0 := by
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> norm_num
    have h2 : Z a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h2).resolve_right hne
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  by_cases hab : ε a = ε b
  · exact S.smul_mem _ (hS a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact S.zero_mem

theorem actM_pow_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ S := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact actM_mem_of_isKStableSub_inK hS hZ ih

theorem exists_norm_actM_pow_le_of_isKStableSub {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    (hSf : FiniteDimensional ℂ S) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ S := hSf
  let g : S →ₗ[ℂ] S := (actM E Z).restrict (fun x hx => actM_mem_of_isKStableSub_inK hS hZ hx)
  let gL : S →L[ℂ] S := LinearMap.toContinuousLinearMap g
  refine ⟨‖gL‖, norm_nonneg _, ?_⟩
  have key : ∀ y : S, ‖actM E Z (y : D)‖ ≤ ‖gL‖ * ‖y‖ := fun y => gL.le_opNorm y
  intro x hx m
  induction m with
  | zero => simp
  | succ m ih =>
    have hm := actM_pow_mem_of_isKStableSub_inK hS hZ hx m
    have h1 := key ⟨_, hm⟩
    rw [pow_succ', Module.End.mul_apply]
    calc ‖actM E Z (((actM E Z) ^ m) x)‖ ≤ ‖gL‖ * ‖((actM E Z) ^ m) x‖ := h1
      _ ≤ ‖gL‖ * (‖gL‖ ^ m * ‖x‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖gL‖ ^ (m + 1) * ‖x‖ := by ring

theorem kStable_of_isKStableSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hk : IsKStableSub ε E S) :
    ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v := by
  intro g hg v hv
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hg
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_isKStableSub hk hS hZ
  have hs : Summable fun m : ℕ => (C ^ m * ‖v‖) * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    simp only [sub_zero, abs_one, one_pow, mul_one]
    exact ((Real.summable_pow_div_factorial C).mul_right ‖v‖).congr fun m => by ring
  have h := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply, Complex.ofReal_one, one_smul] at h
  haveI : FiniteDimensional ℂ S := hS
  have hT : IsClosed ((S.map D.subtype : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : σ (NormedSpace.exp Z) (v : H) ∈ S.map D.subtype := by
    refine hT.mem_of_tendsto h.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
    exact Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ ⟨_, actM_pow_mem_of_isKStableSub_inK hk hZ hv m, rfl⟩
  obtain ⟨w, hwS, hw⟩ := hmem
  exact ⟨w, hwS, hw⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isSmoothVecU_restrict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (hSG : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S) (x : S) :
    IsSmoothVecU ε (fun g => (S.orthogonalProjectionOnto ∘L σ g ∘L S.subtypeL : S →L[ℂ] S)) x ↔
      IsSmoothVecU ε σ (x : H) := by
  set P := S.orthogonalProjectionOnto
  have hP : ∀ w : H, w ∈ S → ((P w : S) : H) = w := by
    intro w hw
    have e : P w = ⟨w, hw⟩ := by
      first
        | exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact Submodule.orthogonalProjection_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨w, hw⟩ : _)
        | (show P ((⟨w, hw⟩ : S) : H) = ⟨w, hw⟩; simp [P])
    rw [e]
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => ((F g : S) : H), hU, hg₀U, (S.subtypeL.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    have hmem : σ g (x : H) ∈ S := hSG g hg x x.2
    dsimp only at e1 ⊢
    rw [← e1]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact (hP _ hmem).symm
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => P (F g), hU, hg₀U, (P.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    dsimp only at e1 ⊢
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [e1]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Helpers

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}

theorem smBr_inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold inUJ; simp

theorem smBr_hasDerivAt_ext (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ))
    (g X : Matrix (Fin n) (Fin n) ℂ) (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (Formalism.REAL.indefinite_unitary_mul_mem ε hgJ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t))
  exact hcomp.congr_of_eventuallyEq hev

theorem smBr_rdExt (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ))
    (g X : Matrix (Fin n) (Fin n) ℂ) (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    S7.RdV X f g = fderiv ℝ F g (g * X) :=
  (smBr_hasDerivAt_ext f F U g X hU hg hgJ hF hfF hX).deriv

theorem smBr_rdBracket (f : Matrix (Fin n) (Fin n) ℂ → E) (X Y g : Matrix (Fin n) (Fin n) ℂ)
    (hf : S7.SmoothOnGV ε f) (hX : inG ε X) (hY : inG ε Y) (hg : inUJ ε g) :
    S7.RdV X (S7.RdV Y f) g - S7.RdV Y (S7.RdV X f) g = S7.RdV (X * Y - Y * X) f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inG ε Z → ∀ k ∈ U, inUJ ε k → S7.RdV Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkJ => smBr_rdExt f F U k Z hU hk hkJ hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU Formalism.REAL.withTop_enat_infty_add_one_le_infty).clm_apply (Formalism.REAL.mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) Formalism.REAL.withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (Formalism.REAL.mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : S7.RdV X (S7.RdV Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    smBr_rdExt (S7.RdV Y f) _ U g X hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : S7.RdV Y (S7.RdV X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    smBr_rdExt (S7.RdV X f) _ U g Y hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (Formalism.REAL.lie_algebra_bracket_mem hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

end Helpers

section Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smBr_loc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    S7.RdV X f g = S7.RdV X f' g := by
  unfold S7.RdV
  congr 1
  funext t
  exact h _ (Formalism.REAL.indefinite_unitary_mul_mem ε hg (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t))

theorem smBr_dS_eq (Z : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dS σ Z w = S7.RdV Z (fun g => σ g w) 1 := by
  simp only [dS, S7.RdV, one_mul]

theorem smBr_orbit (hσ : IsURepOn (UJset ε) σ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z)
    {v : H} (hv : IsSmoothVecU ε σ v) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (dS σ Z v) = S7.RdV Z (fun g => σ g v) g := by
  obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv 1 smBr_inUJ_one
  have hc := smBr_hasDerivAt_ext (fun g => σ g v) F U 1 Z hU h1U smBr_inUJ_one hF hfF hZ
  simp only [one_mul] at hc
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hfun : ((σ g) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Z)) v) =
      fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • Z)) v := by
    funext t
    rw [hσ.1.2 g hg _ (Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t)]
    rfl
  have h3 : HasDerivAt (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • Z)) v)
      (σ g (fderiv ℝ F 1 Z)) 0 := by
    rw [← hfun]; exact h2
  rw [dS, hc.deriv, S7.RdV, h3.deriv]

end Main

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_bracket (hσ : IsURepOn (UJset ε) σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y)
    {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ X (dS σ Y v) - dS σ Y (dS σ X v) = dS σ (X * Y - Y * X) v := by
  have e1 : dS σ X (dS σ Y v) = S7.RdV X (S7.RdV Y (fun g => σ g v)) 1 := by
    rw [smBr_dS_eq]
    exact smBr_loc (fun g hg => smBr_orbit hσ hY hv hg) hX smBr_inUJ_one
  have e2 : dS σ Y (dS σ X v) = S7.RdV Y (S7.RdV X (fun g => σ g v)) 1 := by
    rw [smBr_dS_eq]
    exact smBr_loc (fun g hg => smBr_orbit hσ hX hv hg) hY smBr_inUJ_one
  rw [e1, e2, smBr_dS_eq]
  exact smBr_rdBracket _ X Y 1 hv hX hY smBr_inUJ_one

end ReciprocityTheory.ChartRestriction.DS
end
end
