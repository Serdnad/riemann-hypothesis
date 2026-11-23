module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.IndicatorRholMem
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle006
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Coef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem coef_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hX : inG ε X) (u : H) (m : D) :
    HasDerivAt (fun t : ℝ => ⟪u, σ (g * NormedSpace.exp ((t : ℂ) • X)) (m : H)⟫_ℂ)
      ⟪u, σ g ((actM E X m : D) : H)⟫_ℂ 0 := by
  have h := (((innerSL ℂ u).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hD.deriv X hX m)
  refine HasDerivAt.congr_of_eventuallyEq h (Eventually.of_forall fun t => ?_)
  simp only [hσ.1.2 _ hg _ (exp_smul_mem_UJset hX t)]
  rfl

theorem act_cpart (E : Fin n → Fin n → Module.End ℂ D) (Z : Matrix (Fin n) (Fin n) ℂ) (m : D) :
    actM E Z m = actM E (cpart1 ε Z) m + Complex.I • actM E (cpart2 ε Z) m := by
  have h : actL E Z = actL E (cpart1 ε Z) + Complex.I • actL E (cpart2 ε Z) := by
    rw [← map_smul, ← map_add (f := _), ta_cpart_sum]
  exact congrArg (fun A : Module.End ℂ D => A m) h

theorem eq_zero_of_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    {y : D} (hy : y ∈ genSub E V)
    (h : ∀ g ∈ UJset ε, ∀ v' : V, ⟪((v' : D) : H), σ g (y : H)⟫_ℂ = 0) : y = 0 := by
  let N : Set D := {m | ∀ g ∈ UJset ε, ∀ v' : V, ⟪((v' : D) : H), σ g (m : H)⟫_ℂ = 0}
  have hNr : ∀ X, inG ε X → ∀ m ∈ N, actM E X m ∈ N := fun X hX m hm g hg v' => by
    refine (coef_deriv hσ hD hg hX _ m).unique ?_
    have : (fun t : ℝ => ⟪((v' : D) : H), σ (g * NormedSpace.exp ((t : ℂ) • X)) (m : H)⟫_ℂ) =
        fun _ => 0 := funext fun t => hm _ (ta_inUJ_mul_exp ε hg hX t) v'
    rw [this]; exact hasDerivAt_const _ _
  have hN : ∀ a b, ∀ m ∈ N, E a b m ∈ N := fun a b m hm g hg v' => by
    rw [← actM_single E a b, act_cpart (ε := ε), Submodule.coe_add, Submodule.coe_smul, map_add (f := _),
      map_smul, inner_add_right, inner_smul_right, hNr _ (ta_inG_cpart1 ε _) m hm g hg v',
      hNr _ (ta_inG_cpart2 ε _) m hm g hg v']
    simp
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  let P : Submodule ℂ D :=
    { carrier := {u | ∀ m ∈ N, ⟪u, m⟫_ℂ = 0}
      add_mem' := fun hu hu' m hm => by rw [inner_add_left, hu m hm, hu' m hm, add_zero]
      zero_mem' := fun m _ => inner_zero_left m
      smul_mem' := fun c u hu m hm => by rw [inner_smul_left, hu m hm, mul_zero] }
  have h1J : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hle : genSub E V ≤ P := sInf_le ⟨fun v hv m hm => by
      have := hm 1 h1J ⟨v, hv⟩
      rw [hσ.1.1] at this
      exact this,
    fun a b u hu m hm => by rw [hU a b, hu _ (hN b a m hm), mul_zero]⟩
  exact inner_self_eq_zero.mp (hle hy y h)

theorem inner_deriv {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (f : ℝ → (U →L[ℂ] U)) (φ : U → U → ℂ)
    (h : ∀ a b, HasDerivAt (fun t => ⟪a, f t b⟫_ℂ) (φ a b) 0) (a b : U) :
    ⟪a, deriv f 0 b⟫_ℂ = φ a b := by
  let e := stdOrthonormalBasis ℂ U
  have hf : f = fun t => ∑ i, ∑ j, ⟪e i, f t (e j)⟫_ℂ • (innerSL ℂ (e j)).smulRight (e i) := by
    funext t
    ext x
    conv_lhs => rw [← e.sum_repr' (f t x), ← e.sum_repr' x]

    simp only [map_sum, map_smul, inner_sum, inner_smul_right, sum_smul,
    _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [mul_comm]
  have hd : DifferentiableAt ℝ f 0 := by
    rw [hf]
    exact DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ =>
      (h _ _).differentiableAt.smul_const _
  have h2 := (((innerSL ℂ a).comp (ContinuousLinearMap.apply ℂ U b)).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  exact h2.unique (h a b)

theorem rWord_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (ι : V ≃ₗ[ℂ] U) (Ψ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U))
    (hco : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', Ψ g (ι v)⟫_ℂ)
    (L : List (Matrix (Fin n) (Fin n) ℂ)) : ∀ g, inUJ ε g → ∀ v v' : V,
      ⟪ι v', rWord ε L Ψ g (ι v)⟫_ℂ =
        ⟪((v' : D) : H), σ g (((L.map (actM E)).prod (v : D) : D) : H)⟫_ℂ := by
  induction L with
  | nil => intro g hg v v'; exact (hco g hg v v').symm
  | cons Z L ih =>
    intro g hg v v'
    have hR : ∀ X, inG ε X → ⟪ι v', RdV X (rWord ε L Ψ) g (ι v)⟫_ℂ =
        ⟪((v' : D) : H), σ g ((actM E X ((L.map (actM E)).prod (v : D)) : D) : H)⟫_ℂ := by
      intro X hX
      have := inner_deriv (fun t : ℝ => rWord ε L Ψ (g * NormedSpace.exp ((t : ℂ) • X)))
        (fun a b => ⟪((ι.symm a : D) : H),
          σ g ((actM E X ((L.map (actM E)).prod (ι.symm b : D)) : D) : H)⟫_ℂ)
        (fun a b => by
          refine (coef_deriv hσ hD hg hX _ _).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
          have := ih _ (ta_inUJ_mul_exp ε hg hX t) (ι.symm b) (ι.symm a)
          rwa [ι.apply_symm_apply, ι.apply_symm_apply] at this) (ι v') (ι v)
      rwa [ι.symm_apply_apply, ι.symm_apply_apply] at this
    show ⟪ι v', (RdV (cpart1 ε Z) (rWord ε L Ψ) g + Complex.I • RdV (cpart2 ε Z) (rWord ε L Ψ) g) (ι v)⟫_ℂ = _
    rw [_root_.add_apply, _root_.smul_apply, inner_add_right,
      inner_smul_right, hR _ (ta_inG_cpart1 ε Z), hR _ (ta_inG_cpart2 ε Z), List.map_cons,
      List.prod_cons, Module.End.mul_apply, act_cpart (ε := ε) E Z, Submodule.coe_add,
      Submodule.coe_smul, map_add, map_smul, inner_add_right, inner_smul_right]

end Coef

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem omegaP_mem_nhds {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ OmegaP n) : OmegaP n ∈ 𝓝 x :=
  (tb_inv_hasFDerivAt (tb_isUnit_of_omegaP hx)).choose_spec.1.continuousAt.preimage_mem_nhds
    (isOpen_omega.mem_nhds hx)

def evZ (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) : MMT μ →ₗ[ℂ] ℂ :=
  (LinearMap.proj z : (Matrix (Fin n) (Fin n) ℂ → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (cOm n).subtype ∘ₗ (mmSub μ).subtype

theorem evZ_word (μ : Fin n → ℤ) (L : List (Matrix (Fin n) (Fin n) ℂ)) : ∀ z ∈ OmegaP n,
    evZ μ z ((L.map (actM (eMM μ))).prod (phiMM μ)) = hWord L (PhiP μ) z := by
  induction L with
  | nil => intro z hz; exact Set.indicator_of_mem hz _
  | cons Z L ih =>
    intro z hz
    set F := (L.map (actM (eMM μ))).prod (phiMM μ) with hF
    have h1 : ∀ a b, evZ μ z (eMM μ a b F) =
        fderiv ℂ (hWord L (PhiP μ)) z (z * Matrix.single a b 1) := fun a b => by
      have e : ((F : cOm n) : Matrix (Fin n) (Fin n) ℂ → ℂ) =ᶠ[𝓝 z] hWord L (PhiP μ) :=
        eventually_of_mem (omegaP_mem_nhds hz) ih
      rw [← e.fderiv_eq]
      exact Set.indicator_of_mem hz _
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← hF]
    show _ = fderiv ℂ (hWord L (PhiP μ)) z (z * Z)
    have hZ : z * Z = ∑ a, ∑ b, Z a b • (z * (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ)) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp only [Matrix.mul_sum, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hZ]

    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h1]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst3

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def vcSgl (φ : M) : Fin n → Fin n → M := fun t => Pi.single t φ

def vcRV (n : ℕ) : Fin n → ℕ := fun t => (t : ℕ)

def vcRVd (n : ℕ) : Fin n → ℕ := fun t => (Fin.rev t : ℕ)

def vcThV (lam : Fin n → ℝ) : ℕ → ℂ := fun k => if h : k < n then ((thV lam ⟨k, h⟩ : ℝ) : ℂ) else 0

def vcThVd (lam : Fin n → ℝ) : ℕ → ℂ :=
  fun k => if h : k < n then ((thVd lam (Fin.rev ⟨k, h⟩) : ℝ) : ℂ) else 0

theorem vcThV_rV (lam : Fin n → ℝ) (t : Fin n) : vcThV lam (vcRV n t) = ((thV lam t : ℝ) : ℂ) := by
  simp [vcThV, vcRV, t.isLt]

theorem vcThVd_rVd (lam : Fin n → ℝ) (t : Fin n) : vcThVd lam (vcRVd n t) = ((thVd lam t : ℝ) : ℂ) := by
  unfold vcThVd vcRVd
  rw [dite_eq_left (Fin.rev t).isLt]
  simp only [Fin.eta, Fin.rev_rev]

theorem vcThV_ne (lam : Fin n → ℝ) (hanti : StrictAnti lam) (s : Fin n) :
    ∀ k < n, k ≠ vcRV n s → vcThV lam k ≠ vcThV lam (vcRV n s) := by
  intro k hk hks heq
  rw [vcThV_rV, show vcThV lam k = ((thV lam ⟨k, hk⟩ : ℝ) : ℂ) by simp [vcThV, hk]] at heq
  have h1 : thV lam ⟨k, hk⟩ = thV lam s := by exact_mod_cast heq
  have h2 : lam ⟨k, hk⟩ = lam s := by unfold thV at h1; linarith
  exact hks (congrArg Fin.val (hanti.injective h2))

theorem vcThVd_ne (lam : Fin n → ℝ) (hanti : StrictAnti lam) (s : Fin n) :
    ∀ k < n, k ≠ vcRVd n s → vcThVd lam k ≠ vcThVd lam (vcRVd n s) := by
  intro k hk hks heq
  rw [vcThVd_rVd, show vcThVd lam k = ((thVd lam (Fin.rev ⟨k, hk⟩) : ℝ) : ℂ) by simp [vcThVd, hk]] at heq
  have h1 : thVd lam (Fin.rev ⟨k, hk⟩) = thVd lam s := by exact_mod_cast heq
  have h2 : lam (Fin.rev ⟨k, hk⟩) = lam s := by unfold thVd at h1; linarith
  have h3 := hanti.injective h2
  apply hks
  rw [← h3]
  simp [vcRVd]

theorem vc_xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M}
    (hf : f ∈ Xs A S θ) : A f = ((θ : ℝ) : ℂ) • f := by
  have h := (Submodule.mem_inf.mp hf).2
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

end Inst3

theorem verma_cone (n : ℕ) : VermaConeStatement n := by
  intro M _ _ E lam φ s hE hlow hd hgen hanti
  obtain ⟨hTV, hTVd, -, -⟩ := tens_statement n M E hE
  refine ⟨?_, ?_⟩
  · have hgenV : ∀ t, eeV E (vcSgl φ t) - vcThV lam (vcRV n t) • vcSgl φ t ∈
        vcFlag (tensV E) (vcSgl φ) (vcRV n) (vcRV n t + 1) := by
      intro t
      rw [vcThV_rV]
      show eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) ∈ _
      rw [vc_genV E lam φ hlow hd t]
      refine Submodule.sum_mem _ fun d hd' => vcFlag_stable _ _ _ _ _ _ _ (vcFlag_gen _ _ _ ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      exact hd'
    have h0 : vcFlag (tensV E) (vcSgl φ) (vcRV n) 0 = ⊤ := by
      refine vc_gen_top E φ hgen (tensV E) ?_ _ (vcFlag_stable _ _ _ 0)
        (fun c => vcFlag_gen (tensV E) (vcSgl φ) (vcRV n) (Nat.zero_le _))
      intro a b c m
      rw [vc_tensV_single]
      split_ifs
      · have hx : (Pi.single a m : Fin n → M) ∈
            Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
          Submodule.subset_span ⟨a, rfl⟩
        simpa using Submodule.neg_mem _ hx
      · simp
    have hlowV : ∀ a b, b < a → tensV E a b (vcSgl φ s) ∈ vcFlag (tensV E) (vcSgl φ) (vcRV n) (vcRV n s + 1) := by
      intro a b hab
      show tensV E a b (Pi.single s φ) ∈ _
      rw [vc_tensV_single, hlow a b hab, Pi.single_zero, zero_add]
      split_ifs with hbs
      · subst hbs
        exact vcFlag_gen _ _ _ hab
      · exact Submodule.zero_mem _
    have hdiagV : ∀ a, tensV E a a (vcSgl φ s) = (((lam + rho n + Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • vcSgl φ s := by
      intro a
      show tensV E a a (Pi.single s φ) = _ • (Pi.single s φ : Fin n → M)
      rw [vc_tensV_single, hd a, Pi.single_smul']
      by_cases has : a = s
      · subst has
        simp [add_smul]
      · simp [has, Pi.single_apply]
    have hrinj : Function.Injective (vcRV n) := fun a b h => Fin.ext h
    obtain ⟨h1, h2⟩ := vc_cone_core (tensV E) hTV (eeV E) (vc_commV E hE) (vcFlag (tensV E) (vcSgl φ) (vcRV n))
      (vcThV lam) (vcFlag_stable _ _ _) (vcFlag_step _ _ _ (eeV E) (vc_commV E hE) (vcThV lam) hgenV) n
      (vcRV n s) h0 (vcFlag_eq_bot _ _ _ (fun t => t.isLt)) s.isLt (vcThV_ne lam hanti s) (vcSgl φ s)
      (lam + rho n + Pi.single s 1) (vcFlag_top_le _ _ _ hrinj rfl) hlowV hdiagV
    refine ⟨fun μ f hf hf0 hμ => h1 μ f (by rw [vcThV_rV]; exact vc_xs hf) hf0 hμ, ?_⟩
    intro f₁ f₂ hf₁ hf₂ hw₁ hw₂
    exact h2 f₁ f₂ (by rw [vcThV_rV]; exact vc_xs hf₁) (by rw [vcThV_rV]; exact vc_xs hf₂) hw₁ hw₂
  · have hgenVd : ∀ t, eeVd E (vcSgl φ t) - vcThVd lam (vcRVd n t) • vcSgl φ t ∈
        vcFlag (tensVd E) (vcSgl φ) (vcRVd n) (vcRVd n t + 1) := by
      intro t
      rw [vcThVd_rVd]
      show eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) ∈ _
      rw [vc_genVd E lam φ hlow hd t]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd' =>
        vcFlag_stable _ _ _ _ _ _ _ (vcFlag_gen _ _ _ ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      have := Fin.lt_def.mp hd'
      simp only [vcRVd, Fin.val_rev]
      omega
    have h0 : vcFlag (tensVd E) (vcSgl φ) (vcRVd n) 0 = ⊤ := by
      refine vc_gen_top E φ hgen (tensVd E) ?_ _ (vcFlag_stable _ _ _ 0)
        (fun c => vcFlag_gen (tensVd E) (vcSgl φ) (vcRVd n) (Nat.zero_le _))
      intro a b c m
      rw [vc_tensVd_single]
      split_ifs
      · have hx : (Pi.single b m : Fin n → M) ∈
            Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
          Submodule.subset_span ⟨b, rfl⟩
        simpa using hx
      · simp
    have hlowVd : ∀ a b, b < a → tensVd E a b (vcSgl φ s) ∈
        vcFlag (tensVd E) (vcSgl φ) (vcRVd n) (vcRVd n s + 1) := by
      intro a b hab
      show tensVd E a b (Pi.single s φ) ∈ _
      rw [vc_tensVd_single, hlow a b hab, Pi.single_zero, zero_sub]
      split_ifs with has
      · subst has
        refine Submodule.neg_mem _ (vcFlag_gen _ _ _ ?_)
        have := Fin.lt_def.mp hab
        simp only [vcRVd, Fin.val_rev]
        omega
      · simp
    have hdiagVd : ∀ a, tensVd E a a (vcSgl φ s) =
        (((lam + rho n - Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • vcSgl φ s := by
      intro a
      show tensVd E a a (Pi.single s φ) = _ • (Pi.single s φ : Fin n → M)
      rw [vc_tensVd_single, hd a, Pi.single_smul']
      by_cases has : a = s
      · subst has
        simp [add_smul, sub_smul]
      · simp [has, Pi.single_apply]
    have hrinj : Function.Injective (vcRVd n) := fun a b h => Fin.rev_injective (Fin.ext h)
    obtain ⟨h1, h2⟩ := vc_cone_core (tensVd E) hTVd (eeVd E) (vc_commVd E hE)
      (vcFlag (tensVd E) (vcSgl φ) (vcRVd n)) (vcThVd lam) (vcFlag_stable _ _ _)
      (vcFlag_step _ _ _ (eeVd E) (vc_commVd E hE) (vcThVd lam) hgenVd) n
      (vcRVd n s) h0 (vcFlag_eq_bot _ _ _ (fun t => (Fin.rev t).isLt)) (Fin.rev s).isLt
      (vcThVd_ne lam hanti s) (vcSgl φ s)
      (lam + rho n - Pi.single s 1) (vcFlag_top_le _ _ _ hrinj rfl) hlowVd hdiagVd
    refine ⟨fun μ f hf hf0 hμ => h1 μ f (by rw [vcThVd_rVd]; exact vc_xs hf) hf0 hμ, ?_⟩
    intro f₁ f₂ hf₁ hf₂ hw₁ hw₂
    exact h2 f₁ f₂ (by rw [vcThVd_rVd]; exact vc_xs hf₁) (by rw [vcThVd_rVd]; exact vc_xs hf₂) hw₁ hw₂

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
