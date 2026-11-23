module

public import Formalism.SharpRestriction.ParConsts
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle095
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.Ggeo

theorem bT_le_five_quarters {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := lt_trans one_pos hx1
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hk : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hLa : 0 ≤ L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    have h3 : 0 < L.LaG * L.sc.b' / D.R.k := by linarith
    have h4 : 0 < L.LaG * L.sc.b' := (div_pos_iff_of_pos_right hk).1 h3
    exact ((mul_pos_iff_of_pos_right hb').1 h4).le
  have hr := P.rho_le
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
  have h5 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg P.Crho_pos.le (Real.log_nonneg hx1.le)) hLa) hk.le
  unfold LevelStarExponents.rhoP at hr
  have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h7 := P.bT_le t
  have h8 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h9 := mul_le_mul_of_nonneg_right h6 hb'.le
  linarith

theorem wPl_windows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 ∧ (IsTopPl (Fm.D x i) z → (Fm.L x i).sc.b' ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ 2 * (Fm.L x i).sc.b') := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.T.scale_family_size_relations_eventually Fm
  refine ⟨x0, fun x hx hx1 i j hj z => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, -, -⟩ := h0 x hx hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) h4
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have htop : ∀ (τ : D.what₂.Tau) (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
      L.sc.b' ≤ wj D (j + 1) τ ∧ wj D (j + 1) τ ≤ 2 * L.sc.b' := by
    intro τ t ht
    obtain ⟨a1, a2⟩ := L.win_top (j + 1) (by omega) (by omega) τ t ht
    have a3 := L.bT_ge t
    have a4 := bT_le_five_quarters P t
    constructor <;> linarith
  unfold wPl
  refine ⟨?_, ?_, ?_⟩
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · have := (L.win_thick (j + 1) (by omega) (by omega) _ h1).1
      linarith
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).1
      linarith
    · exact (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).1
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · exact (L.win_thick (j + 1) (by omega) (by omega) _ h1).2
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).2
      linarith
    · have := (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).2
      linarith
  · rintro ⟨hz1, hz2⟩
    refine htop _ ⟨z.2, hz2⟩ ?_
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]

end GlobalTheory.Ggeo
end

section

open Pointwise

namespace GlobalTheory

theorem length_quotient_smul_range_le_finrank_mul : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] (W M : Type) [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] [FiniteDimensional K W] [AddCommGroup M] [Module O M] (f : M →ₗ[O] W), Function.Injective f → ∀ a : O, Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) ≤ (Module.finrank K W : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  intro O K _ _ _ _ _ _ W M _ _ _ _ _ _ _ f hf a
  set R := LinearMap.range (a • (LinearMap.id : M →ₗ[O] M)) with hR
  refine GlobalTheory.T.length_le_of_forall_fg_submodule_length_le O (M ⧸ R) _ ?_
  intro N hN
  obtain ⟨s, hs⟩ := hN
  set g := Function.surjInv (Submodule.mkQ_surjective R) with hg
  have hgs : ∀ q, R.mkQ (g q) = q := Function.surjInv_eq (Submodule.mkQ_surjective R)
  let N' : Submodule O M := Submodule.span O (g '' (s : Set (M ⧸ R)))
  have hmap : N'.map R.mkQ = N := by
    rw [Submodule.map_span, ← hs, ← Set.image_comp]
    congr 1
    ext q
    simp [hgs]
  haveI : Module.Finite O N' := Module.Finite.iff_fg.mpr (Submodule.fg_span (s.finite_toSet.image g))
  let e : N' →ₗ[O] W := f ∘ₗ N'.subtype
  have he : Function.Injective e := hf.comp N'.injective_subtype
  haveI : Module.IsTorsionFree K W := inferInstance
  haveI : Module.IsTorsionFree O W :=
    Module.IsTorsionFree.comap (S := K) (algebraMap O K)
      (fun r hr => IsRegular.of_ne_zero (by
        intro h0
        have hinj := IsFractionRing.injective O K
        have : r = 0 := hinj (by simpa using h0)
        subst this
        exact (not_isRegular_zero (R := O)) hr))
      (fun r m => algebraMap_smul K r m)
  haveI : Module.IsTorsionFree O N' := Function.Injective.moduleIsTorsionFree e he e.map_smul
  haveI : Module.Free O N' := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank O N' ≤ Module.finrank K W := by
    let b := Module.finBasis O N'
    have h1 : LinearIndependent O (e ∘ b) := b.linearIndependent.map' e (LinearMap.ker_eq_bot.mpr he)
    have h2 : LinearIndependent K (e ∘ b) := (LinearIndependent.iff_fractionRing O K).mp h1
    simpa using h2.fintype_card_le_finrank
  let p : N' →ₗ[O] N := (R.mkQ ∘ₗ N'.subtype).codRestrict N (by
    intro x
    rw [← hmap]
    exact ⟨x, x.2, rfl⟩)
  have hp : Function.Surjective p := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let R' := LinearMap.range (a • (LinearMap.id : N' →ₗ[O] N'))
  have hker : R' ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    have : R.mkQ (a • (x : M)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, by simp⟩
    simpa [p] using this
  let q : (N' ⧸ R') →ₗ[O] N := R'.liftQ p hker
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨R'.mkQ x, by simp [q]⟩
  calc Module.length O N ≤ Module.length O (N' ⧸ R') := Module.length_le_of_surjective q hq
    _ = (Module.finrank O N' : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := GlobalTheory.T.length_quotient_scalar_mul O N' a
    _ ≤ _ := by
      gcongr

end GlobalTheory
end
