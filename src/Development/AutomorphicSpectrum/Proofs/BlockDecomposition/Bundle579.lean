module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle641
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle571
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_fd_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    ∃ (A : Submodule ℂ (Sm E a)) (B : Submodule ℂ (Sm E b)), FiniteDimensional ℂ A ∧ FiniteDimensional ℂ B ∧
      (∀ m₂ : GA E b, ∃ φ ∈ A, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁ : GA E a, ∃ φ ∈ B, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, -, rfl⟩ := h
    refine ⟨Submodule.span ℂ {φ₁}, Submodule.span ℂ {φ₂}, inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · refine ⟨φ₂.1 m₂ • φ₁, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp [mul_comm]
    · refine ⟨φ₁.1 m₁ • φ₂, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp
  | zero =>
    refine ⟨⊥, ⊥, inferInstance, inferInstance, fun m₂ => ⟨0, Submodule.zero_mem _, ?_⟩,
      fun m₁ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ hF hG =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    obtain ⟨A', B', hA', hB', h₁', h₂'⟩ := hG
    refine ⟨A ⊔ A', B ⊔ B', inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      obtain ⟨φ', hφ', e'⟩ := h₁' m₂
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      obtain ⟨φ', hφ', e'⟩ := h₂' m₁
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
  | smul c F _ hF =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    refine ⟨A, B, hA, hB, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      refine ⟨c • φ, A.smul_mem c hφ, ?_⟩
      funext x
      simp [e]
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      refine ⟨c • φ, B.smul_mem c hφ, ?_⟩
      funext x
      simp [e]

theorem pairFD_holds : PairFD := by
  intro E _ _ _ a b ι _ U₁ U₂ f hf
  choose A B hA hB h₁ h₂ using fun i => exists_fd_slices U₁ U₂ (f i) (hf i)
  have hA' : FiniteDimensional ℂ (⨆ i, A i : Submodule ℂ (Sm E a)) := Submodule.finiteDimensional_iSup A
  have hB' : FiniteDimensional ℂ (⨆ i, B i : Submodule ℂ (Sm E b)) := Submodule.finiteDimensional_iSup B
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, A i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₂, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₁ i m₂
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, B i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₁, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₂ i m₁
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ

end GlobalTheory.CompanionTheory.EGlue

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairSl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    (∀ m₂, ∃ φ ∈ U₁, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁, ∃ φ ∈ U₂, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine ⟨fun m₂ => ⟨φ₂.1 m₂ • φ₁, U₁.smul_mem _ h₁, ?_⟩, fun m₁ => ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, ?_⟩⟩
    · funext x
      simp [mul_comm]
    · funext x
      simp
  | zero =>
    refine ⟨fun m₂ => ⟨0, U₁.zero_mem, ?_⟩, fun m₁ => ⟨0, U₂.zero_mem, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ h₁ h₂ =>
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁.1 m₂
      obtain ⟨ψ, hψ, e'⟩ := h₂.1 m₂
      refine ⟨φ + ψ, U₁.add_mem hφ hψ, ?_⟩
      funext x
      have i := congrFun e x
      have i' := congrFun e' x
      simp_all
    · obtain ⟨φ, hφ, e⟩ := h₁.2 m₁
      obtain ⟨ψ, hψ, e'⟩ := h₂.2 m₁
      refine ⟨φ + ψ, U₂.add_mem hφ hψ, ?_⟩
      funext x
      have i := congrFun e x
      have i' := congrFun e' x
      simp_all
  | smul r F _ h =>
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h.1 m₂
      refine ⟨r • φ, U₁.smul_mem r hφ, ?_⟩
      funext x
      have i := congrFun e x
      simp_all
    · obtain ⟨φ, hφ, e⟩ := h.2 m₁
      refine ⟨r • φ, U₂.smul_mem r hφ, ?_⟩
      funext x
      have i := congrFun e x
      simp_all

end GlobalTheory.CompanionTheory.EGlue.PairSl

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairSlices : PairSlices := by
  intro E _ _ _ a b U₁ U₂ F hF
  obtain ⟨h₁, h₂⟩ := PairSl.exists_slices U₁ U₂ F hF
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨φ, hφ, e⟩ := h₁ m₂
    have hex : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) := ⟨φ, e⟩
    have hs : sl₁ F m₂ = hex.choose := by simp only [sl₁, dif_pos hex]
    have hc : hex.choose = φ := Subtype.ext (hex.choose_spec.trans e.symm)
    rw [hs, hc]
    exact ⟨hφ, e⟩
  · obtain ⟨φ, hφ, e⟩ := h₂ m₁
    have hex : ∃ φ : Sm E b, φ.1 = fun x => F (m₁, x) := ⟨φ, e⟩
    have hs : sl₂ F m₁ = hex.choose := by simp only [sl₂, dif_pos hex]
    have hc : hex.choose = φ := Subtype.ext (hex.choose_spec.trans e.symm)
    rw [hs, hc]
    exact ⟨hφ, e⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

section

open Filter Topology
open GlobalTheory.CompanionTheory.EGlue PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.MCl

theorem nodup_of_close {ε : ℝ} (hε : ε < 1 / 4) {m n : Multiset ℂ}
    (h : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n) (hg : GapM n) : m.Nodup := by
  induction h with
  | zero => exact Multiset.nodup_zero
  | @cons a b as bs hab hrel ih =>
    have hgn : (b ::ₘ bs).Nodup := hg.1
    have hb : b ∉ bs := (Multiset.nodup_cons.1 hgn).1
    have hg' : GapM bs := by
      refine ⟨(Multiset.nodup_cons.1 hgn).2, fun x hx y hy hxy => ?_⟩
      exact hg.2 x (Multiset.mem_cons_of_mem hx) y (Multiset.mem_cons_of_mem hy) hxy
    refine Multiset.nodup_cons.2 ⟨fun ha => ?_, ih hg'⟩
    obtain ⟨y, hy, hay⟩ := Multiset.exists_mem_of_rel_of_mem hrel ha
    have hne : b ≠ y := fun e => hb (e ▸ hy)
    have h1 := hg.2 b (Multiset.mem_cons_self b bs) y (Multiset.mem_cons_of_mem hy) hne
    have h2 : ‖b - y‖ ≤ ‖a - b‖ + ‖a - y‖ := by
      have : b - y = (a - y) - (a - b) := by ring
      rw [this]
      calc ‖(a - y) - (a - b)‖ ≤ ‖a - y‖ + ‖a - b‖ := norm_sub_le _ _
        _ = ‖a - b‖ + ‖a - y‖ := add_comm _ _
    linarith

theorem prod_close (u : ℂ) (n : Multiset ℂ) : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : Multiset ℂ,
    Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n →
      ‖(m.map (u + ·)).prod - (n.map (u + ·)).prod‖ < δ := by
  induction n using Multiset.induction_on with
  | empty =>
    intro δ hδ
    refine ⟨1, one_pos, fun m hm => ?_⟩
    have : m = 0 := Multiset.rel_zero_right.1 hm
    subst this
    simpa using hδ
  | cons b bs ih =>
    intro δ hδ
    have hc : ContinuousAt (fun p : ℂ × ℂ => p.1 * p.2) (u + b, (bs.map (u + ·)).prod) :=
      continuous_mul.continuousAt
    obtain ⟨δ', hδ', H⟩ := Metric.continuousAt_iff.1 hc δ hδ
    obtain ⟨ε₁, hε₁, H₁⟩ := ih δ' hδ'
    refine ⟨min ε₁ (δ' / 2), lt_min hε₁ (half_pos hδ'), fun m hm => ?_⟩
    obtain ⟨a, as, hab, has, rfl⟩ := Multiset.rel_cons_right.1 hm
    have has' : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε₁) as bs :=
      has.mono fun x _ y _ hxy => hxy.trans (min_le_left _ _)
    have h1 : ‖(u + a) - (u + b)‖ < δ' := by
      have e : (u + a) - (u + b) = a - b := by ring
      rw [e]
      have := hab.trans (min_le_right _ _)
      linarith
    have h2 := H₁ as has'
    have hd : dist ((u + a, (as.map (u + ·)).prod) : ℂ × ℂ) (u + b, (bs.map (u + ·)).prod) < δ' := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨h1, h2⟩
    have h3 := H hd
    rw [dist_eq_norm] at h3
    simpa [Multiset.map_cons, Multiset.prod_cons] using h3

end GlobalTheory.CompanionTheory.EGlue.MCl

namespace GlobalTheory.CompanionTheory.EGlue

theorem mCloseFacts_holds : MCloseFacts := by
  refine ⟨fun ε m n B h hB x hx => ?_, fun ε m n hε h hg => MCl.nodup_of_close hε h hg,
    fun m n hm u => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Multiset.exists_mem_of_rel_of_mem h hx
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa using norm_add_le (x - y) y
    have h2 := hB y hy
    have h3 : ‖x - y‖ ≤ ε := hxy
    linarith
  · rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨ε, hε, H⟩ := MCl.prod_close u n δ hδ
    filter_upwards [hm ε hε] with k hk
    rw [dist_eq_norm]
    exact H _ hk

end GlobalTheory.CompanionTheory.EGlue
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.OneStepProof

open GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem subset_hull (S : Set (Sm E N)) : S ⊆ (hull S : Submodule ℂ (Sm E N)) := by
  intro φ hφ
  refine (Submodule.mem_sInf).2 ?_
  rintro U ⟨hS, -⟩
  exact hS hφ

theorem hull_le {S : Set (Sm E N)} {U : Submodule ℂ (Sm E N)} (hS : S ⊆ U) (hU : _root_.GlobalTheory.CuspRep.IsStable U) : hull S ≤ U :=
  sInf_le ⟨hS, hU⟩

theorem hull_ne_bot {S : Set (Sm E N)} {φ : Sm E N} (hφ : φ ∈ S) (h0 : φ ≠ 0) : hull S ≠ ⊥ := by
  intro h
  have h1 : φ ∈ (hull S : Submodule ℂ (Sm E N)) := subset_hull S hφ
  rw [h] at h1
  exact h0 ((Submodule.mem_bot ℂ).1 h1)

theorem exists_ne_of_hull {S : Set (Sm E N)} (hst : _root_.GlobalTheory.CuspRep.IsStable (hull S)) (T : Sm E N →ₗ[ℂ] Sm E N)
    (he : ∀ o, ∀ χ ∈ hull S, T (act o χ) = act o (T χ)) {ψ : Sm E N} (hψ : ψ ∈ hull S) (hT : T ψ ≠ 0) :
    ∃ φ ∈ S, T φ ≠ 0 := by
  by_contra hcon
  have hz : ∀ φ ∈ S, T φ = 0 := by
    intro φ hφ
    by_contra h
    exact hcon ⟨φ, hφ, h⟩
  have hK : _root_.GlobalTheory.CuspRep.IsStable (hull S ⊓ LinearMap.ker T) := by
    intro o χ hχ
    refine Submodule.mem_inf.2 ⟨hst o χ hχ.1, ?_⟩
    have h0 : T χ = 0 := LinearMap.mem_ker.1 hχ.2
    rw [LinearMap.mem_ker, he o χ hχ.1, h0, map_zero]
  have hS : S ⊆ (hull S ⊓ LinearMap.ker T : Submodule ℂ (Sm E N)) := fun φ hφ =>
    Submodule.mem_inf.2 ⟨subset_hull S hφ, LinearMap.mem_ker.2 (hz φ hφ)⟩
  exact hT (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (hull_le hS hK hψ)).2)

theorem sm_ne_zero {φ : Sm E N} {x : GA E N} (h : φ.1 x ≠ 0) : φ ≠ 0 := by
  rintro rfl
  exact h rfl

theorem oneStep_of_parts : PairSlices → PairRestrict → PairFD → SliceType → PairStep₁ → PairStep₂ → HullGen → CapEquiv →
    OneStep := by
  intro hSl hRe hFD hST hP₁ hP₂ hHG hCE
  intro E _ _ _ a b ι _ K₁ K₂ W₁ W₂ Θ₁ Θ₂ Ω₁ Ω₂ f m₁ m₂ hW₁ hW₂ hF₁ hF₂ hf hT hs₁ hs₂ hA₁ hA₂ hN₁ hN₂ hC₁ hC₂ hI₁ hI₂
    hD₁ hD₂ hP
  obtain ⟨fd₁, fd₂⟩ := hFD E a b ι _ _ f hP
  have ty₁ : ∀ φ ∈ slices₁ f, TypeB K₁ W₁ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).1 φ m h
  have ty₂ : ∀ φ ∈ slices₂ f, TypeB K₂ W₂ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).2 φ m h
  obtain ⟨st₁, fg₁⟩ := hHG E a K₁ W₁ _ ty₁ fd₁
  obtain ⟨st₂, fg₂⟩ := hHG E b K₂ W₂ _ ty₂ fd₂

  have hU₁ : hull (slices₁ f) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    obtain ⟨φ, hφ⟩ := hs₁ i x.2
    refine hull_ne_bot (φ := φ) ⟨i, x.2, hφ⟩ (sm_ne_zero (x := x.1) ?_)
    rw [hφ]
    exact hx
  obtain ⟨t₁, T₁, r₁, g₁, l₁, e₁, i₁, ψ, hψ, hTψ⟩ :=
    hF₁ _ st₁ hA₁ fg₁ hN₁ hC₁ (fun τ => ⟨m₁ τ, hI₁ τ, hD₁ τ⟩) hU₁
  obtain ⟨φ, ⟨i₀, y, hφ⟩, hTφ⟩ := exists_ne_of_hull st₁ T₁ e₁ hψ hTψ
  obtain ⟨G₁ne, G₁p, G₁t, G₁h⟩ := hP₁ E a b ι K₁ K₂ W₁ W₂ _ t₁.space _ T₁ f hW₁ hW₂ st₁ e₁ i₁ hP hT
    ⟨i₀, y, φ, hφ, hTφ⟩

  have hsl : ∀ i m, sl₂ (ap₁ T₁ (f i)) m ∈ hull (slices₂ f) ∧
      (sl₂ (ap₁ T₁ (f i)) m).1 = fun x => ap₁ T₁ (f i) (m, x) :=
    fun i m => (hSl E a b _ _ _ (G₁p i)).2 m
  have hss : slices₂ (fun i => ap₁ T₁ (f i)) ⊆ (hull (slices₂ f) : Submodule ℂ (Sm E b)) := by
    rintro χ ⟨i, m, h⟩
    have hχ : χ = sl₂ (ap₁ T₁ (f i)) m := Subtype.ext (h.trans (hsl i m).2.symm)
    rw [hχ]
    exact (hsl i m).1
  have hle : hull (slices₂ fun i => ap₁ T₁ (f i)) ≤ hull (slices₂ f) := hull_le hss st₂
  have ty₂' : ∀ χ ∈ slices₂ (fun i => ap₁ T₁ (f i)), TypeB K₂ W₂ χ := by
    rintro χ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ _ (G₁t i)).2 χ m h
  obtain ⟨st₂', fg₂'⟩ := hHG E b K₂ W₂ _ ty₂' (hFD E a b ι _ _ _ G₁p).2
  have G₁p' : ∀ i, ap₁ T₁ (f i) ∈ pairSpace t₁.space (hull (slices₂ fun i => ap₁ T₁ (f i))) := fun i =>
    hRe E a b _ _ _ _ (G₁p i) fun m χ h => subset_hull _ ⟨i, m, h⟩
  have hU₂ : hull (slices₂ fun i => ap₁ T₁ (f i)) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 G₁ne
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    refine hull_ne_bot (φ := sl₂ (ap₁ T₁ (f i)) x.1) ⟨i, x.1, (hsl i x.1).2⟩ (sm_ne_zero (x := x.2) ?_)
    rw [(hsl i x.1).2]
    exact hx

  obtain ⟨t₂, T₂, r₂, g₂, l₂, e₂, i₂, ψ', hψ', hTψ'⟩ :=
    hF₂ _ st₂' (fun χ hχ => hA₂ χ (hle hχ)) fg₂' (fun χ hχ => hN₂ χ (hle hχ))
      (by
        obtain ⟨z, hz, h⟩ := hC₂
        exact ⟨z, hz, fun χ hχ => h χ (hle hχ)⟩)
      (fun τ => ⟨m₂ τ, ⟨(hI₂ τ).1, fun u χ hχ => (hI₂ τ).2 u χ (hle hχ)⟩, hD₂ τ⟩) hU₂
  obtain ⟨χ, ⟨i₃, y₃, hχ⟩, hTχ⟩ := exists_ne_of_hull st₂' T₂ e₂ hψ' hTψ'
  obtain ⟨Gne, Gp, Gt, Gh⟩ := hP₂ E a b ι K₁ K₂ W₁ W₂ _ _ t₂.space T₂ (fun i => ap₁ T₁ (f i)) hW₁ hW₂ st₂' e₂ i₂ G₁p' G₁t
    ⟨i₃, y₃, χ, hχ, hTχ⟩
  exact ⟨t₁, t₂, fun i => ap₂ T₂ (ap₁ T₁ (f i)), T₁ ψ, T₂ ψ', r₁, r₂, g₁, g₂, l₁, l₂, Gne, Gp, Gt,
    fun h c e => Gh h c (G₁h h c e), i₁ ψ hψ, hTψ,
    hCE E a _ T₁ ψ m₁ st₁ e₁ hψ (fun τ u => (hI₁ τ).2 u ψ hψ),
    i₂ ψ' hψ', hTψ',
    hCE E b _ T₂ ψ' m₂ st₂' e₂ hψ' (fun τ u => (hI₂ τ).2 u ψ' (hle hψ'))⟩

end GlobalTheory.CompanionTheory.EGlue.OneStepProof

end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue

theorem discInf : DiscInf := by
  intro E _ _ _ M V hV τ
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := M) τ) (((M : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := GlobalTheory.DiscLocEx.exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CompanionTheory.EGlue

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.FactorLimProof

theorem multiset_eq_of_prod_shift {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' :=
  by apply _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep <;> assumption

theorem factorLim_of_parts : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound →
    GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts →
    GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  intro _ hLT hLB hCI hIE hCE hMF hTS hGr hIT E _ _ _ Θs Θf Ωs Ωf N t ψ m n B hLim hRA hRed hGood hAll hψ hψ0 hCap hB hCl
  have leaf := fun k => hLB E N (t k) (ψ k) (m k) B hIT (hGood k) (hψ k) (hψ0 k) (hCap k) (hB k)
  obtain ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, hEmb⟩ :=
    hLT hTS hGr E Θs Θf Ωs Ωf N hLim hRA N le_rfl t (2 * B) hRed hGood hAll leaf
  refine ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, fun τ => ?_, hEmb⟩
  obtain ⟨m₀, mk, hs, hk, hprod⟩ := hCI E N t' s τ hConv hGs
  have hst : ∀ k, IsStable (t (φ k)).space := fun k =>
    hTS E N _ (disc_stable (good_disc (hGood _)))
  have hmk : ∀ k, mk k = m (φ k) τ := by
    intro k
    obtain ⟨e, he1, he2, he3⟩ := hEmb k
    have hne : e (ψ (φ k)) ≠ 0 := fun h => hψ0 _ (he2 _ (hψ _) h)
    have hc : CapEig (e (ψ (φ k))) (m (φ k)) := hCE E N _ e _ _ (hst k) he3 (hψ _) (hCap _)
    exact hIE E N (t' k) _ _ τ _ hIT (hk k) (he1 _ (hψ _)) hne hc
  have hlim : ∀ u : ℂ, Tendsto (fun k => ((m (φ k) τ).map (u + ·)).prod) atTop
      (𝓝 (((n τ).map (u + ·)).prod)) := fun u =>
    hMF.2.2 (fun k => m (φ k) τ) (n τ)
      (fun ε hε => hφ.tendsto_atTop.eventually (hCl τ ε hε)) u
  have hm₀ : m₀ = n τ := multiset_eq_of_prod_shift fun u =>
    tendsto_nhds_unique (by simpa only [hmk] using hprod u) (hlim u)
  exact hm₀ ▸ hIT E N s τ m₀ hs

end GlobalTheory.CompanionTheory.EGlue.FactorLimProof
end

section


theorem _root_.GlobalTheory.T.local_matrix_integral : PositivityTheory.SiegelWeilFormula.Gunr.LocMat := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.locMat | exact GlobalTheory.CompanionTheory.Gunr.locMat | (intros; apply GlobalTheory.CompanionTheory.Gunr.locMat <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unramified_finite_integral : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.finInt | exact GlobalTheory.CompanionTheory.Gunr.finInt | (intros; apply GlobalTheory.CompanionTheory.Gunr.finInt <;> assumption)
end
