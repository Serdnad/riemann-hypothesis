module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle025
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

@[expose] public section

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne

lemma lev_one (N : ℕ) : GlobalTheory.Hk.lev N 1 = CongruenceSubgroup.Gamma1 N := by
  ext γ
  simp only [GlobalTheory.Hk.lev, Subgroup.mem_inf, CongruenceSubgroup.Gamma0_mem, and_iff_left_iff_imp]
  intro _
  exact Subsingleton.elim _ _

theorem tq_semisimple : ∀ (N k q : ℕ) (σ : SL(2, ℤ)), 5 ≤ N → 3 ≤ k → q.Prime → ¬ q ∣ N →
    IsDiam N 1 (q : ZMod N) σ →
    ∀ (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ),
      (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  intro N k q σ hN _ hq hqN hσ f c n h
  obtain ⟨-, -, hT, hD, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  have hT' : TqF (k : ℤ) q σ = GlobalTheory.Hk.heckeT (k : ℤ) q σ := funext fun F => hT _ _ _ F hq.pos
  have hσ' : GlobalTheory.Hk.IsDia N 1 (q : ℤ) σ := (hD N 1 (q : ℤ) σ).1 (by simpa using hσ)
  rw [hT'] at h ⊢
  let g : CuspForm (GlobalTheory.Hk.lev N 1) (k : ℤ) := f.copy ⇑f rfl (by rw [lev_one])
  exact GlobalTheory.T.heckeTOperatorExplicit_semisimple_cuspForms N 1 q (k : ℤ) σ c n (by omega) one_pos hq (by simpa using hqN) hσ' g h

end GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne
end

section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.TateGeo

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem cong_refl' (k : ℕ) (x : Ω) : Cong (p := p) k x x :=
  ⟨0, isIntegral_zero, by simp⟩

theorem cong_symm' {k : ℕ} {x y : Ω} (h : Cong (p := p) k x y) : Cong (p := p) k y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩

theorem cong_trans' {k : ℕ} {x y w : Ω} (h1 : Cong (p := p) k x y) (h2 : Cong (p := p) k y w) : Cong (p := p) k x w := by
  obtain ⟨z, hz, e⟩ := h1
  obtain ⟨z', hz', e'⟩ := h2
  exact ⟨z + z', hz.add hz', by rw [mul_add, ← e, ← e']; ring⟩

theorem cong_add' {k : ℕ} {x y x' y' : Ω} (h1 : Cong (p := p) k x y) (h2 : Cong (p := p) k x' y') :
    Cong (p := p) k (x + x') (y + y') := by
  obtain ⟨z, hz, e⟩ := h1
  obtain ⟨z', hz', e'⟩ := h2
  exact ⟨z + z', hz.add hz', by rw [mul_add, ← e, ← e']; ring⟩

theorem cong_mul_left' {k : ℕ} {x y : Ω} (a : Ω) (ha : IsInt (p := p) a) (h : Cong (p := p) k x y) :
    Cong (p := p) k (a * x) (a * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨a * z, ha.mul hz, by rw [← mul_sub, e]; ring⟩

theorem cong_sum' {k : ℕ} {ι : Type*} (s : Finset ι) (f f' : ι → Ω)
    (h : ∀ i ∈ s, Cong (p := p) k (f i) (f' i)) : Cong (p := p) k (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cong_refl' (p := p) k (0 : Ω)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cong_add' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cong_of_eq' {k : ℕ} {x y : Ω} (h : x = y) : Cong (p := p) k x y := h ▸ cong_refl' k x

theorem mem_geoTop_iff (T : Tower p Ω) (g : Gal p Ω) :
    g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n ↔
      (∀ x : Ω, IsAlgZp p x → g x = x) ∧ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  rw [Subgroup.mem_inf, Subgroup.mem_iInf]
  refine and_congr Iff.rfl (forall_congr' fun n => ?_)
  rw [Gn, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rfl

theorem exists_moved (T : Tower p Ω) {g : Gal p Ω} (hg : g ∉ Ggeo p Ω ⊓ ⨅ n, Gn T n) :
    ∃ a : Ω, g a ≠ a ∧ ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h a = a := by
  rw [mem_geoTop_iff] at hg
  by_contra hno
  push_neg at hno
  apply hg
  refine ⟨fun x hx => ?_, fun n => ⟨?_, ?_⟩⟩
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno x hne
    exact hx' (((mem_geoTop_iff T h).mp hh).1 x hx)
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).1
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).2

theorem uniform_lc_on (hΩ : IsClo p Ω) (T : Tower p Ω) {k : ℕ} {c : Gal p Ω → Ω}
    (hc : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c) :
    ∃ S₀ : Finset Ω, ∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      (∀ x ∈ S₀, h x = g x) → Cong (p := p) k (c h) (c g) := by
  classical
  set H := Ggeo p Ω ⊓ ⨅ n, Gn T n with hH
  have hS : ∀ g : Gal p Ω, ∃ S : Finset Ω,
      (g ∈ H → ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong (p := p) k (c h) (c g)) ∧
      (g ∉ H → ∀ h ∈ H, ¬ ∀ x ∈ S, h x = g x) := by
    intro g
    by_cases hg : g ∈ H
    · obtain ⟨S, hS⟩ := hc.2 g hg
      exact ⟨S, fun _ => hS, fun h => (h hg).elim⟩
    · obtain ⟨a, hga, ha⟩ := exists_moved T hg
      refine ⟨{a}, fun h => (hg h).elim, fun _ h hh hagree => ?_⟩
      have := hagree a (Finset.mem_singleton_self a)
      rw [ha h hh] at this
      exact hga this.symm
  choose S hS1 hS2 using hS
  obtain ⟨F, hF⟩ := GlobalTheory.T.finite_galois_approximation p Ω hΩ S
  refine ⟨F.biUnion S, fun g hg h hh hgh => ?_⟩
  obtain ⟨g0, hg0F, hg0⟩ := hF g
  have hg0H : g0 ∈ H := by
    by_contra hn
    exact hS2 g0 hn g hg hg0
  have h1 : Cong (p := p) k (c g) (c g0) := hS1 g0 hg0H g hg hg0
  have h2 : Cong (p := p) k (c h) (c g0) := hS1 g0 hg0H h hh (fun x hx => by
    rw [hgh x (Finset.mem_biUnion.mpr ⟨g0, hg0F, hx⟩), hg0 x hx])
  exact cong_trans' h2 (cong_symm' h1)

theorem uniform_lc_on_int (hΩ : IsClo p Ω) (T : Tower p Ω) {k : ℕ} {c : Gal p Ω → Ω}
    (hc : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c) :
    ∃ S₁ : Finset Ω, (∀ s ∈ S₁, IsInt (p := p) s) ∧ ∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, (∀ x ∈ S₁, h x = g x) → Cong (p := p) k (c h) (c g) := by
  classical
  obtain ⟨S₀, hS₀⟩ := uniform_lc_on hΩ T hc
  have hm : ∀ x : Ω, ∃ a : O0 p, a ≠ 0 ∧ IsInt (p := p) (a • x) := fun x => by
    obtain ⟨a, ha, hi⟩ := (hΩ.alg.isAlgebraic x).exists_integral_multiple
    exact ⟨a, ha, hi⟩
  choose a ha hai using hm
  refine ⟨S₀.image (fun x => a x • x), ?_, fun g hg h hh hgh => hS₀ g hg h hh fun x hx => ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    exact hai x
  · have e := hgh (a x • x) (Finset.mem_image_of_mem _ hx)
    rw [Algebra.smul_def, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at e
    have hne : algebraMap (O0 p) Ω (a x) ≠ 0 := by
      intro h0
      exact ha x (hΩ.inj (by rw [h0, map_zero]))
    exact mul_left_cancel₀ hne e

theorem h1_killed_by_zeta_sub_one_geo : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  intro p _ hp2 Ω _ _ hΩ T k j hj c hc hcoc
  classical
  set H := Ggeo p Ω ⊓ ⨅ n, Gn T n with hHdef
  obtain ⟨S₁, hS₁int, hS₁⟩ := uniform_lc_on_int hΩ T hc
  obtain ⟨y, E, hy, hEH, hu, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hΩ T H inf_le_right S₁ j hj
  set x : Ω := ∑ g ∈ E, g y * c g with hx
  have hxint : IsInt (p := p) x := by
    refine IsIntegral.sum _ fun g hg => ?_
    exact (IsIntegral.map g.toAlgHom hy).mul (hc.1 g (hEH g hg))
  refine ⟨-x, hxint.neg, fun h hh => ?_⟩
  have hσex : ∀ g ∈ E, ∃ g' ∈ E, (h * g) y = g' y ∧ ∀ s ∈ S₁, (h * g) s = g' s := fun g hg => by
    obtain ⟨g', ⟨hg'E, h1, h2⟩, -⟩ := hu (h * g) (H.mul_mem hh (hEH g hg))
    exact ⟨g', hg'E, h1, h2⟩
  choose! σ hσE hσy hσS using hσex
  have hσinj : Set.InjOn σ E := by
    intro g1 hg1 g2 hg2 he
    have ey : g1 y = g2 y := by
      have := (hσy g1 hg1).trans ((congrArg (fun f : Gal p Ω => f y) he).trans (hσy g2 hg2).symm)
      simpa using this
    have es : ∀ s ∈ S₁, g1 s = g2 s := fun s hs => by
      have := (hσS g1 hg1 s hs).trans ((congrArg (fun f : Gal p Ω => f s) he).trans (hσS g2 hg2 s hs).symm)
      simpa using this
    exact (hu g1 (hEH g1 hg1)).unique ⟨hg1, rfl, fun _ _ => rfl⟩ ⟨hg2, ey, es⟩
  have himg : E.image σ = E :=
    Finset.eq_of_subset_of_card_le (fun g' hg' => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hg'
      exact hσE g hg) (by rw [Finset.card_image_of_injOn hσinj])
  have hperm : ∑ g ∈ E, σ g y * c (σ g) = x := by
    rw [hx, ← Finset.sum_image (f := fun g' => g' y * c g') hσinj, himg]
  have hhx : h x = ∑ g ∈ E, h (g y) * h (c g) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]; simp only [map_mul]
  have hζ : h (T.ζ j) = T.ζ j := (((mem_geoTop_iff T h).mp hh).2 j).1
  have hsumh : ∑ g ∈ E, h (g y) = T.ζ j - 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hsum, map_sub, map_one, hζ]
  have step : ∀ g ∈ E, Cong (p := p) k (h (g y) * h (c g)) (σ g y * c (σ g) - h (g y) * c h) := by
    intro g hg
    have hgH := hEH g hg
    have c1 : Cong (p := p) k (h (c g)) (c (h * g) - c h) := by
      obtain ⟨z, hz, e⟩ := hcoc h hh g hgH
      exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩
    have c2 : Cong (p := p) k (c (h * g)) (c (σ g)) :=
      hS₁ (σ g) (hEH _ (hσE g hg)) (h * g) (H.mul_mem hh hgH) (hσS g hg)
    have c3 : Cong (p := p) k (c (h * g) - c h) (c (σ g) - c h) := by
      obtain ⟨z, hz, e⟩ := c2
      exact ⟨z, hz, by rw [← e]; ring⟩
    have := cong_mul_left' (h (g y)) (IsIntegral.map h.toAlgHom (IsIntegral.map g.toAlgHom hy))
      (cong_trans' c1 c3)
    refine cong_trans' this (cong_of_eq' ?_)
    have ey : h (g y) = σ g y := by rw [← hσy g hg]; rfl
    rw [ey]; ring
  have total := cong_sum' E _ _ step
  rw [← hhx, Finset.sum_sub_distrib, hperm, ← Finset.sum_mul, hsumh] at total
  obtain ⟨z, hz, e⟩ := total
  refine ⟨z, hz, ?_⟩
  show (T.ζ j - 1) * c h - (h (-x) - -x) = _
  rw [map_neg, ← e]; ring

end GlobalTheory.K5.TateGeo
end
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

section Klc

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_eq_pow (T : Tower p Ω) (k j : ℕ) : zS T k = zS T (k + j) ^ (p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, pow_succ' p j, pow_mul]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact (T.ζpow (k + j)).symm

theorem qS_eq_pow (T : Tower p Ω) (k j : ℕ) : qS T k = qS T (k + j) ^ (p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, pow_succ' p j, pow_mul]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact (T.qpow (k + j)).symm

theorem D_zS_mem_span (T : Tower p Ω) {k m : ℕ} (h : k ≤ m) :
    KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T k) ∈
      Submodule.span (integralClosure (O0 p) Ω)
        {KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m),
          KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [zS_eq_pow T k j, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem D_qS_mem_span (T : Tower p Ω) {k m : ℕ} (h : k ≤ m) :
    KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T k) ∈
      Submodule.span (integralClosure (O0 p) Ω)
        {KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m),
          KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [qS_eq_pow T k j, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Klc


theorem p_sq_smul_kaehler_mem_span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω))
    (n : ℕ), ∃ m, n ≤ m ∧ ∃ x y : (integralClosure (O0 p) Ω), (p : (integralClosure (O0 p) Ω)) ^ 2 • η =
      x • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m) +
        y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m) := by
  intro p _ Ω _ _ hp2 hclo T η n
  let 𝒮 := integralClosure (O0 p) Ω
  let 𝒟 := KaehlerDifferential.D (O0 p) 𝒮
  let N : ℕ → Submodule 𝒮 (KaehlerDifferential (O0 p) 𝒮) :=
    fun m => Submodule.span 𝒮 {𝒟 (zS T m), 𝒟 (qS T m)}
  have hmono : Monotone N := fun k m h => Submodule.span_le.2 (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [D_zS_mem_span T h, D_qS_mem_span T h])
  have hder : ∀ B : Subalgebra (O0 p) 𝒮, IsDerOn B (fun x => 𝒟 x) := fun B =>
    ⟨fun x _ y _ => map_add 𝒟 x y, fun x _ y _ => Derivation.leibniz 𝒟 x y,
      fun a => (𝒟).map_algebraMap a⟩
  have hgen : ∀ t : 𝒮, (p : 𝒮) ^ 2 • 𝒟 t ∈ ⨆ m, N m := by
    intro t
    obtain ⟨C, tr, k, a, b, hF, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_towerUnionAdjoin p Ω hp2 hclo T {t}
    have h1 := GlobalTheory.T.almostDualTrace_derivation_mem_span_values (O0 p) 𝒮 _ (towerAlg T) C tr k a b _ htr (fun x => 𝒟 x) (hder C) t
      (hF (by simp))
    have h2 : Submodule.span 𝒮 ((fun x => 𝒟 x) '' (towerAlg T : Set 𝒮)) ≤ ⨆ m, N m := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h3 := GlobalTheory.T.derivationOn_adjoin_mem_span_image (O0 p) 𝒮 _ (Set.range (zS T) ∪ Set.range (qS T)) (fun x => 𝒟 x)
        (hder _) x hx
      refine Submodule.span_le.2 ?_ h3
      rintro _ ⟨y, (⟨k, rfl⟩ | ⟨k, rfl⟩), rfl⟩
      · exact Submodule.mem_iSup_of_mem k (Submodule.subset_span (by simp))
      · exact Submodule.mem_iSup_of_mem k (Submodule.subset_span (by simp))
    rw [pow_two]
    exact h2 h1
  have hall : ∀ ω ∈ Submodule.span 𝒮 (Set.range 𝒟), (p : 𝒮) ^ 2 • ω ∈ ⨆ m, N m := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hgen t
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hη : (p : 𝒮) ^ 2 • η ∈ ⨆ m, N m :=
    hall η (by rw [KaehlerDifferential.span_range_derivation]; trivial)
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed N hmono.directed_le).1 hη
  refine ⟨max m n, le_max_right _ _, ?_⟩
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.1 (hmono (le_max_left m n) hm)
  exact ⟨x, y, hxy.symm⟩

end GlobalTheory.AlmostEt
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

lemma ch_periodic_of_dvd {N L : ℕ} (ε : DirichletCharacter ℂ N) (h : N ∣ L) (d : ℤ) :
    ch ε (d + L) = ch ε d := by
  unfold ch
  have : ((L : ℤ) : ZMod N) = 0 := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff L N).2 h
  rw [Int.cast_add, this, add_zero]

theorem iterU_level_val_stable : ∀ (k N l m : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c a : ℕ → ℂ),
    1 ≤ k → l.Prime → α ≠ 0 → MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) ∧
      (EigF k N l ε t α B c → ∀ r, m ≤ r → val B c l α r a = val B c l α m a) := by
  intro k N l m ε t α B c a hk hl hα ha
  have lev : ∀ m (a : ℕ → ℂ), MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) := by
    intro m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      have hU : MF k (N * l ^ (m + 1)) (ch ε) (Uo l a) := by
        refine GlobalTheory.T.coeffHeckeUOperator_lowers_level k (N * l ^ (m + 1)) l (ch ε) a hk hl ?_ ?_ ?_
        · exact Dvd.dvd.mul_left (dvd_pow_self l (Nat.succ_ne_zero m)) N
        · exact ch_periodic_of_dvd ε (Dvd.intro _ rfl)
        · simpa [pow_succ, mul_assoc] using ha
      rw [Function.iterate_succ_apply]
      exact ih _ hU
  have hb := lev m a ha
  refine ⟨hb, fun hE r hr => ?_⟩
  have per : ∀ d, ch ε (d + ((N * l : ℕ) : ℤ)) = ch ε d := ch_periodic_of_dvd ε (Dvd.intro _ rfl)
  have mfj : ∀ j, MF k (N * l) (ch ε) ((Uo l)^[j] ((Uo l)^[m] a)) := by
    intro j
    induction j with
    | zero => simpa using hb
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch ε) _ hk hl (Dvd.intro_left _ rfl) per ih).1
  have lamj : ∀ j, lam B c ((Uo l)^[j] ((Uo l)^[m] a)) = α ^ j * lam B c ((Uo l)^[m] a) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', hE.U _ (mfj j), ih, pow_succ]
      ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold val
  rw [add_comm m j, Function.iterate_add_apply, lamj, pow_add]
  have hj : α ^ j ≠ 0 := pow_ne_zero _ hα
  field_simp

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, theta ψ (a * b) = theta ψ a * theta ψ b := by
  first | exact @GlobalTheory.PsType.theta_mul | exact GlobalTheory.PsType.theta_mul | (intros; apply GlobalTheory.PsType.theta_mul <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.sumPairingGramMatrix_values_and_definite : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Fintype C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam), (∀ x y : Fin N → K, star x ⬝ᵥ sumGram lam e G *ᵥ y = ∑ c, pairK lam G (valAt lam e c x) (valAt lam e c y)) ∧ IsDefGram (sumGram lam e G) ∧ IsDefGram ((sumGram lam e G)⁻¹)ᵀ ∧ (∀ τ, IsUnit (G τ).det) := by
  first | exact @GlobalTheory.TestLat.sumGram_spec | exact GlobalTheory.TestLat.sumGram_spec | (intros; apply GlobalTheory.TestLat.sumGram_spec <;> assumption)
end

section

open GlobalTheory.K5

theorem GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (S : Finset Ω), (∀ s ∈ S, IsInt (p := p) s) → ∀ j : ℕ, 1 ≤ j →
  ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧ (∀ g ∈ E, g ∈ ⨅ n, Gn T n) ∧
    (∀ h ∈ ⨅ n, Gn T n, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
    ∑ g ∈ E, g y = T.ζ j - 1 :=
  fun p _ hp Ω _ _ hc T S _ j hj => GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp hc T _ le_rfl S j hj
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.badLabelTuple_weight_le_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m q d : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → PrimeOK g q d → (∀ v, IsSeries (τ v)) → ∃ w : ℝ, conv (dirac - eGood τ ch) (tens fun v => (L v).e) 1 = (w : ℂ) * (tens fun v => (L v).e) 1 ∧ w ≤ badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) := by
  first | exact @GlobalTheory.BadShare.badWeight_le | exact GlobalTheory.BadShare.badWeight_le | (intros; apply GlobalTheory.BadShare.badWeight_le <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.taylorConjugate_tangentSpacePadZeroColumns : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  first | exact @GlobalTheory.ConjRestrict.fnConj_pad | exact GlobalTheory.ConjRestrict.fnConj_pad | (intros; apply GlobalTheory.ConjRestrict.fnConj_pad <;> assumption)
end
