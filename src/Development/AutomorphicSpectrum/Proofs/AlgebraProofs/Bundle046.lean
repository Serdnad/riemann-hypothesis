module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle041
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GaussianSphereMeanIntegral
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle010
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
import Mathlib.Topology.UniformSpace.Uniformizable
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaTest

theorem mem_of_test_ideal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ (L : AddSubgroup Ω), LocFree R 1 L → ∀ v : Ω, (∃ m : ℕ, (p : Ω) ^ m * v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → algebraMap Ω C v ∈ spanOver RC (algebraMap Ω C '' L)) → v ∈ L := by
  intro o Ω _ _ _ R p hp hp0 hN hF hI L hL v hm htest
  let e : Ω ≃ₗ[Ω] (Unit → Ω) := (LinearEquiv.funUnique Unit Ω Ω).symm
  have hL' : LocFree R 1 (L.map e.toLinearMap.toAddMonoidHom) :=
    LatticeGoodness.locFree_map_equiv R e hL
  have hmem : ∀ x : Ω, e x ∈ L.map e.toLinearMap.toAddMonoidHom ↔ x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine (hmem v).1 (GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI 1 _ hL' (e v) ?_ ?_)
  · obtain ⟨m, hm⟩ := hm
    refine ⟨m, ?_⟩
    have : (p : Ω) ^ m • e v = e ((p : Ω) ^ m * v) := by
      rw [← smul_eq_mul, map_smul]
    rw [this]
    exact (hmem _).2 hm
  · intro C _ _ _ _ RC ht
    let g : C →+ (Unit → C) :=
      (LinearEquiv.funUnique Unit C C).symm.toLinearMap.toAddMonoidHom
    have hg : bcMap Ω C Unit (e v) = g (algebraMap Ω C v) := by
      funext u
      simp [bcMap, e, g]
    rw [hg]
    have h1 := AddSubgroup.mem_map_of_mem g (htest C RC ht)
    unfold spanOver at h1 ⊢
    rw [AddMonoidHom.map_closure] at h1
    refine (AddSubgroup.closure_mono ?_) h1
    rintro _ ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, bcMap Ω C Unit (e x), ⟨e x, (hmem x).2 hx, rfl⟩, ?_⟩
    funext u
    simp [bcMap, e, g]

end GlobalTheory.CompanionTheory.Ar.Num.HaTest
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil

section
variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] {W : Type} [AddCommGroup W]
  [Module C W]

theorem eigProj_comp_bar [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C)
    (ρ : 𝓞 E →+* Module.End C W) (hsum : ∀ y, ∑ s, HT.eigProj ρ s y = y)
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hbar : ∀ a, bar (bar a) = a) (x : W) :
    HT.eigProj (ρ.comp (bar : 𝓞 E →+* 𝓞 E)) σ x = HT.eigProj ρ σ' x := by
  classical
  conv_lhs => rw [← hsum x]

  rw [map_sum, Finset.sum_eq_single σ']
  · apply HT.LatBasic.eigProj_of_mem
    rw [HT.LatBasic.mem_eigSp]
    intro a
    have h := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ σ' x) (bar a)
    rw [hσ, hbar] at h
    exact h
  · intro s _ hs
    refine HT.LatBasic.eigProj_of_eigenSub_ne
      (χ := (s.comp (algebraMap (𝓞 E) E)).comp (bar : 𝓞 E →+* 𝓞 E)) ?_ ?_
    · intro e
      apply hs
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      refine RingHom.ext fun a => ?_
      have h := DFunLike.congr_fun e (bar a)
      have h2 : σ ((bar a : 𝓞 E) : E) = s (a : E) := by
        simpa [hbar] using h
      change s (a : E) = σ' (a : E)
      rw [hσ, h2]
    · rw [GlobalTheory.EigenSplit.mem_eigenSub]
      intro a
      exact HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ s x) (bar a)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eigProj_zero_form (bar : 𝓞 E ≃+* 𝓞 E) (σ : E →+* C) (ρ : 𝓞 E →+* Module.End C W)
    (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
    (hact : ∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) (φ : Module.Dual C W) :
    HT.eigProj ρH σ (0, φ) = (0, φ ∘ₗ HT.eigProj (ρ.comp (bar : 𝓞 E →+* 𝓞 E)) σ) := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hact]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · ext x
    simp [Prod.snd_sum, LinearMap.sum_apply]

end

theorem span_iff_proj : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [Field C] [Algebra V C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (n : ℕ) (w : Fin n → W) (ψ : Fin n → W × Module.Dual C W), (∀ y, ∑ s, HT.eigProj ρ s y = y) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → Submodule.span C (Set.range w) = HT.eigSp ρ σ' → (∀ j, w j ∈ Lie) → (∀ j, ψ j ∈ HT.eigSp ρH σ ∧ (ψ j).1 = 0 ∧ ∀ j', (ψ j).2 (w j') = if j = j' then 1 else 0) → (∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0) → ∀ y, y ∈ Submodule.span V (Set.range ψ) ↔ ∃ φ : Module.Dual C W, ((0, φ) : W × Module.Dual C W) ∈ HV ∧ HT.eigProj ρH σ (0, φ) = y := by
  intro E _ _ V C _ _ _ _ bar σ σ' W _ _ _ _ ρ ρH HV Lie n w ψ hsum hσ hbar _ hact hlat hspan hwL hψ hint y
  classical

  have hform : ∀ φ : Module.Dual C W, HT.eigProj ρH σ (0, φ) = (0, φ ∘ₗ HT.eigProj ρ σ') := by
    intro φ
    rw [eigProj_zero_form bar σ ρ ρH hact φ]
    refine Prod.ext rfl ?_
    ext x
    simp only [LinearMap.comp_apply]
    rw [eigProj_comp_bar bar σ σ' ρ hsum hσ hbar x]
  have hψe : ∀ j, ψ j = (0, (ψ j).2) := fun j => Prod.ext (hψ j).2.1 rfl

  have hχ : ∀ j x, (ψ j).2 x = (ψ j).2 (HT.eigProj ρ σ' x) := by
    intro j x
    have h := HT.LatBasic.eigProj_of_mem (hψ j).1
    rw [hψe j, hform] at h
    have h2 := congrArg (fun z : W × Module.Dual C W => z.2 x) h
    exact h2.symm

  have hexp : ∀ x, HT.eigProj ρ σ' x = ∑ j, (ψ j).2 x • w j := by
    intro x
    have hm : HT.eigProj ρ σ' x ∈ Submodule.span C (Set.range w) := by
      rw [hspan]; exact HT.LatBasic.eigProj_mem ρ σ' x
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hm
    have hcj : ∀ j, (ψ j).2 x = c j := by
      intro j

      rw [hχ j x, ← hc, map_sum]
      simp [(hψ j).2.2]
    simp only [hcj]
    exact hc.symm

  have key : ∀ φ : Module.Dual C W, HT.eigProj ρH σ (0, φ) = ∑ j, φ (w j) • ψ j := by
    intro φ
    rw [hform]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, (hψ _).2.1]
    · ext x
      simp only [LinearMap.comp_apply]

      rw [hexp x, map_sum, Prod.snd_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]

  have hsm : ∀ (v : V) (z : W × Module.Dual C W), v • z = algebraMap V C v • z := by
    intro v z
    refine Prod.ext ?_ ?_
    · simp
    · ext x
      simp [Algebra.smul_def]
  constructor
  · intro hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hy
    choose φ hφ1 hφ2 using hint
    refine ⟨∑ j, algebraMap V C (c j) • φ j, ?_, ?_⟩
    · rw [hlat]
      intro e he
      rw [LinearMap.sum_apply]
      refine Subring.sum_mem _ fun j _ => ?_
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ ⟨c j, rfl⟩ (hφ1 j e he)
    · rw [key]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (∑ j, algebraMap V C (c j) • φ j) (w k) = algebraMap V C (c k) := by
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hφ2, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
      rw [hsm, hk]
  · rintro ⟨φ, h0, rfl⟩
    rw [key]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨v, hv⟩ := (hlat φ).1 h0 (w j) (hwL j)
    rw [← hv, ← hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil
end
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank

theorem comp_eigProj_eq {E : Type} [Field E] [NumberField E] {C : Type} [Field C]
    [Fintype (E →+* C)] {W : Type} [AddCommGroup W] [Module C W]
    {ρ : 𝓞 E →+* Module.End C W} {s' : E →+* C}
    (hsum : ∀ y, ∑ t, HT.eigProj ρ t y = y) {φ : Module.Dual C W}
    (hφ : ∀ a : 𝓞 E, φ ∘ₗ ρ a = s' (a : E) • φ) :
    φ ∘ₗ HT.eigProj ρ s' = φ := by
  classical
  ext y
  have key : ∀ t, t ≠ s' → φ (HT.eigProj ρ t y) = 0 := by
    intro t ht
    have hmem := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ t y)
    have hex : ∃ a : 𝓞 E, t (a : E) ≠ s' (a : E) := by
      by_contra hc
      push_neg at hc
      exact ht (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
    obtain ⟨a, ha⟩ := hex
    have h1 := LinearMap.congr_fun (hφ a) (HT.eigProj ρ t y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hmem a, map_smul, smul_eq_mul] at h1
    have h2 : (t (a : E) - s' (a : E)) * φ (HT.eigProj ρ t y) = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
  have e : φ y = φ (HT.eigProj ρ s' y) := by
    conv_lhs => rw [← hsum y]

    rw [map_sum, Finset.sum_eq_single s' (fun t _ ht => key t ht) (by simp)]
  exact e.symm

theorem finrank_eigSp_inf_ker_fst :
    ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  intro E _ _ C _ _ bar s s' W _ _ _ ρ ρH hsum hs hbar hH
  set U := HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) with hU
  set T := HT.eigSp ρ s' with hT
  let F : U →ₗ[C] Module.Dual C T :=
    T.dualRestrict ∘ₗ LinearMap.snd C W (Module.Dual C W) ∘ₗ U.subtype
  have hFapply : ∀ (u : U) (x : T), F u x = (u : W × Module.Dual C W).2 x := fun _ _ => rfl
  have hfst : ∀ u : U, (u : W × Module.Dual C W).1 = 0 := fun u => u.2.2
  have hact : ∀ u : U, ∀ a : 𝓞 E,
      (u : W × Module.Dual C W).2 ∘ₗ ρ a = s' (a : E) • (u : W × Module.Dual C W).2 := by
    intro u a
    have h1 := HT.LatBasic.mem_eigSp.1 u.2.1 (bar a)
    have h2 : (u : W × Module.Dual C W) = (0, (u : W × Module.Dual C W).2) :=
      Prod.ext (hfst u) rfl
    rw [h2, hH, hbar] at h1
    have h3 := congrArg Prod.snd h1
    simpa [hs a] using h3
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 := comp_eigProj_eq hsum (hact u)
    apply Subtype.ext
    refine Prod.ext (hfst u) ?_
    rw [← h0]
    ext y
    have := hFapply u ⟨HT.eigProj ρ s' y, HT.LatBasic.eigProj_mem ρ s' y⟩
    rw [hu] at this
    simpa using this.symm
  have hsurj : Function.Surjective F := by
    intro ψ
    let e : W →ₗ[C] T := LinearMap.codRestrict T (HT.eigProj ρ s') (HT.LatBasic.eigProj_mem ρ s')
    have he : ∀ (b : 𝓞 E) (x : W), e (ρ b x) = s' (b : E) • e x := fun b x =>
      Subtype.ext (HodgeDeterminantLattice.eigProj_act s' b x)
    have hmem : ((0 : W), ψ ∘ₗ e) ∈ U := by
      refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, rfl⟩
      rw [hH]
      refine Prod.ext (by simp) ?_
      ext x
      simp [he, hs, hbar]
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    rw [hFapply]
    have : e x = x := Subtype.ext (HT.LatBasic.eigProj_of_mem x.2)
    simp [this]
  rw [(LinearEquiv.ofBijective F ⟨hinj, hsurj⟩).finrank_eq, Subspace.dual_finrank_eq]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank
end
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups : ∀ (n e : ℕ) (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ),
  IntegrableOn (fun u => G (nrmGroups h e u)) (ballProd h e) →
    Integrable (fun π : Fin (e + 1) → Fin n → ℂ => G (nrmGroups h e (coefRows h π))) (gaussM (e + 1) n) ∧
      ∫ π, G (nrmGroups h e (coefRows h π)) ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * sphereMean h e G := by
  intro n e h G hint
  have hfin := (gaussM_univ_pos_lt_top (e + 1) n).2
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hfin⟩
  haveI : IsFiniteMeasure (volume.restrict (ballProd h e)) := ⟨by rw [Measure.restrict_apply_univ]; exact volume_ballProd_lt_top h e⟩
  obtain ⟨a, ha⟩ := ModelDimension.GSph.map_coefRows (e := e) h
  have hmap : Measure.map (coefRows h) (gaussM (e + 1) n) = Measure.map ModelDimension.GSph.scT ((a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)).prod (volume.restrict (ballProd h e))) := by
    rw [ha, ModelDimension.GSph.layer, Measure.prod_smul_left, Measure.map_smul]
    exact ModelDimension.GSph.measurable_scT.aemeasurable
  have h1 : ∀ᵐ x ∂ModelDimension.GSph.ex1, 0 < x :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hp : ∀ᵐ s ∂(ModelDimension.GSph.exP e), ∀ i, 0 < s i := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin e => ModelDimension.GSph.ex1) (i := i)).eventually h1
  have hpos0 : ∀ᵐ s ∂((ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ i, 0 < s i :=
    (withDensity_absolutelyContinuous _ _).ae_le hp
  have hpos : ∀ᵐ s ∂(a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ i, 0 < s i :=
    Measure.ae_smul_measure hpos0 a
  have hne : (volume.restrict (ballProd h e)) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact (volume_ballProd_pos h e).ne'
  have haesm : AEStronglyMeasurable (fun u => G (nrmGroups h e u)) (Measure.map (coefRows h) (gaussM (e + 1) n)) := by
    rw [ha]
    exact ((ModelDimension.GSph.aesm h G hint.1).mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure a
  have hinv : ∀ᵐ s ∂(a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ u, (fun u => G (nrmGroups h e u)) (ModelDimension.GSph.scT (s, u)) = (fun u => G (nrmGroups h e u)) u := by
    filter_upwards [hpos] with s hs u
    exact congrArg G (ModelDimension.GSph.nrm_sc h (fun i => Real.sqrt_pos.mpr (hs i)) u)
  have key := ModelDimension.GSph.transfer (gaussM (e + 1) n) (a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)) (volume.restrict (ballProd h e)) hne (ModelDimension.GSph.measurable_coefRows h) ModelDimension.GSph.measurable_scT hmap haesm hinv hint
  refine ⟨key.1, ?_⟩
  rw [key.2]
  rfl
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.chart_bundle_base_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullExists.main | exact GlobalTheory.CompanionTheory.Ar.Num.PullExists.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullExists.main <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
  (mseg joinCoord IsPull SameGeneric)

theorem main :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
      [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (z : (Σ k, ι' k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
      (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' →
      ∃ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V,
        IsPull O x z E EB ∧ IsPull O x z E' E'B ∧ SameGeneric O (joinCoord x z) EB E'B := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z N V _ _ E E' hE
  obtain ⟨EB, hEB⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E).1 K' ι' z
  obtain ⟨E'B, hE'B⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V E').1 K' ι' z
  exact ⟨EB, E'B, hEB, hE'B,
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z EB E'B hEB hE'B).2.1 hE⟩

end GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt
end

section


theorem _root_.GlobalTheory.T.pullback_cone_null_mod_p_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | exact GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP <;> assumption)
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem _root_.GlobalTheory.T.lattice_span_intersection_basis : ∀ (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (Lie : Submodule V W) (n : ℕ) (w : Fin n → W), Lie.FG → Submodule.span C (Lie : Set W) = ⊤ → LinearIndependent C w → (∀ y, y ∈ Submodule.span V (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w)) → ∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_dual_integral_of_saturated_free_part | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_dual_integral_of_saturated_free_part | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_dual_integral_of_saturated_free_part <;> assumption)
end
