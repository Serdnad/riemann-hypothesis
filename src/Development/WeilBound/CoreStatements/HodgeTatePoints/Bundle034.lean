module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle113
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle031
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFlat
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle027
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle008
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsVanishingIdeal
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle008
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle026
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle033
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

noncomputable section

namespace PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  show IsLocalRing (genMap ξ p).range
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have e : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have ha : (a : Ω) ≠ 0 := fun h0 => by simp [h0] at e
    refine ⟨ha, a.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right e]
    exact b.2
  · rintro ⟨h0, -, h2⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem unitAt_iff_of_dominated {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'} {q : Cpt ξ}
    (h : (∀ a ∈ regAt ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ q, unitAt ξ' p' (i a) → unitAt ξ q a)
    {a : Ω} (ha : a ∈ regAt ξ q) : unitAt ξ q a ↔ unitAt ξ' p' (i a) := by
  refine ⟨fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 a hu.2.1, ?_⟩, h.2 a ha⟩
  rw [← map_inv₀]
  exact h.1 _ hu.2.2

theorem eq_of_dominated_of_inChart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {i : Ω →+* Ω'} {p' : Cpt ξ'} {c : κ} {q r : Cpt M.ξ} (hq : InChart M.ξ x c q) (hr : InChart M.ξ x c r)
    (dq : (∀ a ∈ regAt M.ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q, unitAt ξ' p' (i a) → unitAt M.ξ q a)
    (dr : (∀ a ∈ regAt M.ξ r, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ r, unitAt ξ' p' (i a) → unitAt M.ξ r a) :
    q = r := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.CompanionTheory.Ar.Centre.Sep.eq_of_dominated_of_inChart <;> assumption

theorem eq_of_dominated : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' q₁ q₂ d₁ d₂
  obtain ⟨c₁, hc₁⟩ := M.tie.cover q₁
  obtain ⟨c₂, hc₂⟩ := M.tie.cover q₂
  have hctr : p' ∈ ctrSet o x i ξ' :=
    ⟨c₁, hc₁.1, fun a ha => d₁.1 a ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c₁ q₁ hc₁).1 a ha)⟩
  obtain ⟨p₀, d₀, -, hp₀⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M X' Ω' ξ' i p' hctr
  have e₁ : q₁ = p₀ := eq_of_dominated_of_inChart M hc₁ (hp₀ c₁ hc₁.1 fun j => d₁.1 _ (hc₁.2 j)) d₁ d₀
  have e₂ : q₂ = p₀ := eq_of_dominated_of_inChart M hc₂ (hp₀ c₂ hc₂.1 fun j => d₂.1 _ (hc₂.2 j)) d₂ d₀
  exact e₁.trans e₂.symm

end PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.centre_unique : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ :=
  @PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep.eq_of_dominated
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Htat.HopfOrderTop

private theorem btOrder_top_isHopfOrder' (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group)
    (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R' : Type) [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    [HenselianLocalRing R'] (T : Type) [CommGroup T] [Finite T] (Γ' : QFGroup R' T) :
    IsHopfOrder (Γ'.btOrder ⊤) := by
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  have hU : Γ'.IsFinOpenSub (GlobalTheory.finitePart Γ'.G.hom) := by
    apply QFGroup.isFinOpenSub_of_closedFibre
    · exact GlobalTheory.isFinite_finitePart (R := CommRingCat.of R') Γ'.G.hom
    · intro x hx
      exact GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R') _ x hx
  rw [← PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular R' T Γ' _ hU]
  exact PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub R' T Γ' _ hU

private theorem exists_smul_mem_of_extOrder {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {T : Type} [CommGroup T] [Finite T] (A : Subalgebra R (T → R))
    (hA : ∀ g : T → K, g ∈ extOrder (algebraMap R K) A) :
    ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A := by
  classical
  have key : ∀ x ∈ extOrder (algebraMap R K) A, ∃ s : R, s ≠ 0 ∧ ∃ a ∈ A,
      algebraMap R K s • x = fun t => algebraMap R K (a t) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨1, one_ne_zero, a, ha, by simp⟩
    | algebraMap k =>
      obtain ⟨⟨n, ⟨s, hs⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
      refine ⟨s, nonZeroDivisors.ne_zero hs, algebraMap R (T → R) n, Subalgebra.algebraMap_mem A n, ?_⟩
      funext t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [mul_comm]
      exact hk
    | add x y _ _ hx hy =>
      obtain ⟨s1, hs1, a1, ha1, e1⟩ := hx
      obtain ⟨s2, hs2, a2, ha2, e2⟩ := hy
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, s2 • a1 + s1 • a2, A.add_mem (A.smul_mem ha1 _) (A.smul_mem ha2 _), ?_⟩
      funext t
      have h1 := congrFun e1 t
      have h2 := congrFun e2 t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, map_mul, map_add (f := _)] at h1 h2 ⊢
      linear_combination (algebraMap R K s2) * h1 + (algebraMap R K s1) * h2
    | mul x y _ _ hx hy =>
      obtain ⟨s1, hs1, a1, ha1, e1⟩ := hx
      obtain ⟨s2, hs2, a2, ha2, e2⟩ := hy
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, a1 * a2, A.mul_mem ha1 ha2, ?_⟩
      funext t
      have h1 := congrFun e1 t
      have h2 := congrFun e2 t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul] at h1 h2 ⊢
      linear_combination (algebraMap R K s2 * y t) * h1 + (algebraMap R K (a1 t)) * h2
  choose s hs a ha e using fun t : T =>
    key _ (hA (fun u => algebraMap R K ((Pi.single t (1 : R) : T → R) u)))
  haveI := Fintype.ofFinite T
  have hδ : ∀ t, s t • (Pi.single t (1 : R) : T → R) = a t := by
    intro t
    funext u
    apply IsFractionRing.injective R K
    have := congrFun (e t) u
    simpa [Algebra.smul_def] using this
  refine ⟨∏ t, s t, Finset.prod_ne_zero_iff.mpr fun t _ => hs t, fun f => ?_⟩
  have hmem : (∏ t, s t) • f = ∑ t, (f t * ∏ t' ∈ Finset.univ.erase t, s t') • a t := by
    funext u
    simp only [← hδ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_prod_erase _ s (Finset.mem_univ u)]
    ring
  rw [hmem]
  exact A.sum_mem fun t _ => A.smul_mem (ha t) _

theorem btOrder_top_isHopfOrder (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) : IsHopfOrder (Γ.btOrder ⊤) := by
  classical
  refine PositivityTheory.HtPt.Htat.HopfOrderFlatLocal.isHopfOrder_of_flat_local R T _ ?_ ?_
  · obtain ⟨ΓK, F, hbc⟩ := hBaseChange R T Γ (FractionRing R) (algebraMap R (FractionRing R))
      (IsFractionRing.injective R _)
    have hK := btOrder_top_isHopfOrder' hHenselian hBaseChange hRegular (FractionRing R) T ΓK
    rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange R T Γ _ ΓK F hbc inferInstance] at hK
    obtain ⟨d', hd', hd'm⟩ := hK.full
    refine exists_smul_mem_of_extOrder (K := FractionRing R) _ fun g => ?_
    have := hd'm (d'⁻¹ • g)
    rwa [smul_smul, mul_inv_cancel₀ hd', one_smul] at this
  · intro P hP
    haveI := hP.isPrime
    obtain ⟨R', iR, iD, iH, iA, hic, hfl, hcomap⟩ := hHenselian R P
    have hinj : Function.Injective (algebraMap R R') := PositivityTheory.HtPt.Htat.ValuationInjectivePi.flat_inj
    obtain ⟨Γ', F, hbc⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
    refine ⟨R', iR, iD, inferInstance, iA, hfl, hcomap, ?_⟩
    rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange R T Γ R' Γ' F hbc hfl]
    exact btOrder_top_isHopfOrder' hHenselian hBaseChange hRegular R' T Γ'

end PositivityTheory.HtPt.Htat.HopfOrderTop

theorem PositivityTheory.HtPt.Htat.bt_hopf_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  @PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder hHenselian hBaseChange hRegular
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem trivflag_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : Top.RootModel Ψ N) [CharZero M.Ω] (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o M.Ω] (ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω)), (∀ τ, Num.TrivFlagMod o (p : o) M.y N (fun i => M.xdeg (τ, i))) → ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0 := by
  intro Ψ _ N M _ p _ o _ _ ho hτ mu hmu
  intro W hW
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have key : ∀ τ : Ψ, 0 ≤ ∑ i : Fin N, mu τ i * (-(geoNum 1 W (fun _ : Fin 1 => M.xdeg (τ, i)) : ℝ)) := by
    intro τ
    obtain ⟨hp, ht⟩ := trivflag_deg M.Ω M.K M.ι M.y p o ho W N (fun i => M.xdeg (τ, i)) h1 h2 h3 h4 (hτ τ)
    apply abel_sum N (mu τ) (fun i => -(geoNum 1 W (fun _ : Fin 1 => M.xdeg (τ, i)) : ℝ))
    · intro a b hab
      exact hmu τ a b hab
    · intro i hi
      have := hp i hi
      simp only [Finset.sum_neg_distrib, neg_nonneg]
      exact_mod_cast this
    · simp only [Finset.sum_neg_distrib, neg_eq_zero]
      exact_mod_cast ht
  unfold Top.RootModel.curveDeg
  rw [Fintype.sum_option]
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, M.x_deg]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_nonneg fun τ _ => ?_
  refine le_of_le_of_eq (key τ) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end PositivityTheory.HtPt.Gf
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.HtPt.Pflag

def idxList {N : ℕ} (α : Fin N → ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun i => List.replicate (α i) i

theorem count_idxList {N : ℕ} (α : Fin N → ℕ) (j : Fin N) : (idxList α).count j = α j := by
  classical
  simp only [idxList, List.count_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp [List.count_replicate]

theorem length_idxList {N : ℕ} (α : Fin N → ℕ) : (idxList α).length = ∑ i, α i := by
  simp only [idxList, List.length_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

theorem map_idxList {K : Type} {N : ℕ} (x : Fin N → K → ℤ) (α : Fin N → ℕ) :
    (idxList α).map x = rootList x α := by
  simp [idxList, rootList, List.map_flatMap, List.map_replicate]

theorem prod_map_X {σ : Type} [DecidableEq σ] (s : Multiset σ) :
    ((s.map X).prod : MvPolynomial σ ℝ) = monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add (f := _),
      Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]

theorem length_classList_of_hom {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) : (classList cls μ).length = m := by
  classical
  have h := hH (mem_support_iff.mp hμ)
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem isHomogeneous_hsymm_real (N a : ℕ) : (hsymm (Fin N) ℝ a).IsHomogeneous a := by
  classical
  apply IsHomogeneous.sum
  intro s _
  rw [prod_map_X]
  apply isHomogeneous_monomial
  have h := Finsupp.card_toMultiset (Multiset.toFinsupp (s : Multiset (Fin N)))
  rw [Multiset.toFinsupp_toMultiset] at h
  calc Finsupp.degree (Multiset.toFinsupp (s : Multiset (Fin N)))
      = (Multiset.toFinsupp (s : Multiset (Fin N))).sum fun _ => id := rfl
    _ = a := by rw [← h]; simp

section
variable (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
  [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F))

theorem genNum_hsymm {N : ℕ} (x : Fin N → K → ℤ) (a : ℕ) (Q : List (K → ℤ)) :
    genNum F V x (hsymm (Fin N) ℝ a) Q =
      ((∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F V (rootList x α ++ Q) : ℤ) : ℝ) := by
  classical
  rw [hsymm, (genNum_linear F K ι (Fin N) V x Q).2.2.1]
  simp_rw [prod_map_X, (genNum_linear F K ι (Fin N) V x Q).2.2.2, one_mul]
  push_cast
  symm
  refine Finset.sum_bij'
    (fun α hα => (⟨(idxList α : Multiset (Fin N)), by
      rw [Multiset.coe_card, length_idxList, (Finset.Nat.mem_antidiagonalTuple.mp hα)]⟩ : Sym (Fin N) a))
    (fun s _ => fun i => (s : Multiset (Fin N)).count i) ?_ ?_ ?_ ?_ ?_
  · intro α _
    exact Finset.mem_univ _
  · intro s _
    rw [Finset.Nat.mem_antidiagonalTuple]
    rw [← Finset.sum_subset (Finset.subset_univ (s : Multiset (Fin N)).toFinset)]
    · rw [Multiset.toFinset_sum_count_eq]
      exact s.2
    · intro i _ hi
      simpa using hi
  · intro α _
    funext i
    simp [Multiset.coe_count, count_idxList]
  · intro s _
    apply Subtype.ext
    ext i
    simp [Multiset.coe_count, count_idxList]
  · intro α _
    rw [intNumL_perm_of_perm F K ι V (rootList x α ++ Q) _]
    apply List.Perm.append_right
    rw [← map_idxList]
    rw [← Multiset.coe_eq_coe]
    simp [classList, Multiset.toFinsupp_toMultiset]

theorem genNum_neg (d : ℕ) (hV : IsMultiProjPrime V)
    (hd : ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) {N : ℕ}
    (b : Fin N → K → ℤ) (H : MvPolynomial (Fin N) ℝ) (m : ℕ) (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    genNum F V b (aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) H) Q =
      genNum F V (fun i => -b i) H Q := by
  classical
  have h := genNum_linear_subst F K ι V d hV hd (Fin N) (Fin N) b
    (fun t i => if t = i then -1 else 0) H m hH Q hQ
  have e1 : (fun t : Fin N => ∑ i : Fin N, (if t = i then (-1 : ℤ) else 0) • b i) =
      fun t => -b t := by
    funext t
    simp
  have e2 : (fun t : Fin N => ∑ i : Fin N,
      C (((if t = i then (-1 : ℤ) else 0 : ℤ) : ℝ)) * (X i : MvPolynomial (Fin N) ℝ)) =
      fun t => (-X t : MvPolynomial (Fin N) ℝ) := by
    funext t
    simp only [apply_ite (fun z : ℤ => ((z : ℝ))), Int.cast_neg, Int.cast_one, Int.cast_zero,
      apply_ite C, map_neg, map_one, map_zero, ite_mul, neg_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ t (fun i => -(X i : MvPolynomial (Fin N) ℝ))]
    simp
  rw [e1, e2] at h
  exact h.symm

end

end PositivityTheory.HtPt.Pflag
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {A : Type} [Fintype A] {κa : A → Type} (w : ∀ a, κa a → Ω)

theorem inChart_prod_of_forall (p : Cpt ξ) (h : ∀ a, ∃ l, InChart ξ (w a) l p) :
    ∃ c, InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p := by
  choose c hc using h
  refine ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => (hc a).1, fun c' => ?_⟩
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun a _ => (hc a).2 (c' a)

theorem inChart_of_inChart_prod [DecidableEq A] {p : Cpt ξ} {c : ∀ a, κa a}
    (h : InChart ξ (fun c : (∀ a, κa a) => ∏ a, w a (c a)) c p) (a : A) : InChart ξ (w a) (c a) p := by
  obtain ⟨h0, h1⟩ := h
  have hne : ∀ b, w b (c b) ≠ 0 := fun b => (Finset.prod_ne_zero_iff.1 h0) b (Finset.mem_univ b)
  refine ⟨hne a, fun l => ?_⟩
  have key : (∏ b, w b (Function.update c a l b)) / (∏ b, w b (c b)) = w a l / w a (c a) := by
    rw [← Finset.prod_div_distrib, Fintype.prod_eq_single a]
    · simp
    · intro b hb
      simp [Function.update_of_ne hb, div_self (hne b)]
  rw [← key]
  exact h1 _

end PositivityTheory.HtPt.Mb.LJoinMany.JoinMany

namespace PositivityTheory.HtPt.Mb.LJoinMany

theorem join_finitely_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M A _ κa _ w hw
  classical
  haveI := Fintype.ofFinite A
  have hW : ∃ l : (∀ a, κa a), (∏ a, w a (l a)) ≠ 0 := by
    choose c hc using hw
    exact ⟨c, Finset.prod_ne_zero_iff.2 fun a _ => hc a⟩
  have hcl : Subfield.closure (Set.range (RingHom.id Ω) ∪
      {z | ∃ l l' : (∀ a, κa a), z = (∏ a, w a (l a)) / ∏ a, w a (l' a)}) = ⊤ :=
    eq_top_iff.2 fun z _ => Subfield.subset_closure (Or.inl ⟨z, rfl⟩)
  obtain ⟨M', f, hf⟩ := PositivityTheory.HtPt.Mb.join_exists o Ω κ x M Ω (RingHom.id Ω) (∀ a, κa a)
    (fun c => ∏ a, w a (c a)) (fun _ => rfl) hW hcl
  refine ⟨κ × (∀ a, κa a), inferInstance, _, M', f, hf, ?_, ?_⟩
  · intro a p'
    obtain ⟨-, c, hc⟩ := PositivityTheory.HtPt.Mb.join_charts o Ω κ (∀ a, κa a) x Ω (RingHom.id Ω)
      (fun c => ∏ a, w a (c a)) M' (fun _ => rfl) p'
    exact ⟨c a, JoinMany.inChart_of_inChart_prod _ w hc a⟩
  · intro p hp
    exact PositivityTheory.HtPt.Mb.join_iso o Ω κ x M (∀ a, κa a) (fun c => ∏ a, w a (c a)) M' f hf p
      (JoinMany.inChart_prod_of_forall _ w p hp)

end PositivityTheory.HtPt.Mb.LJoinMany


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.join_many : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω), (∀ a, ∃ l, w a l ≠ 0) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinMany.join_finitely_many
end
