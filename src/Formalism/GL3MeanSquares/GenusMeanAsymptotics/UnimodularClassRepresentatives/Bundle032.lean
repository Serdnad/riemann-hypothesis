module

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle022
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem pow_smul_anti (𝔭 : Ideal (𝓞 F)) (A : Submodule (𝓞 K) V) {i j : ℕ} (hij : i ≤ j) :
    ((extP K 𝔭) ^ j • A : Submodule (𝓞 K) V) ≤ (extP K 𝔭) ^ i • A := Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)

theorem exists_pow_smul_le {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ((extP K 𝔭) ^ r • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂ := by
  apply Formalism.HermitianLattices.Ext.L3.D2.exists_smul_le <;> assumption

set_option linter.unusedVariables false in
theorem locF_inf {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A B : Submodule (𝓞 K) V}
    (hA : locF 𝔭 A = A) (hB : locF 𝔭 B = B) : locF 𝔭 (A ⊓ B) = A ⊓ B := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact (LocF.locF_mono 𝔭 inf_le_left).trans hA.le
    · exact (LocF.locF_mono 𝔭 inf_le_right).trans hB.le
  · exact LocF.le_locF 𝔭 _

theorem locF_inf_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A B : Submodule (𝓞 K) V) :
    locF 𝔭 (A ⊓ B) = locF 𝔭 A ⊓ locF 𝔭 B := by
  have := h𝔭.isPrime
  apply le_antisymm
  · exact le_inf (LocF.locF_mono 𝔭 inf_le_left) (LocF.locF_mono 𝔭 inf_le_right)
  · rintro x ⟨h1, h2⟩
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 A x).1 h1
    obtain ⟨t, ht, htx⟩ := (LocalSpans.mem_locF 𝔭 B x).1 h2
    refine (LocalSpans.mem_locF 𝔭 _ x).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩
    · rw [mul_comm, map_mul, mul_smul]
      exact A.smul_mem _ hsx
    · rw [map_mul, mul_smul]
      exact B.smul_mem _ htx

theorem isLattice_inf {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) : Submodule.IsLattice K (M₁ ⊓ M₂) := by
  have := hM₁
  exact Submodule.IsLattice.inf_left K M₁ M₂

theorem finite_quot_inf {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Finite (↥(locF 𝔭 M₁ ⊓ locF 𝔭 M₂) ⧸
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁ ⊓ locF 𝔭 M₂))) := by
  rw [← locF_inf_locF h𝔭]
  exact finite_quot (isLattice_inf hM₁ hM₂) h𝔭 k

theorem apply_mem_of_mem_autSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h A) {z : V} (hz : z ∈ A) : g z ∈ A := by
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg.2
  rw [← h2]
  exact Submodule.mem_map_of_mem hz

theorem apply_mem_smul_of_mem_autSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V}
    {g : V ≃ₗ[K] V} (hg : g ∈ autSub h A) (I : Ideal (𝓞 K)) {z : V} (hz : z ∈ I • A) :
    g z ∈ I • A := by
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg.2
  have h1 : g z ∈ (I • A).map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hz
  rwa [Submodule.map_smul'', h2] at h1

theorem congr_apply_mem {M₁ M₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {r₁ r₂ j : ℕ} (h1 : ((extP K 𝔭) ^ r₁ • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂)
    (h2 : ((extP K 𝔭) ^ r₂ • locF 𝔭 M₂ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₁) (hj : r₂ + r₁ ≤ j)
    (g : V ≃ₗ[K] V)
    (hg : ∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V))
    {z : V} (hz : z ∈ locF 𝔭 M₂) : g z ∈ locF 𝔭 M₂ := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  have hz1 : algebraMap F K (π : F) ^ r₂ • z ∈ locF 𝔭 M₁ :=
    h2 ((D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).2 ⟨z, hz, rfl⟩)
  have h3 := pow_smul_anti 𝔭 (locF 𝔭 M₁) hj (hg _ hz1)
  rw [pow_add, Submodule.mul_smul] at h3
  have h4 := Submodule.smul_mono (le_refl (extP K 𝔭 ^ r₂)) h1 h3
  obtain ⟨w, hw, e⟩ := (D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).1 h4
  rw [map_smul, ← smul_sub] at e
  have e' : g z - z = w :=
    smul_right_injective V (pow_ne_zero r₂ (D2.unif_ne_zero (K := K) hπ')) e
  have : g z = w + z := by rw [← e']; abel
  rw [this]
  exact add_mem hw hz

theorem exists_congr_mem_autSub (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsFullLattice K M₁) (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ g ∈ autSub h (locF 𝔭 M₁),
      (∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V)) →
      g ∈ autSub h (locF 𝔭 M₂) := by
  obtain ⟨r₁, h1⟩ := exists_pow_smul_le hM₁.toIsLattice hM₂ h𝔭
  obtain ⟨r₂, h2⟩ := exists_pow_smul_le hM₂.toIsLattice hM₁ h𝔭
  refine ⟨r₂ + r₁, fun j hj g hg hc => ⟨hg.1, ?_⟩⟩
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact congr_apply_mem h𝔭 h1 h2 hj g hc hz
  · intro x hx
    have hc' : ∀ z ∈ locF 𝔭 M₁,
        g.symm z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V) := by
      intro z hz
      have hz' : g.symm z ∈ locF 𝔭 M₁ := apply_mem_of_mem_autSub (inv_mem hg) hz
      have := neg_mem (hc _ hz')
      rwa [LinearEquiv.apply_symm_apply, neg_sub] at this
    exact ⟨g.symm x, congr_apply_mem h𝔭 h1 h2 hj g.symm hc' hx, by simp⟩

theorem orbCount_eq_relIndex (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule (𝓞 K) V) :
    orbCount h A B = (autSub h B).relIndex (autSub h A) := by
  let _ : MulAction (V ≃ₗ[K] V) (Submodule (𝓞 K) V) :=
    { smul := fun g L => Formalism.HermitianLatticesTheory.gmap g L
      one_smul := autSub_gmap_one
      mul_smul := autSub_gmap_mul }
  have hst : MulAction.stabilizer ↥(autSub h A) B = (autSub h B).subgroupOf (autSub h A) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      exact ⟨g.2.1, hg⟩
    · intro hg
      exact hg.2
  rw [Subgroup.relIndex, ← hst, Subgroup.index_eq_card,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ B)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro C
  constructor
  · rintro ⟨g, hg, hA, hB⟩
    exact ⟨⟨g, hg, hA⟩, hB⟩
  · rintro ⟨⟨g, hg, hA⟩, hB⟩
    exact ⟨g, hg, hA, hB⟩

theorem relIndex_ne_zero_of_map {G X : Type*} [Group G] [Finite X] (H Γ : Subgroup G) (f : H → X)
    (hf : ∀ a b : H, f a = f b → (a : G)⁻¹ * b ∈ Γ) : Γ.relIndex H ≠ 0 := by
  classical
  show (Γ.subgroupOf H).index ≠ 0
  have hfin : Finite (H ⧸ Γ.subgroupOf H) := by
    let g : Set.range f → H ⧸ Γ.subgroupOf H := fun x => QuotientGroup.mk x.2.choose
    apply Finite.of_surjective g
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      refine ⟨⟨f a, a, rfl⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk a
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hf _ _ (⟨f a, a, rfl⟩ : Set.range f).2.choose_spec
  exact Subgroup.index_ne_zero_of_finite

def resA {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (g : autSub h A) : ↥A →ₗ[𝓞 K] ↥A :=
  (((g : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict
    (fun _ hz => apply_mem_of_mem_autSub g.2 hz)

def redA {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K)) (g : autSub h A) :
    (↥A ⧸ (I • ⊤ : Submodule (𝓞 K) ↥A)) →ₗ[𝓞 K] (↥A ⧸ (I • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (resA g) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

theorem sub_mem_of_redA_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K))
    {a b : autSub h A} (e : redA I a = redA I b) {z : V} (hz : z ∈ A) :
    (b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z ∈ I • A := by
  have h1 := congrArg (fun φ => φ (Submodule.Quotient.mk (⟨z, hz⟩ : ↥A))) e
  simp only [redA, Submodule.mapQ_apply] at h1
  rw [eq_comm, Submodule.Quotient.eq] at h1
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) h1
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h2
  simp only [Submodule.subtype_apply] at h2
  exact h2

theorem relIndex_autSub_ne_zero (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsFullLattice K M₁) (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    (autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_congr_mem_autSub h hM₁ hM₂ h𝔭
  have := finite_quot hM₁.toIsLattice h𝔭 j
  have : Finite ((↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁))) →ₗ[𝓞 K]
      (↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁)))) :=
    Finite.of_injective _ DFunLike.coe_injective
  refine relIndex_ne_zero_of_map _ _ (redA (extP K 𝔭 ^ j)) fun a b e => ?_
  refine hj j le_rfl _ (mul_mem (inv_mem a.2) b.2) fun z hz => ?_
  have h1 := apply_mem_smul_of_mem_autSub (inv_mem a.2) _ (sub_mem_of_redA_eq _ e hz)
  have h2 : ((a : V ≃ₗ[K] V)⁻¹ * (b : V ≃ₗ[K] V)) z - z =
      (a : V ≃ₗ[K] V)⁻¹ ((b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z) := by
    rw [map_sub]
    change _ = (a : V ≃ₗ[K] V).symm _ - (a : V ≃ₗ[K] V).symm _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [h2]
  exact h1

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

section

open NumberField Module Matrix Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem alphaL_eq_of_bridge [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin (finrank K V) → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤)
    (hbr : ∀ k, akCount h L 𝔭 k = isoCount 𝔭 k (diagonal u)) :
    alphaL h L 𝔭 = alphaStd K 𝔭 (finrank K V) := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
      (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
        (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast this
  unfold alphaL
  apply Filter.Tendsto.limUnder_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [hbr, isoCount_diag hK h𝔭 u hu hunit j, eq_div_iff (pow_ne_zero _ hN)]
  ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCC

open WCA WCB

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (han : ∀ x, h x x = 0 → x = 0) {A : Submodule (𝓞 K) V} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1))
    {x y : V} (hx : InL 𝔭 A 0 x)
    (hxx : h x x = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n))
    (hyy : h y y = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n))
    {J : ℕ} (hJ : 1 ≤ J) (hw : InL 𝔭 A (v + (v + J)) (y - x)) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ z, InL 𝔭 A 0 z → InL 𝔭 A J (g z - z)) ∧
      (∀ z, InL 𝔭 A 0 z → InL 𝔭 A 0 (g.symm z)) ∧ g x = y := by
  classical
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨θ₀, hθ₀⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := idealPowerSpanBounds.exists_inv_theta (K := K) hθ₀ 1
  have hconj : κ (conjO K θ₀) = star (κ θ₀) := rfl
  set δ : K := κ θ₀ - star (κ θ₀) with hδ
  have hδe : InI 𝔭 1 (δ * κ e - 1) := by
    refine ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1),
      (θ₀ - conjO K θ₀) * e - 1, he, ?_⟩
    simp only [map_sub, map_mul, map_one, hδ, hconj, one_mul]
  obtain ⟨hne, hinv⟩ := InI.unit h𝔭 hF hδe
  have hδe' : 1 + (δ * κ e - 1) = δ * κ e := by ring
  rw [hδe'] at hne hinv
  have hδ0 : δ ≠ 0 := left_ne_zero_of_mul hne
  have he0 : κ e ≠ 0 := right_ne_zero_of_mul hne
  have hstarδ : star δ = -δ := by
    rw [hδ, star_sub, star_star]
    ring
  set l : K := κ θ₀ * δ⁻¹ with hl_def
  have hl : l + star l = 1 := by
    have h1 : l + star l = (κ θ₀ - star (κ θ₀)) * δ⁻¹ := by
      rw [hl_def, star_mul', star_inv₀, hstarδ, inv_neg]
      ring
    rw [h1]
    exact mul_inv_cancel₀ hδ0
  have hl0 : InI 𝔭 0 l := by
    have h1 := InI.mul hp (InI.int hp θ₀) (InI.mul hp (InI.int hp e) hinv)
    have h2 : κ e * (δ * κ e)⁻¹ = δ⁻¹ := by
      rw [mul_inv, mul_comm δ⁻¹, ← mul_assoc, mul_inv_cancel₀ he0, one_mul]
    rw [h2] at h1
    exact h1
  have hls0 : InI 𝔭 0 (star l) := InI.conj hF hl0
  set d : V := y - x with hd
  have hy : y = x + d := by simp [hd]
  have hexp : ∀ a b : V, h (a + b) (a + b) = h a a + h a b + h b a + h b b := by
    intro a b
    simp only [map_add (f := _), LinearMap.add_apply]
    ring
  have hdd : h x d + h d x + h d d = 0 := by
    have h1 := hexp x d
    rw [← hy, hyy, hxx] at h1
    linear_combination -h1
  set z₀ : V := x + star l • d with hz₀
  have hdL : InL 𝔭 A 0 (star l • d) := (InL.smul hp hls0 hw).mono (by omega)
  have hz₀L : InL 𝔭 A 0 z₀ := InL.add hp hx hdL
  have hsymm : ∀ a b : V, star (h a b) = h b a := fun a b => by
    simpa [starRingEnd_apply] using hs.eq a b
  set c : K := h z₀ z₀ with hc_def
  have hcstar : star c = c := hsymm z₀ z₀
  have hn0 : κ (ι n) ≠ 0 := κι_ne_zero hn
  have hcn : InI 𝔭 (v + (v + J)) (c - κ (ι n)) := by
    have h1 : c - κ (ι n) = h (star l • d) z₀ + h x (star l • d) := by
      rw [hc_def, hz₀]
      simp only [map_add (f := _), LinearMap.add_apply]
      rw [hxx]
      ring
    rw [h1]
    exact InI.add hp ((InL.form hp hF hA (InL.smul hp hls0 hw) hz₀L).mono (by omega))
      ((InL.form hp hF hA hx (InL.smul hp hls0 hw)).mono (by omega))
  set ε : K := (κ (ι n))⁻¹ * (c - κ (ι n)) with hε_def
  have hεv : InI 𝔭 (v + J) ε := InI.div h𝔭 hn hv hcn
  obtain ⟨hne', hinv'⟩ := InI.unit h𝔭 hF (hεv.mono (by omega))
  have hc : c = κ (ι n) * (1 + ε) := by
    rw [hε_def, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    ring
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero hn0 hne'
  have hcinv : c⁻¹ = (1 + ε)⁻¹ * (κ (ι n))⁻¹ := by
    rw [hc, mul_inv, mul_comm]
  set w : V := c⁻¹ • d with hw_def
  have hwv : InL 𝔭 A (v + J) w := by
    rw [hw_def, hcinv, mul_smul]
    exact (InL.smul hp hinv' (InL.div h𝔭 hn hv hw)).mono (by omega)
  have hwJ : InL 𝔭 A J w := hwv.mono (by omega)
  have hw1 : InL 𝔭 A 1 w := hwv.mono (by omega)
  set θ : K := c⁻¹ * c⁻¹ * h d z₀ with hθ_def
  have hθJ : InI 𝔭 J θ := by
    have h1 : InI 𝔭 (v + (v + J)) (h d z₀) := (InL.form hp hF hA hw hz₀L).mono (by omega)
    have h2 := InI.div h𝔭 hn hv (InI.div h𝔭 hn hv h1)
    have h3 := InI.mul hp hinv' (InI.mul hp hinv' h2)
    have h4 : θ = (1 + ε)⁻¹ * ((1 + ε)⁻¹ *
        ((κ (ι n))⁻¹ * ((κ (ι n))⁻¹ * h d z₀))) := by
      rw [hθ_def, hcinv]
      ring
    rw [h4]
    exact h3.mono (by omega)
  have hθ1 : InI 𝔭 1 θ := hθJ.mono (by omega)
  have hskew : h d z₀ + h z₀ d = 0 := by
    rw [hz₀]
    simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul,
      starRingEnd_apply, star_star]
    linear_combination hdd + h d d * hl
  have hθstar : star θ = -θ := by
    rw [hθ_def, star_mul', star_mul', star_inv₀, hcstar, hsymm]
    linear_combination c⁻¹ * c⁻¹ * hskew
  set Y : V →ₗ[K] V := WCB.skewY h z₀ w θ with hY_def
  have hY := WCB.skewY_skew hs z₀ w hθstar
  have hYz : Y z₀ = d := by
    rw [hY_def, WCB.skewY_apply]
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    have hcoef : θ * c - h w z₀ = 0 := by
      rw [hw_def, LinearMap.map_smulₛₗ₂, starRingEnd_apply, star_inv₀,
        hcstar, smul_eq_mul, hθ_def]
      linear_combination c⁻¹ * h d z₀ * hcc
    rw [hcoef, zero_smul, zero_add, hw_def, smul_smul, hcc, one_smul]
  obtain ⟨g, hg, hgz, hs1, hs2⟩ := WCB.exists_cayley han hY hl
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨z', hz'⟩ := hs1 z
    have hz'L := WCB.mem_of_resolvent h𝔭 hF hA hz₀L hw1 hθ1 hls0 hz hz'
    rw [← hz', hgz]
    have h1 : z' + l • Y z' - (z' - star l • Y z') = (l + star l) • Y z' := by
      rw [add_smul]
      abel
    rw [h1, hl, one_smul]
    exact WCB.skewY_mem hp hF hA hz₀L hwJ hθJ hz'L
  · intro z hz
    obtain ⟨z', hz'⟩ := hs2 z
    have hz'' : z' - (-l) • Y z' = z := by
      rw [neg_smul, sub_neg_eq_add]
      exact hz'
    have hz'L := WCB.mem_of_resolvent h𝔭 hF hA hz₀L hw1 hθ1 (InI.neg hl0) hz hz''
    have hgs : g.symm z = z' - star l • Y z' := by
      rw [LinearEquiv.symm_apply_eq, hgz, hz']
    rw [hgs]
    exact InL.sub hp hz'L ((InL.smul hp hls0 (WCB.skewY_mem hp hF hA hz₀L hwJ hθJ hz'L)).mono
      (by omega))
  · have hx' : z₀ - star l • Y z₀ = x := by
      rw [hYz, hz₀]
      abel
    rw [← hx', hgz, hYz, hz₀, hy, add_assoc, ← add_smul, add_comm (star l) l, hl, one_smul]

end Formalism.HermitianLattices.Ext.L3.WCC
end
end
