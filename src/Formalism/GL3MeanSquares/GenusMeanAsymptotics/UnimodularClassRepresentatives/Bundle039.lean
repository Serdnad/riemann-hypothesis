module

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle029
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle038
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle035
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle024
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem boxSet_finite (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  apply Formalism.HermitianLattices.Ext.L3.BoxSum.finite_boxSet <;> assumption

theorem ne_zero_of_mem_boxSet {T : ℝ} {n : 𝓞 F} (hn : n ∈ boxSet K F T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  have := (hn φ).1
  simp at this

theorem absNorm_le_of_mem_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  by_contra hlt
  have := box_inter_eq_empty hK hF (b := Ideal.span {n}) (not_le.mp hlt)
  have hmem : n ∈ {n' : 𝓞 F | n' ∈ boxSet K F T ∧ n' ∈ Ideal.span {n}} :=
    ⟨hn, Ideal.mem_span_singleton_self n⟩
  rw [this] at hmem
  exact hmem

def eFac (K : Type) {F : Type} [Field K] [Field F] [NumberField F] [Algebra F K] (m : ℕ)
    (𝔭 : Ideal (𝓞 F)) : ℝ :=
  1 - etaF K F 𝔭 ^ m * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ))

theorem eFac_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : 1 ≤ m) : 0 < eFac K m 𝔭 := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by exact_mod_cast two_le_absNorm h𝔭
  have h1 := IdealNormInequalities.zpow_neg_lt_one hq hm
  have h0 : 0 ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) := zpow_nonneg (by linarith) _
  have hη : |etaF K F 𝔭 ^ m| = 1 := by
    rw [abs_pow]
    unfold etaF
    split_ifs <;> simp
  have h2 : etaF K F 𝔭 ^ m * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) ≤
      (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) := by
    calc _ ≤ |etaF K F 𝔭 ^ m| * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ = _ := by rw [hη, one_mul]
  unfold eFac
  linarith

theorem alphaN_eq_stage (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    ∃ k : ℕ, alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  set k0 := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2
  refine ⟨k0, ?_⟩
  refine Tendsto.limUnder_eq (tendsto_atTop_of_eventually_const (i₀ := k0) fun k hk => ?_)
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih, nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk]
    generalize 2 * finrank K V - 1 = r
    rw [add_mul, one_mul, pow_add]
    push_cast
    field_simp

theorem alphaN_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 → 0 ≤ alphaN h L 𝔭 n ∧ alphaN h L 𝔭 n ≤ C := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := alphaN_eq_stage hK hF hs hd hL hLi h𝔭 hn
  rw [hk]
  exact ⟨by positivity, (div_le_iff₀ (by positivity)).mpr (hC k n)⟩

end Formalism.HermitianLattices.Ext.L3.A5
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

theorem relIndex_eq_card_image {G α : Type*} [Group G] (H S : Subgroup G) (f : G → α)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ a⁻¹ * b ∈ H) :
    H.relIndex S = Nat.card {c : α // ∃ a ∈ S, f a = c} := by
  classical
  show Nat.card (S ⧸ H.subgroupOf S) = _
  apply Nat.card_congr
  refine Equiv.ofBijective (fun q => Quotient.liftOn' q
    (fun a : S => (⟨f a, a, a.2, rfl⟩ : {c : α // ∃ a ∈ S, f a = c})) ?_) ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    show f a = f b
    have hab' : a⁻¹ * b ∈ H.subgroupOf S := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab'
    exact (hf a a.2 b b.2).mpr hab'
  · intro q₁ q₂ e
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    have e' : f a = f b := congrArg Subtype.val e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hf a a.2 b b.2).mp e'
  · rintro ⟨c, a, ha, rfl⟩
    exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (a b : V ≃ₗ[K] V) (B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap a B = Formalism.HermitianLatticesTheory.gmap b B ↔ a⁻¹ * b ∈ glSub B := by
  rw [mem_glSub]
  constructor
  · intro e
    rw [autSub_gmap_mul, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro e
    rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm, autSub_gmap_mul a, e]

theorem autSub_le_sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    autSub h A ≤ sSub h A 𝔭 k := fun X hX => ⟨hX.2, fun x _ y _ => by
  rw [hX.1 x y, sub_self]
  exact Submodule.zero_mem _⟩

theorem coe_mem_of_mem_smul_top (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) {u : ↥A}
    (hu : u ∈ (I • ⊤ : Submodule (𝓞 K) ↥A)) : (u : V) ∈ I • A := by
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) hu
  rwa [Submodule.map_smul'', Submodule.map_subtype_top] at h2

theorem exists_autSub_mul_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k) {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), g⁻¹ * X ∈ nSub (locF 𝔭 A₀) 𝔭 (k - eA h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨hXg, hXh⟩ := hX
  set A := locF 𝔭 A₀ with hA
  let f : ↥A →ₗ[𝓞 K] ↥A :=
    (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).domRestrict A).codRestrict A
      (fun x => apply_mem hXg x.2)
  have hf : ∀ x : ↥A, ((f x : ↥A) : V) = X x := fun x => rfl
  let Xb : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
    Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)
  have key : ∀ x x' : ↥A, Submodule.Quotient.mk x' = Xb (Submodule.Quotient.mk x) →
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
    intro x x' hx
    have h1 : x' - f x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
      rw [← Submodule.Quotient.eq]
      exact hx
    exact coe_mem_of_mem_smul_top _ _ h1
  have h0 : ∀ {z : V}, z ∈ A → z ∈ extP K 𝔭 ^ 0 • A := fun hz => by rwa [pow_zero_smul]
  let := hA₀
  obtain ⟨g, hg, hgX⟩ := exists_isom_lift hK hF hs hd (A₀ := A₀) inferInstance hA₀i h𝔭 hk Xb (by
    intro x y x' y' hx hy
    rw [congrP_algebraMap_iff_sub_mem h𝔭]
    have hu := key x x' hx
    have hv := key y y' hy
    have e1 : h (x' : V) (y' : V) - h (x : V) (y : V) =
        (h (X x) (X y) - h (x : V) (y : V)) + h ((x' : V) - X x) (y' : V)
          + h (X x) ((y' : V) - X y) := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [e1]
    refine add_mem (add_mem (hXh x x.2 y y.2) ?_) ?_
    · simpa using form_mem_pK hF hA₀i h𝔭 hu (h0 y'.2)
    · simpa using form_mem_pK hF hA₀i h𝔭 (h0 (apply_mem hXg x.2)) hv)
  refine ⟨g, hg, mul_mem (inv_mem hg.2) hXg, fun x hx => ?_⟩
  have h1 := hgX ⟨x, hx⟩ (f ⟨x, hx⟩) rfl
  have h2 := apply_mem_smul (inv_mem (show g ∈ glSub A from hg.2)) _ ((Submodule.neg_mem _ h1))
  have e : ∀ z : V, g⁻¹ (g z) = z := fun z => by
    rw [← mul_apply_eq_comp, inv_mul_cancel]
    rfl
  simpa [e, hf] using h2

theorem relIndex_inf_glSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) =
      orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  let := hA₀
  let := hB₀
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub (A₀ := A₀) (B₀ := B₀) inferInstance inferInstance h𝔭
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1 + k₁, fun k hk => ?_⟩
  rw [Subgroup.inf_relIndex_left,
    relIndex_eq_card_image _ _ (fun X => Formalism.HermitianLatticesTheory.gmap X (locF 𝔭 B₀))
      (fun a _ b _ => gmap_eq_iff a b _)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ⟨?_, ?_⟩)
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨g, hg, hY⟩ := exists_autSub_mul_nSub hK hF hs hd hA₀ hA₀i h𝔭 (by omega) hX
    exact ⟨g, hg.1, hg.2, (gmap_eq_iff g X _).2 (hk₁ _ (by omega) hY)⟩
  · rintro ⟨g, hg, hgA, rfl⟩
    exact ⟨g, autSub_le_sSub h _ 𝔭 k ⟨hg, hgA⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinF

open idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

omit [FiniteDimensional K V] in
theorem exists_norm_int (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {y : V} (hy : y ∈ L) :
    ∃ a : 𝓞 F, h y y = algebraMap (𝓞 K) K (ι a) := by
  obtain ⟨z, hz⟩ := (Submodule.mem_one).1 (hLi y hy y hy)
  have hzc : conjO K z = z := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [WA.algebraMap_conjO, hz, Cell.form_self_star hs y]
  obtain ⟨a, ha⟩ := (conjO_eq_iff_mem_range hF z).1 hzc
  exact ⟨a, by rw [ha, hz]⟩

theorem newton (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {N : ℕ} (hN : 1 ≤ N) {y : V}
    (hy : y ∈ L) {a : 𝓞 F} (ha : h y y = algebraMap (𝓞 K) K (ι a)) (ha1 : a - 1 ∈ 𝔭 ^ N) :
    ∃ y' ∈ L, ∃ a' : 𝓞 F, h y' y' = algebraMap (𝓞 K) K (ι a') ∧ a' - 1 ∈ 𝔭 ^ (N + 1) ∧
      y' - y ∈ (extP K 𝔭 ^ N • L : Submodule (𝓞 K) V) := by
  obtain ⟨c, hc⟩ := traceDeterminantCongruences.exists_trace_one hK hF h𝔭 1
  have hc' : c + conjO K c - 1 ∈ extP K 𝔭 ^ 1 := hc
  rw [pow_one] at hc'
  have hEm : ι (a - 1) ∈ extP K 𝔭 ^ N := localizedQuotients.ι_mem_pow ha1
  have hEc : conjO K (ι (a - 1)) = ι (a - 1) := idealPowerSpanBounds.conjO_map hF (a - 1)
  obtain ⟨ν, hν⟩ : ∃ ν : 𝓞 F, ι ν = conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c) := by
    have : conjO K (conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c)) =
        conjO K (1 - ι (a - 1) * c) * (1 - ι (a - 1) * c) := by
      rw [map_mul, WA.conjO_conjO, mul_comm]
    exact (conjO_eq_iff_mem_range hF _).1 this
  have ha' : ι a = 1 + ι (a - 1) := by rw [map_sub, map_one]; ring
  refine ⟨(1 - ι (a - 1) * c) • y, L.smul_mem _ hy, ν * a, ?_, ?_, ?_⟩
  · rw [← algebraMap_smul K (1 - ι (a - 1) * c) y]
    simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, starRingEnd_apply]
    rw [ha, map_mul, hν, map_mul, map_mul, WA.algebraMap_conjO]
    ring
  · rw [← idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 (N + 1) (ν * a - 1)]
    have key : ι (ν * a - 1) = ι (a - 1) * (-(c + conjO K c - 1)) +
        ι (a - 1) * ι (a - 1) * (conjO K c * c - (c + conjO K c) + ι (a - 1) * conjO K c * c) := by
      rw [map_sub (algebraMap (𝓞 F) (𝓞 K)) (ν * a) 1, map_mul, hν, ha', map_one, map_sub, map_one,
        map_mul, hEc]
      ring
    rw [key]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ]
      exact Ideal.mul_mem_mul hEm ((Ideal.neg_mem_iff _).2 hc')
    · refine Ideal.mul_mem_right _ _ ?_
      refine Ideal.pow_le_pow_right (by omega : N + 1 ≤ N + N) ?_
      rw [pow_add]
      exact Ideal.mul_mem_mul hEm hEm
  · have : (1 - ι (a - 1) * c) • y - y = (-(ι (a - 1) * c)) • y := by
      rw [sub_smul, one_smul, neg_smul]; abel
    rw [this]
    exact Submodule.smul_mem_smul ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ hEm)) hy

theorem newton_iter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) {y : V}
    (hy : y ∈ L) {a : 𝓞 F} (ha : h y y = algebraMap (𝓞 K) K (ι a)) (ha1 : a - 1 ∈ 𝔭 ^ k) (j : ℕ) :
    ∃ y' ∈ L, ∃ a' : 𝓞 F, h y' y' = algebraMap (𝓞 K) K (ι a') ∧ a' - 1 ∈ 𝔭 ^ (k + j) ∧
      y' - y ∈ (extP K 𝔭 ^ k • L : Submodule (𝓞 K) V) := by
  induction j with
  | zero => exact ⟨y, hy, a, ha, by simpa using ha1, by simp⟩
  | succ j ih =>
    obtain ⟨y1, hy1, a1, hh1, h1, hd1⟩ := ih
    obtain ⟨y2, hy2, a2, hh2, h2, hd2⟩ := newton hK hF h𝔭 (by omega : 1 ≤ k + j) hy1 hh1 h1
    refine ⟨y2, hy2, a2, hh2, by simpa only [add_assoc] using h2, ?_⟩
    have : y2 - y = (y2 - y1) + (y1 - y) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hd2) hd1

theorem exists_exact_lift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} (h1 : h x₀ x₀ = 1) {k : ℕ} (hk : 1 ≤ k) {y : V} (hy : y ∈ L)
    (hyy : CongrP 𝔭 k (h y y) 1) :
    ∃ z ∈ locF 𝔭 L, h z z = 1 ∧ z - y ∈ (extP K 𝔭 ^ k • locF 𝔭 L : Submodule (𝓞 K) V) := by
  have hcongr (j : ℕ) (b : 𝓞 F) :
      CongrP 𝔭 j (algebraMap (𝓞 K) K (ι b)) 1 ↔ b - 1 ∈ 𝔭 ^ j := by
    have h := integralBasisSpans.congrP_int h𝔭 j (ι b) (ι 1)
    rw [Ideal.Quotient.eq, ← map_sub, idealPowerSpanBounds.mem_pow_iff] at h
    simpa only [map_one] using h
  obtain ⟨a, ha⟩ := exists_norm_int hF hs hLi hy
  rw [ha] at hyy
  have ha1 := (hcongr k a).1 hyy
  have hOne : algebraMap F K ((1 : 𝓞 F) : F) = 1 := by simp
  obtain ⟨c, hc⟩ := exists_exact_near hK hF hs hd hL hLi h𝔭 (n := 1) one_ne_zero
    ⟨x₀, h1.trans hOne.symm⟩
  obtain ⟨y', hy', a', ha', ha1', hd'⟩ := newton_iter hK hF h𝔭 hk hy ha ha1 c
  obtain ⟨z, hz0, hz1, hzd⟩ := hc (k + c) (Nat.le_add_left c k) y'
    (localizedQuotients.le_locF 𝔭 L hy') (by rw [ha', hOne]; exact (hcongr _ _).2 ha1')
  rw [Nat.add_sub_cancel] at hzd
  refine ⟨z, hz0, hz1.trans hOne, ?_⟩
  have : z - y = (z - y') + (y' - y) := by abel
  rw [this]
  exact Submodule.add_mem _ hzd
    (Submodule.smul_mono le_rfl (localizedQuotients.le_locF 𝔭 L) hd')

end Formalism.HermitianLattices.Ext.L3.PinF
end
end
