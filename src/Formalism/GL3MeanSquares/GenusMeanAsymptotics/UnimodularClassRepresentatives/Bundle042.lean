module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralLatOfForall
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle037
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldBis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldFurther
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldMore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrB

section One

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem akCount_congr {A B : Submodule (𝓞 K) V} (e : ↥A ≃ₗ[𝓞 K] ↥B)
    (he : ∀ x y : ↥A, h (e x : V) (e y : V) = h (x : V) (y : V)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    akCount h B 𝔭 k = akCount h A 𝔭 k := by
  have hmap : ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A).map (e : ↥A →ₗ[𝓞 K] ↥B) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let ε := Submodule.Quotient.equiv _ _ e hmap
  have hε : ∀ x : ↥A, ε (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := fun x => rfl
  unfold akCount
  refine (Nat.card_congr (Equiv.subtypeEquiv ε.conj.toEquiv ?_)).symm
  intro X
  have hX : ∀ x : ↥A, (ε.conj X) (Submodule.Quotient.mk (e x)) = ε (X (Submodule.Quotient.mk x)) := by
    intro x
    rw [LinearEquiv.conj_apply_apply, ← hε, LinearEquiv.symm_apply_apply]
  constructor
  · intro H x y x' y' h1 h2
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective x'
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [he, he]
    refine H x y x' y' ?_ ?_
    · apply ε.injective
      rw [hε, ← hX]
      exact h1
    · apply ε.injective
      rw [hε, ← hX]
      exact h2
  · intro H x y x' y' h1 h2
    rw [← he, ← he x y]
    refine H (e x) (e y) (e x') (e y') ?_ ?_
    · change _ = (ε.conj X) _
      rw [hX, ← h1, hε]
    · change _ = (ε.conj X) _
      rw [hX, ← h2, hε]

theorem akCount_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) : akCount h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 k = akCount h T 𝔭 k :=
  akCount_congr (A := T) (B := Formalism.HermitianLatticesTheory.gmap g T) ((g.restrictScalars (𝓞 K)).submoduleMap T)
    (fun x y => hg (x : V) (y : V)) 𝔭 k

theorem alphaL_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : alphaL h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = alphaL h T 𝔭 := by
  unfold alphaL
  simp only [akCount_gmap hg]

end One

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem localFactor_map' {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : lamP h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = lamP h T 𝔭 := by
  unfold lamP
  rw [UnimodularLocalization.vd_gmap hg, alphaL_gmap hg]

theorem sum_locReps_eq (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s s' : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s)
    (hsr' : IsLocReps S L 𝔭 s') :
    ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 = ∑ T ∈ s', (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  have ex : ∀ T ∈ s, ∃! T₀, T₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = T :=
    fun T hT => hsr'.2 T (hsr.1 T hT).1 (hsr.1 T hT).2.1 (hsr.1 T hT).2.2
  refine Finset.sum_bij (fun T hT => (ex T hT).choose) ?_ ?_ ?_ ?_
  · exact fun T hT => (ex T hT).choose_spec.1.1
  · intro T₁ h1 T₂ h2 e
    obtain ⟨g₁, hg₁, e₁⟩ := (ex T₁ h1).choose_spec.1.2
    obtain ⟨g₂, hg₂, e₂⟩ := (ex T₂ h2).choose_spec.1.2
    simp only at e
    rw [← e] at e₂
    have hu := hsr.2 T₂ (hsr.1 T₂ h2).1 (hsr.1 T₂ h2).2.1 (hsr.1 T₂ h2).2.2
    refine hu.unique ⟨h1, g₂ * g₁⁻¹, Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁), ?_⟩
      ⟨h2, 1, Subgroup.one_mem _, autSub_gmap_one _⟩
    rw [← e₁, ← autSub_gmap_mul, mul_assoc, inv_mul_cancel, mul_one, e₂]
  · intro T₀ h0
    obtain ⟨T, ⟨hT, g, hg, e⟩, -⟩ :=
      hsr.2 T₀ (hsr'.1 T₀ h0).1 (hsr'.1 T₀ h0).2.1 (hsr'.1 T₀ h0).2.2
    refine ⟨T, hT, ?_⟩
    refine (ex T hT).unique (ex T hT).choose_spec.1 ⟨h0, g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    rw [← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro T hT
    obtain ⟨g, hg, e⟩ := (ex T hT).choose_spec.1.2
    conv_lhs => rw [← e, GoodGenusOrbits.fibLoc_gmap hs S L 𝔭 hg, localFactor_map' hg]

theorem psiP_eq_sum' (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  have hex : ∃ s, IsLocReps S L 𝔭 s := ⟨s, hsr⟩
  unfold psiP
  rw [dite_eq_left hex]
  exact sum_locReps_eq hs S L 𝔭 hex.choose_spec hsr

end Formalism.HermitianLattices.Ext.L3.BrB
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace unitaryAbsoluteValueBounds

theorem abs_eta_pow (𝔭 : Ideal (𝓞 F)) (M : ℕ) : |etaF K F 𝔭 ^ M| = 1 := by
  have hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
    unfold etaF
    split_ifs <;> simp
  rcases hη with h | h <;> rw [h] <;> simp

theorem abs_x_eq (𝔭 : Ideal (𝓞 F)) (m : ℕ) :
    |etaF K F 𝔭 ^ m * ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹| = ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹ := by
  rw [abs_mul, abs_eta_pow, one_mul, abs_of_nonneg (by positivity)]

theorem alphaN_rank_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hm : finrank K V = 0) {n : 𝓞 F} (hn : n ≠ 0) : alphaN h L 𝔭 n = 0 := by
  have hsub : Subsingleton V := finrank_zero_iff.1 hm
  have hLfull : Submodule.IsFullLattice K L :=
    { toIsLattice := hL, span_eq_top := Subsingleton.elim _ _ }
  rw [firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hLfull hLi h𝔭
    (localValuationFiltration.notMem_pow_vF h𝔭 hn)
    (k := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) (by omega)]
  have h0 : nkCount h L 𝔭 (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) n = 0 := by
    unfold nkCount
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨x, y, -, hc⟩
    have hy : h (y : V) (y : V) = algebraMap F K ((0 : 𝓞 F) : F) := by
      rw [Subsingleton.elim (y : V) 0]
      simp
    rw [hy, MeanB.congrP_algebraMap_iff_sub_mem h𝔭, zero_sub, neg_mem_iff, mem_pow_iff_le_vF h𝔭 hn] at hc
    omega
  rw [h0]
  simp

end unitaryAbsoluteValueBounds

theorem alphaN_of_vd_zero_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    alphaN h L 𝔭 n = (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) :=
  unitaryAbsoluteValueBounds.alphaN_unit hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv hm hn

theorem alphaN_eq_of_vF_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0) (hvv : vF 𝔭 n = vF 𝔭 n') :
    alphaN h L 𝔭 n = alphaN h L 𝔭 n' := by
  rcases Nat.eq_zero_or_pos (finrank K V) with hm | hm
  · rw [unitaryAbsoluteValueBounds.alphaN_rank_zero hK hF hs hd hL.toIsLattice hLi h𝔭 hm hn,
      unitaryAbsoluteValueBounds.alphaN_rank_zero hK hF hs hd hL.toIsLattice hLi h𝔭 hm hn']
  · rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv hm _ n hn rfl, unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv hm _ n' hn' rfl, hvv]

theorem alphaN_rho_diff_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hvv : vF 𝔭 n = vF 𝔭 n' + 1) :
    |alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) - alphaN h L 𝔭 n' / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)))| ≤
      8 * ((vF 𝔭 n : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭 : ℝ) ^ (-(((finrank K V - 1) * ((vF 𝔭 n + 1) / 2) : ℕ) : ℤ)) := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := unitaryAbsoluteValueBounds.one_lt_q h𝔭
  rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv (by omega) _ n hn rfl,
    unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv (by omega) _ n' hn' rfl,
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne',
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne', hvv,
    Finset.sum_range_succ _ (vF 𝔭 n' + 1), add_sub_cancel_left, abs_pow, unitaryAbsoluteValueBounds.abs_x_eq, zpow_neg,
    zpow_natCast, inv_pow, ← pow_mul]
  have h1 : ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * (vF 𝔭 n' + 1)))⁻¹ ≤
      ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le (Nat.mul_le_mul_left _ (by omega)))
  have h2 : (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ := by
    positivity
  have h3 : (1 : ℝ) ≤ 8 * (((vF 𝔭 n' + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ ((vF 𝔭 n' + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc _ ≤ _ := h1
    _ = 1 * _ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 h2

end Formalism.HermitianLattices.Ext.L3
end
end
