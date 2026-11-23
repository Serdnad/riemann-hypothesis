module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscrIdealSmulLeIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle043
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle034
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOfNormRepCountNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle015
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsTotPosDefOfSmul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocFEqLocFAdjoinCut
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle038
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdLeOneOfBasis
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle018
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle040
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoWeightedTprod
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumRegroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem extOf_one (S : VecSplit h h') : SplitBAux.extOf S 1 = 1 := by
  rw [← extHom_apply, map_one]

theorem extOf_mul (S : VecSplit h h') (a b : V' ≃ₗ[K] V') :
    SplitBAux.extOf S (a * b) = SplitBAux.extOf S a * SplitBAux.extOf S b := by
  rw [← extHom_apply, ← extHom_apply, ← extHom_apply, map_mul]

theorem gmap_extOf_inv (S : VecSplit h h') (a : V' ≃ₗ[K] V') (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a) (Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a⁻¹) M) = M := by
  rw [← autSub_gmap_mul, ← extOf_mul, mul_inv_cancel, extOf_one, autSub_gmap_one]

theorem gmap_extOf_inv' (S : VecSplit h h') (a : V' ≃ₗ[K] V') (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a⁻¹) (Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a) M) = M := by
  rw [← autSub_gmap_mul, ← extOf_mul, inv_mul_cancel, extOf_one, autSub_gmap_one]

theorem orb_equiv (S : VecSplit h h') :
    Equivalence (fun M₁ M₂ : Submodule (𝓞 K) V =>
      ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M₁ = M₂) := by
  refine ⟨fun M => ⟨1, one_mem _, by rw [extOf_one, autSub_gmap_one]⟩, ?_, ?_⟩
  · rintro M₁ M₂ ⟨g', hg', e⟩
    exact ⟨g'⁻¹, inv_mem hg', by rw [← e, gmap_extOf_inv']⟩
  · rintro M₁ M₂ M₃ ⟨g', hg', e⟩ ⟨g'', hg'', e'⟩
    exact ⟨g'' * g', mul_mem hg'' hg', by rw [extOf_mul, autSub_gmap_mul, e, e']⟩

theorem through_smul (hs : h.IsSymm) (S : VecSplit h h') {A M : Submodule (𝓞 K) V}
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h')
    (hM : (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g A = M) ∧ S.x₀ ∈ M) :
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M) ∧
      S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M := by
  obtain ⟨⟨g, hg, hgA⟩, hxM⟩ := hM
  refine ⟨⟨SplitBAux.extOf S g' * g, mul_mem (SplitBAux.extOf_mem_isom hs S hg') hg, ?_⟩, ?_⟩
  · rw [autSub_gmap_mul, hgA]
  · exact ⟨S.x₀, hxM, SplitBAux.extOf_x₀ S g'⟩

theorem tube_add (D : Subgroup (V ≃ₗ[K] V)) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) {J k : ℕ}
    (hJk : J ≤ k) (x : V) {y z : V} (hy : y ∈ tube D A 𝔭 J x)
    (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) : y + z ∈ tube D A 𝔭 J x := by
  obtain ⟨g, hg, hy'⟩ := hy
  refine ⟨g, hg, ?_⟩
  have hz' : z ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hJk) hz
  have e : y + z - g x = (y - g x) + z := by abel
  rw [e]
  exact add_mem hy' hz'

theorem autSub_apply_mem {u : V ≃ₗ[K] V} {A : Submodule (𝓞 K) V} (hu : u ∈ autSub h A) {x : V}
    (hx : x ∈ A) : u x ∈ A := by
  have h2 : Formalism.HermitianLatticesTheory.gmap u A = A := hu.2
  rw [← h2]
  exact ⟨x, hx, rfl⟩

theorem same_orbit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {g₁ g₂ : V ≃ₗ[K] V} (hg₁ : g₁ ∈ Formalism.HermitianLatticesTheory.isom h) (hg₂ : g₂ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx₁ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) (hx₂ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L))
    {J : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 L) 𝔭 + 1 ≤ J) {y : V}
    (h1 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₁.symm S.x₀))
    (h2 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₂.symm S.x₀)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) =
      Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L) := by
  have hx₁' : g₁.symm S.x₀ ∈ locF 𝔭 L := (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g₁ (locF 𝔭 L) S.x₀).1 hx₁
  have hx₂' : g₂.symm S.x₀ ∈ locF 𝔭 L := (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g₂ (locF 𝔭 L) S.x₀).1 hx₂
  obtain ⟨u₁, hu₁, hy₁⟩ := h1
  obtain ⟨u₂, hu₂, hy₂⟩ := h2
  have ha : u₁ (g₁.symm S.x₀) ∈ locF 𝔭 L := autSub_apply_mem hu₁ hx₁'
  have hb : u₂ (g₂.symm S.x₀) ∈ locF 𝔭 L := autSub_apply_mem hu₂ hx₂'
  have hna : h (u₁ (g₁.symm S.x₀)) (u₁ (g₁.symm S.x₀)) = algebraMap F K (n : F) := by
    rw [SplitBAux.isom_apply hu₁.1, SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg₁), hx]
  have hnb : h (u₂ (g₂.symm S.x₀)) (u₂ (g₂.symm S.x₀)) = algebraMap F K (n : F) := by
    rw [SplitBAux.isom_apply hu₂.1, SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg₂), hx]
  have hxy : u₂ (g₂.symm S.x₀) - u₁ (g₁.symm S.x₀) ∈
      ((extP K 𝔭) ^ J • (locF 𝔭 L) : Submodule (𝓞 K) V) := by
    have e : u₂ (g₂.symm S.x₀) - u₁ (g₁.symm S.x₀) =
        (y - u₁ (g₁.symm S.x₀)) - (y - u₂ (g₂.symm S.x₀)) := by abel
    rw [e]
    exact sub_mem hy₁ hy₂
  obtain ⟨w, hw, -, hwab⟩ := exists_isom_congr hK hF hs hd hL hLi h𝔭 hn ha hb hna hnb hJ hxy
  set G : V ≃ₗ[K] V := g₂ * u₂⁻¹ * w * u₁ * g₁⁻¹ with hGdef
  have hG : G ∈ Formalism.HermitianLatticesTheory.isom h :=
    mul_mem (mul_mem (mul_mem (mul_mem hg₂ (inv_mem hu₂.1)) hw.1) hu₁.1) (inv_mem hg₁)
  have hGx : G S.x₀ = S.x₀ := by
    change g₂ (u₂.symm (w (u₁ (g₁.symm S.x₀)))) = S.x₀
    rw [hwab, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  refine ⟨SplitBAux.res S G hG hGx, SplitBAux.res_mem_isom S G hG hGx, ?_⟩
  rw [extOf_res, ← autSub_gmap_mul]
  have e : G * g₁ = g₂ * u₂⁻¹ * w * u₁ := by
    rw [hGdef, inv_mul_cancel_right]
  rw [e, autSub_gmap_mul, hu₁.2, autSub_gmap_mul, hw.2, autSub_gmap_mul, (inv_mem hu₂).2]

theorem exists_on_orbit (hs : h.IsSymm) (S : VecSplit h h') {A : Submodule (𝓞 K) V}
    {g γ : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h')
    (e : Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (Formalism.HermitianLatticesTheory.gmap γ A) = Formalism.HermitianLatticesTheory.gmap g A) {y : V}
    (hy : g y = S.x₀) : ∃ u ∈ autSub h A, u (γ.symm S.x₀) = y := by
  refine ⟨g⁻¹ * SplitBAux.extOf S g' * γ, ?_, ?_⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.isom h ∧ _
    refine ⟨mul_mem (mul_mem (inv_mem hg) (SplitBAux.extOf_mem_isom hs S hg')) hγ, ?_⟩
    rw [autSub_gmap_mul, autSub_gmap_mul, e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · rw [mul_apply_eq_comp, mul_apply_eq_comp, LinearEquiv.apply_symm_apply, SplitBAux.extOf_x₀,
      ← hy]
    exact g.symm_apply_apply y

end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace PinD

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (n : 𝓞 F) (hn : n ≠ 0)
    (S : VecSplit (algebraMap F K (n : F) • h) (algebraMap F K (n : F) • h'))
    (hs' : (algebraMap F K (n : F) • h).IsSymm) (hd' : IsTotPosDef (algebraMap F K (n : F) • h))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : (algebraMap F K (n : F) • h) S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (n : F) • h) L₀ ∧
      repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n ≠ 0 ∧
      psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
        alphaStd K 𝔭 (finrank K V - 1) * repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero (algebraMap F K)).2 hnF
  set S₁ := unscale hc S with hS₁
  have hx1 : h S₁.x₀ S₁.x₀ = 1 := by
    have e := hx
    rw [smul_form_apply] at e
    exact mul_left_cancel₀ hc (e.trans (mul_one _).symm)
  have hs : h.IsSymm := isSymm_of_smul hF hc hs'
  have hd : IsTotPosDef h := isTotPosDef_of_smul hK hF hs hd' hx1
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 := fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  obtain ⟨L₀, hLf, hLi, hxL, hvd⟩ :=
    Cell.exists_full_lattice hK hF hs hd h𝔭 (x₀ := S₁.x₀) (n := 1) (by simpa using hx1) h1𝔭
  have hL : Submodule.IsLattice K L₀ := hLf.toIsLattice
  have hs₁' : h'.IsSymm := S₁.isSymm hs
  have hd₁' : IsTotPosDef h' := S₁.isTotPosDef hd
  have hsc' := S.isSymm hs'
  have hdc' := S.isTotPosDef hd'
  have hCf := StabilizerLattices.isFullLattice_cut S₁ hLf
  have hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h' (S₁.cut L₀) := Formalism.HermitianLattices.Ext.L3.UnimodularLocalization.isIntegralLat_cut S₁ hLi
  have hvdC : vd h' (S₁.cut L₀) 𝔭 = vd h L₀ 𝔭 := PinC.vd_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭
  have hm := S₁.finrank_add_one
  have hLic := PinA.isIntegralLat_smul hLi n
  have hCic := PinA.isIntegralLat_smul hCi n
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hb)
  have hsplit : alphaL h L₀ 𝔭 = alphaN h L₀ 𝔭 1 * alphaL h' (S₁.cut L₀) 𝔭 :=
    alphaL_split hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd
  have hαpos : 0 < alphaL h L₀ 𝔭 := alphaL_pos hK hF hs hd hLf hLi h𝔭
  have hαC : 0 < alphaL h' (S₁.cut L₀) 𝔭 := alphaL_pos hK hF hs₁' hd₁' hCf hCi h𝔭
  have hαN : alphaN h L₀ 𝔭 1 ≠ 0 := by
    intro h0
    rw [hsplit, h0, zero_mul] at hαpos
    exact lt_irrefl _ hαpos
  have hNsm : alphaN (algebraMap F K (n : F) • h) L₀ 𝔭 n =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 n * alphaN h L₀ 𝔭 1 := by
    have e := alphaN_smul hK hF hs hd hLf hLi h𝔭 hn hs' hd' (by omega) one_ne_zero
    rwa [mul_one] at e
  have hLsm := alphaL_smul hK hF hs hd hLf hLi h𝔭 hn hs' hd'
  have hvsm := PinA.vd_smul hK hF hs hd hLf hLi h𝔭 hn
  have hvT : vd (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      vd h' (S₁.cut L₀) 𝔭 + finrank K V' * vF 𝔭 n := by
    rw [vd_locF hK hF hsc' hdc' hCf.toIsLattice hCic h𝔭]
    exact PinA.vd_smul hK hF hs₁' hd₁' hCf hCi h𝔭 hn
  have hαT : alphaL (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 n * finrank K V' ^ 2) * alphaL h' (S₁.cut L₀) 𝔭 := by
    rw [← alphaL_smul hK hF hs₁' hd₁' hCf hCi h𝔭 hn hsc' hdc']
    unfold alphaL
    simp only [akCount_locF hF _ (S₁.cut L₀) 𝔭 h𝔭]
  have hrep : IsLocReps S₁ L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} :=
    PinC.isLocReps_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd
  have hrep' : IsLocReps S L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} := isLocReps_scale hF hc S hL hLi h𝔭 hrep
  have hpsi : psiP S L₀ 𝔭 = lamP (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 := by
    rw [psiP_eq_sum hK hF hs' hd' S hL hLic h𝔭 hrep', Finset.sum_singleton, fibLoc_unscale hc,
      PinC.fibLoc_cut hK hF hs hd S₁ hx1 hLf hLi hxL h𝔭 hvd]
    simp
  refine ⟨L₀, hLf, hLic, ?_, ?_⟩
  · unfold repRatio
    rw [hNsm, hLsm]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hN) (mul_ne_zero (pow_ne_zero _ hN) hαN))
      (mul_ne_zero (pow_ne_zero _ hN) hαpos.ne')
  · rw [hpsi]
    unfold lamP repRatio
    rw [hvT, hαT, hNsm, hLsm, hvsm, hsplit, hvdC, ← hm, Nat.add_sub_cancel]
    have hA := hαC.ne'
    field_simp
    ring

end PinD

theorem liPin : LIPin := by
  unfold LIPin
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S 𝔭 n hs hd h𝔭 hn hx
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero _).2 hnF
  obtain ⟨h₀, rfl⟩ : ∃ h₀ : V →ₗ⋆[K] V →ₗ[K] K, algebraMap F K (n : F) • h₀ = h :=
    ⟨(algebraMap F K (n : F))⁻¹ • h, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨h₀', rfl⟩ : ∃ h₀' : V' →ₗ⋆[K] V' →ₗ[K] K, algebraMap F K (n : F) • h₀' = h' :=
    ⟨(algebraMap F K (n : F))⁻¹ • h', by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  exact PinD.core hK hF n hn S hs hd h𝔭 hx

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace A5

open scoped Classical in
theorem coe_filter_box (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ)
    (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ bId v} =
      ↑((boxSet_finite hK hF T).toFinset.filter fun n => v ≤ valF n) := by
  ext n
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hb, hI⟩
    exact ⟨hb, (mem_bId_iff (ne_zero_of_mem_boxSet hb) v).mp hI⟩
  · rintro ⟨hb, hv⟩
    exact ⟨hb, (mem_bId_iff (ne_zero_of_mem_boxSet hb) v).mpr hv⟩

open scoped Classical in
theorem dominated (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ,
      |T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n| ≤
        C / nrm (fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℝ)) v := by
  obtain ⟨C1, hC1⟩ := prodS_bound hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm S
  refine ⟨2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1, fun T hT v => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hsum0 : 0 ≤ ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n := by
    refine Finset.sum_nonneg fun n hn => ?_
    have hb : n ∈ boxSet K F T := by
      simpa using (Finset.mem_filter.mp hn).1
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hC1 n (ne_zero_of_mem_boxSet hb)).1
  rw [abs_of_nonneg (mul_nonneg (zpow_nonneg hT0.le _) hsum0)]
  have hterm : ∀ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ≤
        (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1) * C1 := fun n hn => by
    have hb : n ∈ boxSet K F T := by
      simpa using (Finset.mem_filter.mp hn).1
    have hP := hC1 n (ne_zero_of_mem_boxSet hb)
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (absNorm_le_of_mem_boxSet hK hF hb) _) hP.2 hP.1
      (pow_nonneg (pow_nonneg hT0.le _) _)
  have hcard : (((boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n)).card : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm (bId v) : ℝ) := by
    have h1 := Formalism.HermitianLattices.Ext.L3.BoxCube.card_box_le hK hF (bId_ne_bot v) hT0.le
    have h2 : ((boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n)).card =
        Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ bId v} := by
      rw [← Set.ncard_coe_finset, ← coe_filter_box hK hF T v, ← Nat.card_coe_set_eq]
      rfl
    rw [h2]
    exact h1
  have hle := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hle
  have hexp : Formalism.HermitianLatticesTheory.fDeg K * finrank K V =
      Formalism.HermitianLatticesTheory.fDeg K + Formalism.HermitianLatticesTheory.fDeg K * (finrank K V - 1) := by
    conv_lhs => rw [show finrank K V = (finrank K V - 1) + 1 by omega]
    ring
  have hTT : T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
      (T ^ Formalism.HermitianLatticesTheory.fDeg K * (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1)) = 1 := by
    rw [zpow_neg, zpow_natCast, ← pow_mul, ← pow_add, ← hexp]
    exact inv_mul_cancel₀ (pow_ne_zero _ hT0.ne')
  have hC1n : 0 ≤ C1 := by
    have := hC1 1 one_ne_zero
    exact this.1.trans this.2
  rw [← absNorm_bId]
  calc T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n
      ≤ T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ((2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm (bId v) : ℝ)) *
          ((T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1) * C1)) := by
        refine mul_le_mul_of_nonneg_left (hle.trans ?_) (zpow_nonneg hT0.le _)
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (pow_nonneg (pow_nonneg hT0.le _) _) hC1n)
    _ = (2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1 / (Ideal.absNorm (bId v) : ℝ)) *
        (T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
          (T ^ Formalism.HermitianLatticesTheory.fDeg K * (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1))) := by ring
    _ = 2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1 / (Ideal.absNorm (bId v) : ℝ) := by rw [hTT, mul_one]

end A5

open A5 in
theorem tendsto_singS_sum (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * singS F h L n)
      atTop (𝓝 ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V))) := by
  classical
  set S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    (finite_vd_ne_zero (F := F) hK hF hs hd hL hLi).toFinset with hSdef
  have hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S := fun 𝔭 h𝔭 =>
    (Set.Finite.mem_toFinset _).mpr h𝔭
  obtain ⟨C, hC⟩ := dominated hK hF hs hd hL hLi hm S
  set c0 : ℝ := (finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
    Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) with hc0
  have main := tendsto_weighted_tprod
    (q := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ))
    (fun 𝔭 => by exact_mod_cast two_le_absNorm 𝔭.2) summable_inv_absNorm_sq S
    (ρ := roL h L S) (roL_zero hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm hS) (fun 𝔭 h𝔭 j => by simp [roL, h𝔭])
    (roL_diff hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm hS) valF
    (fun j : ℕ => (boxSet_finite hK hF ((j : ℝ) ^ 2)).toFinset)
    (fun n => (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n)
    (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)))
    (c0 * ∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹) c0 C
    (fun 𝔭 => (eFac K (finrank K V) 𝔭.1)⁻¹) (fun h0 => by rw [h0, zero_mul]) ?_ ?_ ?_
  · refine main.congr fun j => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (boxSet_finite hK hF ((j : ℝ) ^ 2))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb : n ∈ boxSet K F ((j : ℝ) ^ 2) := (Set.Finite.mem_toFinset _).mp hn
    rw [singS_eq hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm hS (ne_zero_of_mem_boxSet hb), mul_assoc]
  · intro v hv
    have ht := tendsto_sum_box_ideal hK hF hs hd hL hLi hm S hS (bId_ne_bot v)
      (fun 𝔭 h𝔭 => bId_sup_eq_top (Finset.disjoint_right.mp hv h𝔭))
    simp_rw [coe_filter_box hK hF, finsum_mem_coe_finset] at ht
    rw [absNorm_bId] at ht
    have he : c0 * (∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹) /
        nrm (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ)) v =
        c0 / nrm (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ)) v *
          ∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹ := by ring
    rw [he]
    exact ht
  · filter_upwards [eventually_ge_atTop 1] with j hj v
    refine hC _ ?_ v
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith
  · intro S' hS'
    have ht := tendsto_sum_box_ideal hK hF hs hd hL hLi hm S' (fun 𝔭 h𝔭 => hS' (hS 𝔭 h𝔭))
      (b := ⊤) (by simp) (fun 𝔭 _ => by simp)
    simp only [Submodule.mem_top, and_true, Ideal.absNorm_top, Nat.cast_one, div_one] at ht
    refine ht.congr fun j => ?_
    have hset : {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2)} = boxSet K F ((j : ℝ) ^ 2) := rfl
    rw [hset, finsum_mem_eq_finite_toFinset_sum _ (boxSet_finite hK hF ((j : ℝ) ^ 2))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb : n ∈ boxSet K F ((j : ℝ) ^ 2) := (Set.Finite.mem_toFinset _).mp hn
    rw [mul_assoc, ← prod_aLoc hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hS hS' (ne_zero_of_mem_boxSet hb)]
    rfl

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem repMass_eq_prod_psi (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) = c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 :=
  MassProductFormula.repMass_eq_prod_psi' hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi hc

end Formalism.HermitianLattices.Ext.L3
end
end
