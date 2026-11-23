module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtHomInjective
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle015
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle023
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle029
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountEqSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle038
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle042
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle009
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle018
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle026
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle033
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle044
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
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
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle039

@[expose] public section

section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem nu_gmap_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    nu h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = nu h L 𝔭 ∧
      vd h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = vd h L 𝔭 := by
  have hv : vd h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = vd h L 𝔭 := by
    rw [UnimodularLocalization.vd_gmap hg, vd_locF hK hF hs hd hL hLi h𝔭]
  have ha : alphaL h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = alphaL h L 𝔭 := by
    rw [BrB.alphaL_gmap hg]
    unfold alphaL
    simp only [akCount_locF hF h L 𝔭 h𝔭]
  refine ⟨?_, hv⟩
  unfold nu
  rw [ha, hv]

theorem main_term (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M₂ : Submodule (𝓞 K) V} (hM₂ : Submodule.IsFullLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hx₂ : S.x₀ ∈ locF 𝔭 M₂)
    {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      (nkCount h L 𝔭 k n : ℝ) = kap S (locF 𝔭 M₂) 𝔭 n J k *
        ((Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * nu h L 𝔭) *
        ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * (nu h' T 𝔭)⁻¹ := by
  have hL_gmap (g : V ≃ₗ[K] V) :
      Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
    refine { toIsLattice := Submodule.IsLattice.of_fg K (hL.fg.map _), span_eq_top := ?_ }
    change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  obtain ⟨R, hR⟩ := exists_mReps hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hn hx hsr
  have h1 := nkCount_eq_sum hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hn hx hR
  have h2 : ∀ M ∈ R, ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      kap S M 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
    intro M hM
    obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
    rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
    exact kap_eq hK hF hs hd S (by first | exact hL_gmap g | exact (hL_gmap g).toIsLattice) (UnimodularLocalization.isIntegralLat_gmap hg hLi) (by first | exact hM₂ | exact hM₂.toIsLattice) hM₂i
      h𝔭 hn hx hxM hx₂
  have h3 : ∀ᶠ J in atTop, ∀ᶠ k in atTop, ∀ M ∈ R,
      kap S M 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
    filter_upwards [(Finset.eventually_all R).mpr h2] with J hJ
    exact (Finset.eventually_all R).mpr hJ
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  filter_upwards [h1, h3] with J hJ1 hJ3
  filter_upwards [hJ1, hJ3] with k hk1 hk3
  rw [hk1, ← sum_oM hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hsr hR (fun T => (nu h' T 𝔭)⁻¹), Nat.cast_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [← hk3 M hM]
  obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
  obtain ⟨e1, e2⟩ := nu_gmap_locF hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hg
  have hν : 0 < nu h L 𝔭 := by
    rw [← e1, LocalizedFibreSets.gmap_locF]
    exact nu_pos hK hF hs hd (by first | exact hL_gmap g | exact (hL_gmap g).toIsLattice) (UnimodularLocalization.isIntegralLat_gmap hg hLi) h𝔭
  have hν' : 0 < nu h' (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) 𝔭 := by
    rw [LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]
    exact nu_pos hK hF (S.isSymm hs) (S.isTotPosDef hd)
      (by
        have hcut := StabilizerLattices.isFullLattice_cut S (hL_gmap g)
        first | exact hcut | exact hcut.toIsLattice)
      (UnimodularLocalization.isIntegralLat_cut S (UnimodularLocalization.isIntegralLat_gmap hg hLi)) h𝔭
  have ho : (oM S (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) : ℝ) ≠ 0 := by
    rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
    exact_mod_cast oM_ne_zero hs S (by first | exact hL_gmap g | exact (hL_gmap g).toIsLattice) h𝔭 hxM
  unfold kap
  rw [e1, e2]
  have hq' := pow_pos hq (vd h L 𝔭)
  field_simp

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

section

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

namespace Step

theorem final_algebra (μ c lam D P a mm vv sq lV : ℝ) (f : ℕ) (hD : 0 < D) (hP : 0 < P)
    (ha : 0 < a) (hmm : 0 < mm) (hvv : 0 < vv) (hsq : 0 < sq)
    (h : μ * ((P / (mm * a)) ^ f / (vv * D)) = 0 + c * lam * D⁻¹ * ((mm ^ f)⁻¹ / sq * lV)) :
    μ = c * ((a / P) ^ f * vv / sq * lV) * lam := by
  have hD' := hD.ne'
  have hP' := hP.ne'
  have ha' := ha.ne'
  have hmm' := hmm.ne'
  have hvv' := hvv.ne'
  have hsq' := hsq.ne'
  have hX : (P / (mm * a)) ^ f / (vv * D) ≠ 0 := by positivity
  rw [zero_add] at h
  rw [eq_div_of_mul_eq hX h, div_pow, mul_pow, div_pow]
  field_simp

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem normD_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : 0 < normD h L := by
  have hd' : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hne φ
    simp [hx] at this
  have hne := LocF.discrIdeal_ne_bot hd' hL hLi
  unfold normD
  apply Real.sqrt_pos.mpr
  have : Ideal.absNorm (discrIdeal h L) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hne
  exact_mod_cast Nat.pos_of_ne_zero this

theorem tendsto_left (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Tendsto (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (Formalism.HermitianLatticesTheory.mass h L *
        ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
          (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L)))) := by
  rw [RankOne.mass_eq_sum h L s hsr, Finset.sum_mul]
  simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ fun M hM => ?_
  have hg := hsr.1 M hM
  obtain ⟨hMi, -, hMD⟩ := integral_of_mem_genus hK hF hs hd hL hLi hg
  have ht := (tendsto_ballCount hK hF hs hd hg.1 hMi).const_mul
    ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)⁻¹)
  rw [hMD] at ht
  refine ht.congr fun j => ?_
  rw [div_eq_mul_inv (ballCount h M ((j : ℝ) ^ 2) : ℝ), div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem tendsto_right (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) :
    Tendsto (fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (0 + c * lamG F h L * (normD h L)⁻¹ *
        ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V)))) := by
  have hf : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have hexp : 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V ≠ 0 := by positivity
  have h1 : Tendsto (fun j : ℕ => Formalism.HermitianLatticesTheory.mass h L /
      (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hexp).comp tendsto_natCast_atTop_atTop)
  have h2 := (tendsto_singS_sum hK hF hs hd hL hLi hm).const_mul
    (c * lamG F h L * (normD h L)⁻¹)
  refine (h1.add h2).congr fun j => ?_
  rw [add_div]
  congr 1
  rw [finsum_mem_congr rfl fun n hn => repMass_eq hH hLI hK hF hs hd hL hLi hm hc hn,
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    ← Finset.mul_sum, zpow_neg, zpow_natCast, ← pow_mul, ← mul_assoc 2, div_eq_mul_inv]
  ring

end Step

theorem massConst_succ (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c) (hc : MassConst K F (m - 1) c) :
    MassConst K F m (c * Formalism.HermitianLatticesTheory.massRatioRightSide K m) := by
  unfold MassConst
  intro V _ _ _ _ _ h L hs hd hfin hL hLi
  subst hfin
  obtain ⟨s, hsr⟩ := StabilizerLattices.exists_classReps hs hd hL.toIsLattice
  have hlim := Step.tendsto_left hK hF hs hd hL hLi hsr
  have hlim2 := Step.tendsto_right hH hLI hK hF hs hd hL hLi hm hc
  have hfun : (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) =
      fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    funext j
    rw [sum_ballCount_eq hK hF hs hd hL.toIsLattice hLi hsr (by positivity)]
  rw [hfun] at hlim
  have hAB := tendsto_nhds_unique hlim hlim2
  have hn0 : 0 < finrank K V := by omega
  have hfact : ((finrank K V).factorial : ℝ) =
      (finrank K V : ℝ) * ((finrank K V - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred hn0.ne']
    push_cast
    ring
  rw [hfact, zpow_neg, zpow_natCast] at hAB
  have hv := vInv_pos K
  have key := Step.final_algebra (Formalism.HermitianLatticesTheory.mass h L) c (lamG F h L) (normD h L)
    (Real.pi ^ finrank K V) ((finrank K V - 1).factorial : ℝ) (finrank K V : ℝ)
    (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
    (Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K)) (lValEtaF K F (finrank K V))
    (Formalism.HermitianLatticesTheory.fDeg K) (Step.normD_pos hd hL hLi) (by positivity) (by positivity)
    (by exact_mod_cast hn0) (by positivity) (by positivity) hAB
  rw [massRatio_eq_lvalue hK hF (finrank K V) hm]
  exact key

end Formalism.HermitianLattices.Ext.L3
end
end
