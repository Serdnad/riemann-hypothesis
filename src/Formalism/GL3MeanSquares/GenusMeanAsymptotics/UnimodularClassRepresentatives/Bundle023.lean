module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle015
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle018
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle021
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
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

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def fibG (S : VecSplit h h') (L : Submodule (𝓞 K) V) (Λ' : Submodule (𝓞 K) V') :
    Set (Submodule (𝓞 K) V) :=
  {Λ | Λ ∈ Formalism.HermitianLatticesTheory.genus h L ∧ S.x₀ ∈ Λ ∧ S.cut Λ = Λ'}

def IsFibReps (S : VecSplit h h') (L : Submodule (𝓞 K) V) (s' : Finset (Submodule (𝓞 K) V')) :
    Prop :=
  (∀ Λ' ∈ s', (fibG S L Λ').Nonempty) ∧
  ∀ Λ' : Submodule (𝓞 K) V', (fibG S L Λ').Nonempty →
    ∃! Λ₀, Λ₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g Λ₀ = Λ'

namespace StabilizerLattices

open SplitBAux

theorem pair_mem_of_fibG (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ') :
    (Λ, S.x₀) ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h (Λ, S.x₀) = (emb S Λ', S.x₀) :=
  ⟨⟨hΛ.1, hΛ.2.1, rfl⟩, Prod.ext (by rw [← hΛ.2.2]; exact inf_perpO S Λ) rfl⟩

theorem fibG_of_pair_mem (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {p : Submodule (𝓞 K) V × V} (hp : p ∈ pairs h L (h S.x₀ S.x₀))
    (e : proj h p = (emb S Λ', S.x₀)) : p.1 ∈ fibG S L Λ' ∧ p.2 = S.x₀ := by
  obtain ⟨Λ, x⟩ := p
  obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
  change Λ ⊓ perpO h x = emb S Λ' at e1
  change x = S.x₀ at e2
  subst e2
  rw [inf_perpO] at e1
  exact ⟨⟨hp.1, hp.2.1, emb_injective S e1⟩, rfl⟩

theorem exists_move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) (p : Submodule (𝓞 K) V × V) :
    ∃ g : Formalism.HermitianLatticesTheory.isom h, p ∈ pairs h L (h S.x₀ S.x₀) →
      g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, S.x₀) ∧
      Formalism.HermitianLatticesTheory.gmap g.1 p.1 ∈ fibG S L (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := by
  by_cases hp : p ∈ pairs h L (h S.x₀ S.x₀)
  · have hne : p.2 ≠ 0 := by
      intro h0
      have := hp.2.2
      rw [h0] at this
      exact S.hx₀ (by simpa using this.symm)
    obtain ⟨g, hg, hgx⟩ := exists_isom_map_of_eq hK hs hd hne hp.2.2
    refine ⟨⟨g, hg⟩, fun _ => ⟨Prod.ext rfl hgx, OrbitRepresentatives.gmap_mem_genus hs hp.1 hg, ?_, rfl⟩⟩
    rw [← hgx]
    exact apply_mem_gmap g hp.2.1
  · exact ⟨1, fun h => absurd h hp⟩

theorem fibG_smul (hs : h.IsSymm) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {Λ' : Submodule (𝓞 K) V'} {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ')
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∈ fibG S L (Formalism.HermitianLatticesTheory.gmap g' Λ') := by
  refine ⟨OrbitRepresentatives.gmap_mem_genus hs hΛ.1 (extOf_mem_isom hs S hg'), ?_, ?_⟩
  · have := apply_mem_gmap (extOf S g') hΛ.2.1
    rwa [extOf_x₀] at this
  · rw [cut_gmap_extOf, hΛ.2.2]

theorem finite_stab_proj (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) {p : Submodule (𝓞 K) V × V}
    (hp : p ∈ pairs h L (h S.x₀ S.x₀)) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p) : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  obtain ⟨g, hg⟩ := exists_move hK hs hd S L p
  obtain ⟨hg1, hg2⟩ := hg hp
  have e : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
    rw [← proj_smul, hg1]
    exact (pair_mem_of_fibG S hg2).2
  have hlat : Submodule.IsFullLattice K (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := isFullLattice_cut S hg2.1.1
  have f1 : Finite (Formalism.ThetaLiftIndependence.autL h' (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1))) :=
    (Formalism.HermitianLatticesTheory.autFinite K V' h' (S.isSymm hs) (trace_pos (S.isTotPosDef hd)) _ hlat).to_subtype
  have f2 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (g • proj h p)) := by
    rw [e]
    exact Finite.of_equiv _ (stabPairEquiv hs S _).symm
  have f3 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p)) :=
    Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (g := g) (a := proj h p) rfl).symm.toEquiv
  exact Set.toFinite _

end StabilizerLattices

open StabilizerLattices SplitBAux in
theorem exists_fibReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : ∃ s', IsFibReps S L s' := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  choose γ hγ using exists_move hK hs hd S L
  obtain ⟨T, hT1, hT2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h')
    {Λ' : Submodule (𝓞 K) V' | (fibG S L Λ').Nonempty}
    (fun g' Λ' ⟨Λ, hΛ⟩ => ⟨_, fibG_smul hs S hΛ g'.2⟩)
    ((fun p => S.cut (Formalism.HermitianLatticesTheory.gmap (γ p).1 p.1)) '' (sX : Set (Submodule (𝓞 K) V × V)))
    (sX.finite_toSet.image _)
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, (hγ p (hsX p hp)).2⟩)
    (by
      rintro Λ' ⟨Λ, hΛ⟩
      obtain ⟨t, ⟨ht, k, hk⟩, -⟩ := hX _ (pair_mem_of_fibG S hΛ).1
      refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
      have e : (k * (γ t)⁻¹) • (Formalism.HermitianLatticesTheory.gmap (γ t).1 t.1, S.x₀) = (Λ, S.x₀) := by
        rw [← (hγ t (hsX t ht)).1, mul_smul, inv_smul_smul, hk]
      obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
      have := gmap_res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2 e1
      rw [hΛ.2.2] at this
      exact ⟨⟨res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2, res_mem_isom S _ _ _⟩, this⟩)
  refine ⟨T, hT1, fun Λ' hΛ' => ?_⟩
  have := hT2 Λ' hΛ'
  simp_rw [exists_smul_iff] at this
  exact this

open StabilizerLattices SplitBAux in
theorem repMass_eq_sum_fib (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {s' : Finset (Submodule (𝓞 K) V')}
    (hs' : IsFibReps S L s') :
    repMass h L (h S.x₀ S.x₀) =
      ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  have hex := exists_classReps hs hd hL
  unfold repMass
  rw [dite_eq_left hex, ← sum_pairs_eq_rep hs hd (h S.x₀ S.x₀) hex.choose_spec hsX hX]
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (proj h) proj_smul
    (pairs h L (h S.x₀ S.x₀)) (proj h '' pairs h L (h S.x₀ S.x₀))
    (pairs_stable hs L _) (fun p hp => Set.mem_image_of_mem _ hp) sX
    (s'.image fun Λ' => (emb S Λ', S.x₀)) hsX
    (by
      intro u hu
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨Λ, hΛ⟩ := hs'.1 Λ' hΛ'
      exact ⟨_, (pair_mem_of_fibG S hΛ).1, (pair_mem_of_fibG S hΛ).2⟩)
    hX
    (by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨g, hg⟩ := exists_move hK hs hd S L p
      obtain ⟨hg1, hg2⟩ := hg hp
      have hgy : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
        rw [← proj_smul, hg1]
        exact (pair_mem_of_fibG S hg2).2
      obtain ⟨Λ₀, ⟨h₀, g', hg', e'⟩, huniq⟩ := hs'.2 _ ⟨_, hg2⟩
      refine ⟨(emb S Λ₀, S.x₀), ⟨Finset.mem_image.mpr ⟨Λ₀, h₀, rfl⟩,
        g⁻¹ * ⟨extOf S g', extOf_mem_isom hs S hg'⟩, ?_⟩, ?_⟩
      · have e0 : (⟨extOf S g', extOf_mem_isom hs S hg'⟩ : Formalism.HermitianLatticesTheory.isom h) • (emb S Λ₀, S.x₀) =
            g • proj h p := by
          rw [hgy, ← e', ← gmap_extOf_emb]
          exact Prod.ext rfl (extOf_x₀ S g')
        rw [mul_smul, e0, inv_smul_smul]
      · rintro t ⟨ht, k, hk⟩
        obtain ⟨Λ₁, h₁, rfl⟩ := Finset.mem_image.mp ht
        have e : (g * k) • (emb S Λ₁, S.x₀) =
            (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
          rw [mul_smul, hk, hgy]
        obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
        have := gmap_res S (g * k).1 (g * k).2 e2 e1
        rw [cut_emb, cut_emb] at this
        rw [huniq Λ₁ ⟨h₁, _, res_mem_isom S _ _ _, this⟩])
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact finite_stab_proj hK hs hd S L hp)
  rw [key, Finset.sum_image (fun A _ B _ e => emb_injective S (Prod.ext_iff.mp e).1)]
  refine Finset.sum_congr rfl fun Λ' _ => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V //
      p ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h p = (emb S Λ', S.x₀)} = Nat.card (fibG S L Λ') :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.1, (fibG_of_pair_mem S p.2.1 p.2.2).1⟩
        invFun := fun Λ => ⟨(Λ.1, S.x₀), pair_mem_of_fibG S Λ.2⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl (fibG_of_pair_mem S p.2.1 p.2.2).2.symm)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabPairEquiv hs S Λ')]

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField Module
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallSum

open BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem repMass_eq_sum {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) {s : Finset (Submodule (𝓞 K) V)}
    (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) (t : K) :
    repMass h L t = ∑ M ∈ s, (repCount h M t : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
  classical
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨s, hsr⟩
  obtain ⟨sX, hsX, hX⟩ := StabilizerLattices.exists_pairReps hs hd hL t
  have e1 := StabilizerLattices.sum_pairs_eq_rep hs hd t hsr hsX hX
  have e2 := StabilizerLattices.sum_pairs_eq_rep hs hd t hex.choose_spec hsX hX
  simp only [repMass, dite_eq_left hex]
  rw [← e2, e1]

theorem integral_of_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {L M : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) : Formalism.HermitianLatticesTheory.IsIntegralLat h M := by
  exact Formalism.HermitianLatticesTheory.genusBasic_int (IsFractionRing.injective (𝓞 K) K)
    (fun r => Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range r) h L M hM.2 hLi

theorem exists_mem_boxSet (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M) {T : ℝ} {x : V}
    (hx : x ∈ M) (hx0 : x ≠ 0) (hxT : ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T) :
    ∃ n ∈ boxSet K F T, h x x = algebraMap F K (n : F) := by
  have hsym : star (h x x) = h x x := by
    rw [← starRingEnd_apply]
    exact hs.eq x x
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hMi x hx x hx)
  have hy' : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y := by rw [hy]; exact hsym
  obtain ⟨n, hn⟩ := QuadraticExtensionConjugation.exists_int_of_star_eq hF y hy'
  have hkey : h x x = algebraMap F K (n : F) := by
    rw [← hy, ← hn]
    rfl
  refine ⟨n, fun φ => ?_, hkey⟩
  rw [← hkey]
  exact ⟨hd x hx0 φ, hxT φ⟩

theorem ballCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M) {T : ℝ} (hT : 0 ≤ T) :
    ballCount h M T =
      1 + ∑ n ∈ (finite_boxSet hK hF T).toFinset, repCount h M (algebraMap F K (n : F)) := by
  classical
  let Fn : 𝓞 F → Finset V := fun n => (StabilizerLattices.finite_rep hd hM (algebraMap F K (n : F))).toFinset
  have hset : {x : V | x ∈ M ∧ ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T} =
      ↑(insert 0 ((finite_boxSet hK hF T).toFinset.biUnion Fn)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      Finset.mem_biUnion, Set.Finite.mem_toFinset, Fn]
    constructor
    · rintro ⟨hx, hxT⟩
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · obtain ⟨n, hn, he⟩ := exists_mem_boxSet hF hs hd hMi hx hx0 hxT
        exact Or.inr ⟨n, hn, hx, he⟩
    · rintro (rfl | ⟨n, hn, hx, he⟩)
      · exact ⟨M.zero_mem, fun φ => by simp [hT]⟩
      · exact ⟨hx, fun φ => by rw [he]; exact (hn φ).2⟩
  obtain ⟨φ0⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h0 : (0 : V) ∉ (finite_boxSet hK hF T).toFinset.biUnion Fn := by
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, Fn, Set.mem_ofPred_eq, not_exists, not_and]
    intro n hn _ he
    have h1 := (hn φ0).1
    rw [← he] at h1
    simp at h1
  have hdisj : ∀ n ∈ (finite_boxSet hK hF T).toFinset, ∀ m ∈ (finite_boxSet hK hF T).toFinset,
      n ≠ m → Disjoint (Fn n) (Fn m) := by
    intro n _ m _ hnm
    rw [Finset.disjoint_left]
    intro x hxn hxm
    simp only [Fn, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hxn hxm
    apply hnm
    exact RingOfIntegers.ext ((algebraMap F K).injective (hxn.2.symm.trans hxm.2))
  unfold ballCount
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem h0, Finset.card_biUnion hdisj, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold repCount
  rw [← Set.coe_ofPred, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (StabilizerLattices.finite_rep hd hM _)]

private theorem repCount_zero_eq_one_of_isTotPosDef {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) (M : Submodule (𝓞 K) V) :
    repCount h M 0 = 1 := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  rw [repCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, M.zero_mem, by simp⟩, fun y => Subtype.ext ?_⟩
  by_contra hne
  have h1 := hd y.1 hne φ
  rw [y.2.2] at h1
  simp at h1

theorem sum_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) {T : ℝ} (hT : 0 ≤ T) :
    ∑ M ∈ s, (ballCount h M T : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F T, repMass h L (algebraMap F K (n : F)) := by
  classical
  have hmass : Formalism.HermitianLatticesTheory.mass h L = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ := by
    have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨s, hsr⟩
    rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h L hex]
    have e1 := repMass_eq_sum hs hd hL hsr 0
    have e2 := repMass_eq_sum hs hd hL hex.choose_spec 0
    simp only [repCount_zero_eq_one_of_isTotPosDef hd, Nat.cast_one, one_div] at e1 e2
    rw [← e2, e1]
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_boxSet hK hF T), hmass]
  have hsplit : ∀ M ∈ s, (ballCount h M T : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ) =
      ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ + ∑ n ∈ (finite_boxSet hK hF T).toFinset,
        (repCount h M (algebraMap F K (n : F)) : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
    intro M hMs
    have hMg := hsr.1 M hMs
    rw [ballCount_eq hK hF hs hd hMg.1.toIsLattice (integral_of_mem_genus hs hL hLi hMg) hT]
    push_cast
    rw [add_div, one_div, Finset.sum_div]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun n _ => (repMass_eq_sum hs hd hL hsr _).symm

end Formalism.HermitianLattices.Ext.L3.BallSum
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem BrA.normD_eq_tprod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hD' : BrA.discrF F h L ≠ ⊥ := by
    intro e
    apply hD
    rw [BrA.discrIdeal_eq_map hF hs, e, Ideal.map_bot]
  rw [BrA.normD_eq hK hF hs, BrA.absNorm_eq_tprod hD']
  exact tprod_congr fun 𝔭 => by rw [BrA.vd_eq hF hs]

theorem integral_of_mem_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {M : Submodule (𝓞 K) V} (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h M ∧ (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭) ∧
      normD h M = normD h L := by
  obtain ⟨hMl, hMg⟩ := hM
  have key : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 M := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact hMg P hP
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M := by
    intro x hx y hy
    rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭.1 𝔭.2
    exact BrA.form_mem_locF hF hLi 𝔭.2.isPrime hg (e ▸ LocF.le_locF 𝔭.1 M hx)
      (e ▸ LocF.le_locF 𝔭.1 M hy)
  have hvd : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭 h𝔭
    rw [← localizedQuotients.vd_locF hF h M h𝔭, ← localizedQuotients.vd_locF hF h L h𝔭, ← e]
    unfold vd
    rw [BrA.discrIdeal_gmap hg]
  refine ⟨hMi, hvd, ?_⟩
  rw [BrA.normD_eq_tprod hK hF hs hd hMl hMi, BrA.normD_eq_tprod hK hF hs hd hL hLi]
  exact tprod_congr fun 𝔭 => by rw [hvd 𝔭.1 𝔭.2]

theorem normD_eq_prod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 :=
  BrA.normD_eq_tprod hK hF hs hd hL hLi

theorem absNorm_span_eq_prod (n : 𝓞 F) (hn : n ≠ 0) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [BrA.absNorm_eq_tprod hI]
  refine tprod_congr fun 𝔭 => ?_
  unfold vF
  simp only [Ideal.span_singleton_le_iff_mem]

end Formalism.HermitianLattices.Ext.L3
end
end
