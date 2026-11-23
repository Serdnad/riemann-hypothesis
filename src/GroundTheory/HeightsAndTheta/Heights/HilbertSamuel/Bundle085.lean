module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibrePt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCoeffCycle
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle080
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle005
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle012
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountIntegrals

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section


open ProjFrameFibrePt in
theorem ProjFrameGenPtRel.proof : ProjFrameGenPtRel.Statement := by
  intro D Ω _ _ κ _ x e _ hF G
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro n hn
    have h1 : (C (n : ℤ) : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))) ∈ graphP x e := by
      rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, eq_intCast, Int.cast_natCast]
      exact hn
    rw [graphP, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (C : (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* MvPolynomial Unit _), C_eq_zero,
      ← map_natCast (Ideal.Quotient.mk (coordIdeal ℤ x)), Ideal.Quotient.eq_zero_iff_mem, coordIdeal,
      RingHom.mem_ker, map_natCast, ← map_natCast (Polynomial.C : Ω →+* Polynomial Ω), Polynomial.C_eq_zero] at h1
    exact_mod_cast h1
  ·
    have hker : ∀ h : MRing (GlobalTheory κ),
        aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) h = 0 ↔ h ∈ coordIdeal ℤ x := by
      intro h
      constructor
      · intro h0
        have h2 : rename (fun p : Ix κ => aV D p.2) h ∈ graphP x e := by
          rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_rename]
          exact h0
        rwa [graphP, graphIdeal, RingHom.mem_ker, graphMap_rename_inl, C_eq_zero,
          Ideal.Quotient.eq_zero_iff_mem] at h2
      · intro hh
        exact aeval_inl_eq_zero G hh
    ext f
    have hu : f ∈ coordIdeal ℤ (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) ↔
        ∀ d, homogeneousComponent d f ∈ coordIdeal ℤ x := by
      rw [coordIdeal, RingHom.mem_ker, Polynomial.ext_iff]
      simp only [coeff_coneMap, Polynomial.coeff_zero, hker]
    rw [hu]
    constructor
    · intro h
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => h d
    · intro h d
      exact coordIdeal_isHomogIdeal ℤ x f h d
  ·
    intro k
    have h := x'_frame_mul G (e := e) k
    change G.x' (bV κ k) * G.x' (aV D (e 0).2) = G.x' (bV κ 0) * G.x' (aV D (e k).2)
    linear_combination -h
  ·
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_fieldRange] at hy
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨f, g, _, rfl⟩ := G.gen c
      have key : ∀ h : MRing (GlobalTheory (Fin (D + 1))), algebraMap G.Φ G.Φ' (aeval G.x h) ∈
          Subfield.closure (Set.range fun k : Fin (D + 1) => G.x' ⟨Sum.inr (), k⟩) := by
        intro h
        induction h using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, eq_intCast, map_intCast]
          exact intCast_mem _ a
        | add p q hp hq =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hp hq
        | mul_X p i hp =>
          rw [map_mul, map_mul, aeval_X]
          exact mul_mem hp (Subfield.subset_closure ⟨i.2, G.compat i⟩)
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨G.x ⟨(), k⟩, (G.compat ⟨(), k⟩).symm⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GenericFibreVar.proof : GenericFibreVar.Statement := by
  intro K _ ι _ Ω _ y D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (mCoordIdeal y).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ mCoordIdeal y → m = 0 := by
    intro m hm
    have h1 : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
    rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) = KH.genIdeal y := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq
      (D + Fintype.card K) _ ?_
    rw [hform, hdim, show D + 1 + Fintype.card K = (D + Fintype.card K) + 1 by omega]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockHorizDiv

section Local

variable {R : Type*} [CommRing R]

theorem length_loc_eq (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R} (h : J₁ ≤ J₂) {t : R} (ht : t ∉ W)
    (htJ : ∀ a ∈ J₂, t * a ∈ J₁) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
  let q : (R ⧸ J₁) →ₗ[R] (R ⧸ J₂) := Submodule.factor h
  let φ := IsLocalizedModule.mapExtendScalars W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J₁))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J₂)) (Localization.AtPrime W) q
  have hsurj : Function.Surjective φ :=
    IsLocalizedModule.map_surjective W.primeCompl _ _ q (Submodule.factor_surjective h)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have h0 : LocalizedModule.mk (q (Submodule.Quotient.mk a)) s = 0 := by
        rw [← hy]
        exact (IsLocalizedModule.map_LocalizedModules W.primeCompl q _ s).symm
      rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero'] at h0 ⊢
      obtain ⟨u, hu⟩ := h0
      refine ⟨⟨t, ht⟩ * u, ?_⟩
      change u • (Submodule.Quotient.mk a : R ⧸ J₂) = 0 at hu
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at hu ⊢
      have := htJ _ hu
      simpa [mul_assoc] using this
  exact (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).length_eq

theorem multAt_eq_of_mul {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (W : Ideal (MRingOver R ι)) [W.IsPrime] {J₁ J₂ : Ideal (MRingOver R ι)} {t₁ t₂ : MRingOver R ι} (h₁ : t₁ ∉ W)
    (h₂ : t₂ ∉ W) (hJ₁ : ∀ a ∈ J₂, t₁ * a ∈ J₁) (hJ₂ : ∀ a ∈ J₁, t₂ * a ∈ J₂) : multAt J₁ W = multAt J₂ W := by
  have e₁ := length_loc_eq W (le_sup_left : J₁ ≤ J₁ ⊔ J₂) h₁ fun a ha => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
    rw [mul_add]
    exact J₁.add_mem (J₁.mul_mem_left _ hy) (hJ₁ z hz)
  have e₂ := length_loc_eq W (le_sup_right : J₂ ≤ J₁ ⊔ J₂) h₂ fun a ha => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
    rw [mul_add]
    exact J₂.add_mem (hJ₂ y hy) (J₂.mul_mem_left _ hz)
  unfold multAt
  rw [dite_eq_left ‹W.IsPrime›, dite_eq_left ‹W.IsPrime›, e₁, e₂]

theorem mem_minimalPrimes_iff {I₁ I₂ W : Ideal R}
    (h : ∀ Q : Ideal R, Q.IsPrime → Q ≤ W → (I₁ ≤ Q ↔ I₂ ≤ Q)) :
    W ∈ I₁.minimalPrimes ↔ W ∈ I₂.minimalPrimes := by
  have key : ∀ {I₁ I₂ : Ideal R}, (∀ Q : Ideal R, Q.IsPrime → Q ≤ W → (I₁ ≤ Q ↔ I₂ ≤ Q)) →
      W ∈ I₁.minimalPrimes → W ∈ I₂.minimalPrimes := by
    intro I₁ I₂ h hW
    refine ⟨⟨hW.1.1, (h W hW.1.1 le_rfl).1 hW.1.2⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, (h Q hQ.1 hQW).2 hQ.2⟩ hQW⟩
  exact ⟨key h, key fun Q hQ hQW => (h Q hQ hQW).symm⟩

end Local

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem rel_mem' {x x' : Ix κ → Ω} {c : κ} {l : Ix κ → ℤ} (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j)
    (k : Ix κ) (n : Ix κ → ℤ) (hn : ∑ j, (n j : Ω) * x' j = x k) :
    X ⟨0, k.2⟩ * twoBlockNum l - X ⟨0, c⟩ * ∑ j : Ix κ, C (n j) * X ⟨1, j.2⟩ ∈ twoBlockIdeal x x' := by
  show mConeMap (pair x x') _ = 0
  rw [map_sub, map_mul, map_mul, TwoBlockCoeffCycle.mConeMap_X, TwoBlockCoeffCycle.mConeMap_X, twoBlockNum,
    TwoBlockCoeffCycle.mConeMap_lin, TwoBlockCoeffCycle.mConeMap_lin]
  simp only [TwoBlockCoeffCycle.pair_one, TwoBlockCoeffCycle.pair_zero', ← hl, hn]
  ring

theorem intCast_not_mem {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {Q : Ideal (MRing ι)} (hQ : IsHorizontal Q) {d : ℤ}
    (hd : d ≠ 0) : (d : MRing ι) ∉ Q := by
  intro h
  have : d ∈ Q.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, eq_intCast]
    exact h
  rw [hQ, Ideal.mem_bot] at this
  exact hd this

theorem mul_mem_of_sup {R : Type*} [CommRing R] {P J : Ideal R} {s t : R} (hP : P ≤ J) (hs : t * s ∈ J) :
    ∀ a ∈ P ⊔ Ideal.span {s}, t * a ∈ J := by
  intro a ha
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  rw [mul_add, mul_left_comm]
  exact J.add_mem (J.mul_mem_left _ (hP hy)) (J.mul_mem_left _ hs)

theorem den_rel {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ j₀ : κ, (d : MRing (FinTwoTypeFamily κ)) * X ⟨0, c⟩ * X ⟨1, j₀⟩ ∈
      twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} := by
  obtain ⟨d, hd0, hdB⟩ := ChangeOfLattice.exists_clear_den B
  refine ⟨d, by exact_mod_cast hd0, fun j₀ => ?_⟩
  let j : Ix κ := ⟨(), j₀⟩
  choose N hN using hdB j
  have hNx : ∑ k, (N k : Ω) * x k = ((d : ℤ) : Ω) * matAct B x j := by
    simp only [matAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ((N k : ℚ) : Ω) = ((d : ℚ) : Ω) * ((B j k : ℚ) : Ω) := by rw [← hN k]; push_cast; ring
    push_cast at this ⊢
    rw [this]
    ring
  have hrel := TwoBlockCoeffCycle.rel_mem hl (d : ℤ) N j hNx
  have := Submodule.add_mem_sup hrel
    (Ideal.mul_mem_right (∑ k : Ix κ, C (N k) * X ⟨0, k.2⟩) _ (Ideal.mem_span_singleton_self (twoBlockNum l)))
  simpa using this

theorem num_rel {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hsp : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)))
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) (i₀ : κ) :
    X ⟨0, i₀⟩ * twoBlockNum l ∈ twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} := by
  let k : Ix κ := ⟨(), i₀⟩
  have hk : x k ∈ Submodule.span ℤ (Set.range (matAct B x)) := hsp (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hk
  have hn' : ∑ j, (n j : Ω) * matAct B x j = x k := by simpa [zsmul_eq_mul] using hn
  have hrel := rel_mem' hl k n hn'
  have := Submodule.add_mem_sup hrel
    (Ideal.mul_mem_right (∑ j : Ix κ, C (n j) * X ⟨1, j.2⟩) _ (Ideal.mem_span_singleton_self (twoBlockDen c)))
  simpa [twoBlockDen] using this

theorem sup_le_iff_of_horiz {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hsp : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)))
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) {Q : Ideal (MRing (FinTwoTypeFamily κ))} (hQ : Q.IsPrime)
    (hH : IsHorizontal Q) (hR : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Q) :
    twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} ≤ Q ↔
      twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} ≤ Q := by
  obtain ⟨i₀, hi₀⟩ := hR 0
  obtain ⟨j₀, hj₀⟩ := hR 1
  obtain ⟨d, hd0, hd⟩ := den_rel (c := c) (l := l) hl
  constructor
  · intro h
    refine sup_le (le_sup_left.trans h) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    rcases hQ.mem_or_mem (h (hd j₀)) with h1 | h1
    · rcases hQ.mem_or_mem h1 with h2 | h2
      · exact absurd h2 (intCast_not_mem hH hd0)
      · exact h2
    · exact absurd h1 hj₀
  · intro h
    refine sup_le (le_sup_left.trans h) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    rcases hQ.mem_or_mem (h (num_rel hsp hl i₀)) with h1 | h1
    · exact absurd h1 hi₀
    · exact h1

end TwoBlockHorizDiv


open TwoBlockHorizDiv in
theorem TwoBlockHorizDiv.proof : TwoBlockHorizDiv.Statement := by
  intro Ω _ _ κ _ x B c l hsp hl W hW
  have hiff : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W → ∀ Q : Ideal (MRing (FinTwoTypeFamily κ)), Q.IsPrime → Q ≤ W →
      (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} ≤ Q ↔
        twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} ≤ Q) := by
    intro hr Q hQ hQW
    have hH : IsHorizontal Q := by
      unfold IsHorizontal at hW ⊢
      exact le_bot_iff.mp (hW ▸ Ideal.comap_mono hQW)
    have hR : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Q := fun k => (hr k).imp fun i hi h => hi (hQW h)
    exact sup_le_iff_of_horiz hsp hl hQ hH hR
  refine ⟨⟨fun ⟨hm, hr⟩ => ⟨(mem_minimalPrimes_iff (hiff hr)).1 hm, hr⟩,
    fun ⟨hm, hr⟩ => ⟨(mem_minimalPrimes_iff (hiff hr)).2 hm, hr⟩⟩, ?_⟩
  rintro ⟨hm, hr⟩
  have : W.IsPrime := hm.1.1
  obtain ⟨i₀, hi₀⟩ := hr 0
  obtain ⟨j₀, hj₀⟩ := hr 1
  obtain ⟨d, hd0, hd⟩ := den_rel (c := c) (l := l) hl
  refine multAt_eq_of_mul W (t₁ := (d : MRing (FinTwoTypeFamily κ)) * X ⟨1, j₀⟩) (t₂ := X ⟨0, i₀⟩) ?_ hi₀ ?_ ?_
  · intro h
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› h with h1 | h1
    · exact intCast_not_mem hW hd0 h1
    · exact hj₀ h1
  · refine mul_mem_of_sup le_sup_left ?_
    have : (d : MRing (FinTwoTypeFamily κ)) * X ⟨1, j₀⟩ * twoBlockDen c = (d : MRing (FinTwoTypeFamily κ)) * X ⟨0, c⟩ * X ⟨1, j₀⟩ := by
      rw [twoBlockDen]; ring
    rw [this]
    exact hd j₀
  · exact mul_mem_of_sup le_sup_left (num_rel hsp hl i₀)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SupBoundCount

noncomputable section

theorem BlockResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    BlockResolutionFormsIndependent.Statement := by
  intro D K _ _ ι _ Ω _ _ d n r b hb a ha
  choose f hf hbf using hb.1
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg

  set F : ((Σ k, ι k) → ℂ) → ℂ := fun z => ∑ k, a k * eval z (map (Int.castRingHom ℂ) (f k)) with hF
  have ha' : ∀ x : d.R.X, F (blockPt d x) = 0 := by
    intro x
    have := ha x
    simp only [hbf, eval_map_int_rat] at this
    exact this
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb.2.1
    simp only [hbf, SupBoundCount.aeval_map_int] at this
    exact this
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)

  have hev : ∀ (s : MRing ι) (e : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s e → ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
        (∏ k, c k ^ e k) * eval z (map (Int.castRingHom ℂ) s) := by
    intro s e hs c z
    rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hc : (∏ i : (Σ k, ι k), c i.1 ^ m i) = ∏ k, c k ^ e k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ i, c k ^ m ⟨k, i⟩ = _
      rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
    simp only [mul_pow, Finset.prod_mul_distrib, hc]
    ring

  have hsmul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      F (fun p => c p.1 * z p) = (∏ k, c k ^ blockDeg d.k₀ n k) * F z := by
    intro c z
    simp only [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hev (f k) _ (hf k) c z]
    ring

  have hoff : ∀ z, z ∈ mcPts (mCoordIdeal d.y) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨x, c, hc, hxz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 := ha' x
    rw [show blockPt d x = d.R.lift x x from rfl, hxz, hsmul] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))

  have hpts : ∀ z ∈ mcPts (mCoordIdeal d.y), F z = 0 := by
    intro z hz
    have hcl := hND K ι (mCoordIdeal d.y) (D + 1) g d.arith hgP hz
    have hsub : {z | z ∈ mcPts (mCoordIdeal d.y) ∧
        eval z (map (Int.castRingHom ℂ) g) ≠ 0} ⊆ {z | F z = 0} := by
      intro z' hz'
      exact hoff z' hz'.1 hz'.2
    exact (isClosed_eq hFc continuous_const).closure_subset_iff.2 hsub hcl
  exact coeff_eq_zero hli (mcPts_nonempty d) hpts

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem SecCochReduce.map_map_int {K : Type} {ι : K → Type} (p : ℕ) (f : MRing ι) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (MvPolynomial.map (Int.castRingHom ℤ) f) =
      MvPolynomial.map (Int.castRingHom (ZMod p)) f := by
  rw [MvPolynomial.map_map]
  congr 1

theorem SecCochReduce.proof : SecCochReduce.Statement := by
  intro K _ _ ι _ _ Ω _ y p a s hs
  funext J
  rw [FibreReduction.redCoch_apply]
  by_cases hz : ∃ k, y ⟨k, GenOnFibres.cellChart J k⟩ = 0
  · obtain ⟨k, h0⟩ := hz
    have := GenOnFibres.subsingleton_loc (S := ZMod p) (GenOnFibres.cellChart_mem J k) h0
    exact Subsingleton.elim _ _
  · push Not at hz
    obtain ⟨e, F, hF, _, heq⟩ := GenOnFibres.secCoch_spec (S := ℤ) hs J hz
    have hrep : GenOnFibres.IsRep y (ZMod p) (KH.cellMon (ZMod p) J.1)
        (FibreReduction.redLoc y p J.1 (GenOnFibres.secCoch y ℤ s a J)) (GenOnFibres.cellChart J) s a := by
      refine ⟨e, F, hF, GenOnFibres.cmon_mem (ZMod p) (GenOnFibres.cellChart_mem J) e, ?_⟩
      rw [heq, FibreReduction.redLoc_mk, FibreReduction.redRing_mk, SecCochReduce.map_map_int]
      congr 1
      exact Subtype.ext (SecCochReduce.map_map_int p _)
    exact hrep.unique (GenOnFibres.secCoch_spec hs J hz)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
