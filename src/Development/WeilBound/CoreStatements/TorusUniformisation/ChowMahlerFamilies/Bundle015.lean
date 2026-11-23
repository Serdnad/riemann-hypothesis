module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurveInFibre

theorem valAt_inv {X : Scheme.{0}} {Ω K : Type} [Field Ω] [Field K] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {η : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (h : ValAt ξ η a r) (hr : r ≠ 0) :
    ValAt ξ η a⁻¹ r⁻¹ := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  have hl := Scheme.isLocalHom_stalkClosedPointTo η
  have hs : IsUnit s := hl.map_nonunit s (IsUnit.mk0 _ hr)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · exact map_units_inv _ u
  · exact map_units_inv _ u

theorem finite_not_integral {K O A : Type} [Field K] [CommRing O] [CommRing A] (C : Crv.ACurve K) (g : O →+* A)
    (hg : g.FiniteType) (φ : A →+* K) (hO : ∀ i a, φ (g a) ∈ (C.v i).valuationSubring) :
    {i | ¬ ∀ a, φ a ∈ (C.v i).valuationSubring}.Finite := by
  let := g.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType O A from hg).out
  have hfin : ∀ a : A, {i | φ a ∉ (C.v i).valuationSubring}.Finite := by
    intro a
    by_cases h0 : φ a = 0
    · simp [h0]
    · exact (C.fin _ h0).subset fun i hi h1 => hi (le_of_eq h1)
  refine (t.finite_toSet.biUnion fun a _ => hfin a).subset fun i hi => ?_
  by_contra hc
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hc
  refine hi fun a => ?_
  have ha : a ∈ Algebra.adjoin O (t : Set A) := ht ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact hc y hy
  | algebraMap r => exact hO i r
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem ae_centre {X : Scheme.{0}} {K O : Type} [Field K] [CommRing O] (s : X ⟶ Spec (CommRingCat.of O))
    [IsSeparated s] [LocallyOfFiniteType s] (C : Crv.ACurve K) (η : Spec (CommRingCat.of K) ⟶ X)
    (z : ∀ i, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X)
    (hz : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ z i = η)
    (U : X.Opens) (hU : centre η ∈ U) : {i | centre (z i) ∉ U}.Finite := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hU
  have hV : IsAffineOpen V := hV
  have hr : Set.range η ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]
    exact hxV
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec η hr)
  have hφ' : Spec.map φ ≫ hV.fromSpec = η := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨g, hg⟩ := Spec.map_surjective (hV.fromSpec ≫ s)
  have hgf : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 (hg ▸ inferInstance)
  choose ψ hψ using fun i => Spec.map_surjective (z i ≫ s)
  have hsq : ∀ i, ψ i ≫ CommRingCat.ofHom (C.v i).valuationSubring.subtype = g ≫ φ := fun i => by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, hg, ← Category.assoc, ← Category.assoc, hz, hφ']
  have hsq' : ∀ i a, φ.hom (g.hom a) = ((ψ i).hom a : K) := fun i a =>
    (congrArg (fun f => f.hom a) (hsq i)).symm
  refine (finite_not_integral C g.hom hgf φ.hom fun i a => ?_).subset fun i hi hc => hi ?_
  · rw [hsq' i a]
    exact ((ψ i).hom a).2
  · let χ : Γ(X, V) ⟶ CommRingCat.of (C.v i).valuationSubring :=
      CommRingCat.ofHom (φ.hom.codRestrict (C.v i).valuationSubring hc)
    have : IsDominant (Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype)) :=
      ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (C.v i).valuationSubring.subtype).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
        exact bot_le)⟩
    have e : z i = Spec.map χ ≫ hV.fromSpec := by
      refine ext_of_isDominant_of_isSeparated s ?_
        (Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype)) ?_
      · rw [Category.assoc, ← hg, ← hψ, ← Spec.map_comp]
        congr 1
        ext a
        exact (hsq' i a).symm
      · rw [hz, ← Category.assoc, ← Spec.map_comp, ← hφ']
        rfl
    refine hVU ?_
    change centre (z i) ∈ (V : Set X)
    rw [e, ← hV.range_fromSpec]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

end PositivityTheory.Xgn.CurveInFibre

theorem PositivityTheory.Xgn.exists_curve_in_fibre_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) := by
  intro X Ω _ ξ O _ s _ _ ϖ Γ _
  refine ⟨⟨Γ.z, Γ.z_gen, PositivityTheory.Xgn.CurveInFibre.ae_centre s Γ.C Γ.η Γ.z Γ.z_gen⟩, rfl, fun L n _ => ⟨?_, ?_⟩⟩
  · rintro ⟨e, f, r, he, hf, hr, hfin, hd⟩
    refine ⟨Γ.η_spec, Γ.z_spec, e, f, fun i => (r i)⁻¹, he, fun i => (hf i).2, fun i => ⟨inv_ne_zero (hr i).1, ?_⟩,
      ?_, ?_⟩
    · rw [← inv_div]
      exact PositivityTheory.Xgn.CurveInFibre.valAt_inv (hr i).2 (hr i).1
    · simpa using hfin
    · rw [← hd]
      simp
  · rintro ⟨h₀, h, e, f, r, he, hf, hr, hfin, hd⟩
    refine ⟨e, f, fun i => (r i)⁻¹, he, fun i => ⟨h i, hf i⟩, fun i => ⟨inv_ne_zero (hr i).1, ?_⟩, ?_, ?_⟩
    · rw [← inv_div]
      exact PositivityTheory.Xgn.CurveInFibre.valAt_inv (hr i).2 (hr i).1
    · simpa using hfin
    · rw [hd]
      simp
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurvePositivity

theorem change_gen {Ω : Type} [Field Ω] (σ π e f : Ω) (M : ℕ) (hf : f ≠ 0) :
    π / (σ / e) ^ M = π / (σ / f) ^ M * (e / f) ^ M := by
  have hfM : f ^ M ≠ 0 := pow_ne_zero _ hf
  rw [div_pow, div_pow, div_pow, div_div_eq_mul_div, div_div_eq_mul_div]
  by_cases hσ : σ ^ M = 0
  · simp [hσ]
  · field_simp

theorem val_one {K : Type} [Field K] (C : Crv.ACurve K) (hw : ∀ i, 0 < C.w i) (c : K) (hc : c ≠ 0)
    (r t : C.I → K) (M : ℕ) (hr : ∀ i, r i ≠ 0) (hfin : {i | C.v i (r i) ≠ 1}.Finite)
    (hd : ∑ᶠ i, (C.w i : ℤ) * (-WithZero.log (C.v i (r i))) = 0)
    (ht : ∀ i, C.v i (t i) ≤ 1) (hct : ∀ i, c = t i * r i ^ M) (i : C.I) : C.v i (t i) = 1 := by
  have ht0 : ∀ j, t j ≠ 0 := fun j h => hc (by rw [hct j, h, zero_mul])
  have hvt : ∀ j, C.v j (t j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (ht0 j)
  have hvr : ∀ j, C.v j (r j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).2 (hr j)
  have hL : ∀ j, WithZero.log (C.v j c) =
      WithZero.log (C.v j (t j)) + (M : ℤ) * WithZero.log (C.v j (r j)) := by
    intro j
    rw [hct j, map_mul, map_pow, WithZero.log_mul (hvt j) (pow_ne_zero _ (hvr j)), WithZero.log_pow]
    simp
  have hle : ∀ j, WithZero.log (C.v j (t j)) ≤ 0 := by
    intro j
    have := (WithZero.log_le_log (hvt j) one_ne_zero).2 (ht j)
    rwa [WithZero.log_one] at this
  set A : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j (t j)) with hA
  set B : C.I → ℤ := fun j => (C.w j : ℤ) * WithZero.log (C.v j c) with hB
  set D : C.I → ℤ := fun j => (C.w j : ℤ) * (-WithZero.log (C.v j (r j))) with hD
  have hsB : (Function.support B).Finite := (C.fin c hc).subset (fun j hj => by
    simp only [Function.mem_support, hB] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, mul_zero])
  have hsD : (Function.support D).Finite := hfin.subset (fun j hj => by
    simp only [Function.mem_support, hD] at hj
    intro h1; apply hj; rw [h1, WithZero.log_one, neg_zero, mul_zero])
  have hABD : A = fun j => B j + (M : ℤ) * D j := by
    funext j; simp only [hA, hB, hD]; rw [hL j]; ring
  have hsMD : (Function.support fun j => (M : ℤ) * D j).Finite :=
    hsD.subset (Function.support_mul_subset_right _ _)
  have hsA : (Function.support A).Finite := by
    rw [hABD]; exact (hsB.union hsMD).subset (Function.support_add _ _)
  have hsum : ∑ᶠ j, A j = 0 := by
    rw [hABD, finsum_add_distrib hsB hsMD, ← mul_finsum]
    simp only [hB, hD]
    rw [C.prod c hc, hd, mul_zero, add_zero]
  have hnn : ∀ j, 0 ≤ -A j := fun j => by
    simp only [hA]; have := hle j; have := hw j; nlinarith
  have hsA' : (Function.support fun j => -A j).Finite :=
    hsA.subset (fun j hj => by simpa [Function.mem_support] using hj)
  have h1 := single_le_finsum i hsA' hnn
  rw [finsum_neg_distrib, hsum, neg_zero] at h1
  have h2 : WithZero.log (C.v i (t i)) = 0 := by
    have h3 : A i = 0 := by have := hnn i; linarith
    simp only [hA] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (by have := hw i; omega)
    · exact h4
  rw [← WithZero.exp_log (hvt i), h2, WithZero.exp_zero]

end PositivityTheory.Xgn.CurvePositivity

theorem PositivityTheory.Xgn.degree_zero_curve_positive : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (L : Lat ξ Ω) (σ π : Ω) (M : ℕ) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → L.IsVB 1 ⊤ → 0 < M → Γ.HasDeg L 0 → (∀ (p : Cpt ξ) (e : Ω), L.IsGenAt p e → π / (σ / e) ^ M ∈ regAt ξ p) → (∀ e, L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e → unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ (π / (σ / e) ^ M)) → ∀ (i : Γ.C.I) (h : genPt ξ ⤳ centre (Γ.z i)) (e : Ω), L.IsGenAt ⟨centre (Γ.z i), h⟩ e → unitAt ξ ⟨centre (Γ.z i), h⟩ (π / (σ / e) ^ M) := by
  intro X Ω _ ξ O _ s _ _ ϖ L σ π M Γ hξ _ _ hdeg hreg hunit i h e he
  obtain ⟨e0, f, r, he0, hf, hr, hfin, hd⟩ := hdeg
  have hf' : ∀ j, L.IsGenAt ⟨centre (Γ.z j), Γ.z_spec j⟩ (f j) := fun j => (hf j).2
  obtain ⟨c, hc⟩ := ProjectiveLinePlaces.valAt_of_unit Γ.η_spec (hunit e0 he0)
  choose g hg using fun j => hreg _ _ (hf' j)
  let t : ∀ j, (Γ.C.v j).valuationSubring := fun j => (Scheme.stalkClosedPointTo (Γ.z j)).hom (g j)
  have hz : ∀ j, ValAt ξ (Γ.z j) (π / (σ / f j) ^ M) (t j) := fun j => ⟨Γ.z_spec j, g j, hg j, rfl⟩
  have hη : ∀ j, ValAt ξ Γ.η (π / (σ / f j) ^ M) (t j : Γ.κ) := fun j =>
    ProjectiveLinePlaces.valAt_restrict _ (Γ.z_gen j) Γ.η_spec (hz j)
  have hct : ∀ j, (c : Γ.κ) = (t j : Γ.κ) * r j ^ M := fun j => by
    have h2 := CoordModel.valAt_mul (hη j) (ProjectiveLinePlaces.valAt_pow (hr j).2 M)
    rw [← PositivityTheory.Xgn.CurvePositivity.change_gen σ π e0 (f j) M (hf' j).1] at h2
    exact CoordModel.valAt_unique hξ hc h2
  have hv := PositivityTheory.Xgn.CurvePositivity.val_one Γ.C Γ.w_pos c c.ne_zero r (fun j => (t j : Γ.κ)) M
    (fun j => (hr j).1) hfin hd (fun j => (t j).2) hct i
  have ht0 : (t i : Γ.κ) ≠ 0 := fun h0 => by simp [h0] at hv
  have hu : IsUnit (t i) := by
    refine IsUnit.of_mul_eq_one ⟨(t i : Γ.κ)⁻¹, ?_⟩ (Subtype.ext (mul_inv_cancel₀ ht0))
    change Γ.C.v i _ ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hgu : IsUnit (g i) := (Scheme.isLocalHom_stalkClosedPointTo' (Γ.z i)).map_nonunit (g i) hu
  obtain ⟨u, hu1, hu2⟩ := (CptModel.unitAt_iff ξ _ _).1 (ProjectiveLinePlaces.unitAt_div he (hf' i))
  refine (CptModel.unitAt_iff ξ _ _).2 ⟨g i * u ^ M, hgu.mul (hu1.pow M), ?_⟩
  rw [PositivityTheory.Xgn.CurvePositivity.change_gen σ π e (f i) M (hf' i).1, map_mul, map_pow, hu2]
  exact congrArg (· * (e / f i) ^ M) (hg i)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagframe_basis

variable {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {N : ℕ}

theorem repr_expand (w u : Module.Basis (Fin N) Ω V) (v : V) (j : Fin N) :
    w.repr v j = ∑ q, u.repr v q * w.repr (u q) j := by
  conv_lhs => rw [← u.sum_repr v]
  exact GradedFrameCharacterisation.repr_sum_smul w _ _ j

theorem top_coord (w u : Module.Basis (Fin N) Ω V) (hup : ∀ i j, i < j → w.repr (u i) j = 0)
    (v : V) (i : Fin N) (hv : ∀ j, i < j → u.repr v j = 0) :
    (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = u.repr v i * w.repr (u i) i := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [repr_expand w u]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : i < q
    · rw [hv q hq, zero_mul]
    · rw [hup q j (lt_of_le_of_lt (not_lt.mp hq) hj), mul_zero]
  · rw [repr_expand w u]
    refine Finset.sum_eq_single i (fun q _ hq => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hq with h | h
    · rw [hup q i h, mul_zero]
    · rw [hv q h, zero_mul]

theorem vanish_above (w u : Module.Basis (Fin N) Ω V) (hup : ∀ i j, i < j → w.repr (u i) j = 0)
    (hd : ∀ i, w.repr (u i) i ≠ 0) (v : V) (i : Fin N) (hv : ∀ j, i < j → w.repr v j = 0) :
    ∀ j, i < j → u.repr v j = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hne : (Finset.univ.filter (fun j => i < j ∧ u.repr v j ≠ 0)).Nonempty := by
    obtain ⟨j, hj, hj'⟩ := hcon
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hj'⟩⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image _ id hne
  have hm := (Finset.mem_filter.mp hmS).2
  have habove : ∀ j, m < j → u.repr v j = 0 := by
    intro j hj
    by_contra h0
    have hjS := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hm.1 hj, h0⟩)
    exact absurd hjS (not_le.mpr hj)
  have ht := top_coord w u hup v m habove
  have h0 := hv m hm.1
  rw [ht.2] at h0
  exact mul_ne_zero hm.2 (hd m) h0

theorem exists_basis (w : Module.Basis (Fin N) Ω V) (f : Fin N → V)
    (hup : ∀ i j, i < j → w.repr (f i) j = 0) (hd : ∀ i, w.repr (f i) i ≠ 0) :
    ∃ u : Module.Basis (Fin N) Ω V, ∀ i, u i = f i := by
  classical
  rcases isEmpty_or_nonempty (Fin N) with hN | hN
  · exact ⟨w, fun i => isEmptyElim i⟩
  · have hli : LinearIndependent Ω f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      by_contra hcon
      push_neg at hcon
      have hne : (Finset.univ.filter (fun j => g j ≠ 0)).Nonempty := by
        obtain ⟨j, hj⟩ := hcon
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image _ id hne
      have hm := (Finset.mem_filter.mp hmS).2
      have h0 := congrArg (fun v => w.repr v m) hg

      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h0
      rw [Finset.sum_eq_single m] at h0
      · exact mul_ne_zero hm (hd m) h0
      · intro q _ hqm
        rcases lt_or_gt_of_ne hqm with h | h
        · rw [hup q m h, mul_zero]
        · have hgq : g q = 0 := by
            by_contra hq
            exact absurd (hmax q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)) (not_le.mpr h)
          rw [hgq, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ m) h
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli ?_, fun i => ?_⟩
    · rw [Module.finrank_eq_card_basis w]
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank]

theorem coords_mem {O : Type*} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (L : AddSubgroup V)
    (u : Module.Basis (Fin N) Ω V) (hst : ∀ a ∈ R, ∀ i, a • u i ∈ L)
    (htop : ∀ v ∈ L, ∀ i, (∀ j, i < j → u.repr v j = 0) → u.repr v i ∈ R) :
    ∀ v ∈ L, ∀ i, u.repr v i ∈ R := by
  classical
  have main : ∀ k : ℕ, ∀ v ∈ L, (∀ j : Fin N, k ≤ j.val → u.repr v j = 0) → ∀ i, u.repr v i ∈ R := by
    intro k
    induction k with
    | zero =>
      intro v _ hv i
      rw [hv i (Nat.zero_le _)]
      exact R.zero_mem
    | succ k ih =>
      intro v hvL hv
      by_cases hk : k < N
      · have ha : u.repr v ⟨k, hk⟩ ∈ R :=
          htop v hvL ⟨k, hk⟩ (fun j hj => hv j (Nat.succ_le_of_lt (Fin.lt_def.mp hj)))
        have hv'L : v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩ ∈ L := L.sub_mem hvL (hst _ ha _)
        have hrep : ∀ j, u.repr (v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩) j =
            u.repr v j - u.repr v ⟨k, hk⟩ * (if (⟨k, hk⟩ : Fin N) = j then 1 else 0) := by
          intro j
          rw [map_sub, map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
            Finsupp.single_apply, smul_eq_mul]
        have hv' : ∀ j : Fin N, k ≤ j.val → u.repr (v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩) j = 0 := by
          intro j hj
          rw [hrep j]
          rcases Nat.lt_or_eq_of_le hj with h | h
          · have hne : (⟨k, hk⟩ : Fin N) ≠ j := fun e => by
              rw [← e] at h
              exact lt_irrefl _ h
            rw [hv j h, if_neg hne, mul_zero, sub_zero]
          · have he : (⟨k, hk⟩ : Fin N) = j := Fin.ext h
            subst he
            rw [if_pos rfl, mul_one, sub_self]
        intro i
        have hi := ih _ hv'L hv' i
        rw [hrep i] at hi
        have h2 : u.repr v ⟨k, hk⟩ * (if (⟨k, hk⟩ : Fin N) = i then (1 : Ω) else 0) ∈ R := by
          split_ifs
          · rw [mul_one]
            exact ha
          · rw [mul_zero]
            exact R.zero_mem
        have h3 := R.add_mem hi h2
        rwa [sub_add_cancel] at h3
      · intro i
        exact ih v hvL (fun j hj => hv j (by have := j.isLt; omega)) i
  intro v hv i
  exact main N v hv (fun j hj => absurd j.isLt (not_lt.mpr hj)) i

end PositivityTheory.Xgn.A_flagframe_basis

open PositivityTheory.Xgn.A_flagframe_basis in
theorem PositivityTheory.Xgn.t_flagframe_basis : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b ↔ ∀ s, mseg x s ≠ 0 → ∃ u : Module.Basis (Fin N) Ω V, (∀ i j, i < j → w.repr (u i) j = 0) ∧ (∀ i, w.repr (u i) i = chartMon x s (b i)) ∧ ∀ v, v ∈ E.lat s ↔ ∀ i, u.repr v i ∈ chartRing O (mseg x) s := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ E w b
  have hmon : ∀ s, mseg x s ≠ 0 → ∀ d : K → ℤ, chartMon x s d ≠ 0 := by
    intro s hs d
    have hs' : ∏ k : K, x ⟨k, s k⟩ ≠ 0 := hs
    show ∏ k : K, x ⟨k, s k⟩ ^ d k ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun k _ =>
      zpow_ne_zero _ (Finset.prod_ne_zero_iff.mp hs' k (Finset.mem_univ _))
  constructor
  · intro hF s hs
    have hdeg : ∀ i, ∃ f ∈ E.lat s, (∀ j, i < j → w.repr f j = 0) ∧ w.repr f i = chartMon x s (b i) := by
      intro i
      have hmem : chartMon x s (b i) ∈ degLat O x (b i) s := ⟨1, Subalgebra.one_mem _, (one_mul _).symm⟩
      rw [← hF.graded s hs i] at hmem
      exact hmem
    choose f hfL hfup hfd using hdeg
    obtain ⟨u, hu⟩ := exists_basis w f hfup (fun i => by rw [hfd i]; exact hmon s hs (b i))
    have hup_u : ∀ i j, i < j → w.repr (u i) j = 0 := fun i j hij => by
      rw [hu i]
      exact hfup i j hij
    refine ⟨u, hup_u, fun i => by rw [hu i]; exact hfd i, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · refine coords_mem (chartRing O (mseg x) s) (E.lat s) u
        (fun a ha i => by rw [hu i]; exact E.stable s a ha _ (hfL i)) ?_ v hv
      intro v' hv' i hup'
      have ht := top_coord w u hup_u v' i hup'
      have hin : w.repr v' i ∈ degLat O x (b i) s := by
        rw [← hF.graded s hs i]
        exact ⟨v', hv', ht.1, rfl⟩
      obtain ⟨a, ha, hae⟩ := hin
      rw [ht.2, hu i, hfd i] at hae
      have hc := mul_right_cancel₀ (hmon s hs (b i)) hae
      rw [hc]
      exact ha
    · rw [← u.sum_repr v]
      exact AddSubgroup.sum_mem _ fun q _ => by
        rw [hu q]
        exact E.stable s _ (hv q) _ (hfL q)
  · intro hR
    refine ⟨fun s hs i => ?_⟩
    obtain ⟨u, hup, hdiag, hmem⟩ := hR s hs
    ext t
    constructor
    · rintro ⟨v, hv, habove, rfl⟩
      have hd : ∀ i, w.repr (u i) i ≠ 0 := fun i => by
        rw [hdiag i]
        exact hmon s hs (b i)
      have hu_above := vanish_above w u hup hd v i habove
      have ht := top_coord w u hup v i hu_above
      exact ⟨u.repr v i, (hmem v).mp hv i, by rw [ht.2, hdiag i]; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a • u i, (hmem _).mpr fun j => ?_, fun j hj => ?_, ?_⟩
      · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        split_ifs
        · rw [mul_one]
          exact ha
        · rw [mul_zero]
          exact Subalgebra.zero_mem _
      · rw [map_smul, Finsupp.smul_apply, hup i j hj, smul_zero]
      · rw [map_smul, Finsupp.smul_apply, hdiag i, smul_eq_mul]
        rfl
end
