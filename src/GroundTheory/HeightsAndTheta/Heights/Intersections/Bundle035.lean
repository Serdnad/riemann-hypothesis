module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle030
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem regRing_mem_locRing {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((x : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W :=
  x.2 W hW hPW

def regToLoc (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) : regRing P →+* locRing P W where
  toFun x := ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

theorem regToLoc_apply {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    regToLoc P W hW hPW x = ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩ :=
  rfl

theorem regToLoc_coe {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((regToLoc P W hW hPW x : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) :=
  (congrArg Subtype.val (regToLoc_apply hW hPW x)).trans (Subtype.coe_mk _ _)

def regMaxAt (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    Ideal (regRing P) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (regToLoc P W hW hPW)

theorem not_mem_regMaxAt_iff {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W)
    (hloc : IsLocalRing (locRing P W)) (x : regRing P) :
    x ∉ regMaxAt P W hW hPW hloc ↔
      ∃ z ∈ locRing P W, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 := by
  have hc : ∀ b : locRing P W, ((regToLoc P W hW hPW x * b : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * b := fun b => by
    rw [Subring.coe_mul, regToLoc_coe]
  simp only [regMaxAt, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    refine ⟨b.1, b.2, ?_⟩
    rw [← hc b, hb, Subring.coe_one]
  · rintro ⟨z, hz, h⟩
    refine IsUnit.of_mul_eq_one (a := regToLoc P W hW hPW x) ⟨z, hz⟩ (Subtype.ext ?_)
    rw [hc, Subring.coe_one]
    exact h

theorem intCast_mem_regMaxAt (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)} (hPp : P.IsPrime)
    (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) {n : ℤ} (hn : C n ∈ W) :
    (n : regRing P) ∈ regMaxAt P W hW hPW hloc := by
  by_contra h
  obtain ⟨z, hz, h⟩ := (not_mem_regMaxAt_iff hW hPW hloc _).1 h
  have h1W : (1 : MRing ι) ∉ W := fun h => hW.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hu := ((hL K ι P W hPp hW.1.1 hPW).2 (n : locRing P W) (C n) 1 0 (RegularityDenominator.isMultiHomog_C n)
    AvoidRing.isMultiHomog_one h1W (by simp [eq_intCast C n])).1
  refine hu (IsUnit.of_mul_eq_one (a := (n : locRing P W)) ⟨z, hz⟩ (Subtype.ext ?_)) hn
  simpa using h

theorem regMaxAt_isMaximal (hO : RegularityOrder.Statement) (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    (regMaxAt P W hW hPW hloc).IsMaximal := by
  have : (regMaxAt P W hW hPW hloc).IsPrime := by unfold regMaxAt; infer_instance
  have : Module.Finite ℤ (regRing P) := (hO K ι P hP).2.1
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
  have hn : n ∈ (regMaxAt P W hW hPW hloc).comap (algebraMap ℤ (regRing P)) := by
    rw [Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
    exact intCast_mem_regMaxAt hL hP.2.1.1 hW hPW hloc hnW
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap ℤ (regRing P))
    Algebra.IsIntegral.isIntegral _
    (_root_.IsPrime.to_maximal_ideal fun h => hn0 (by rw [h] at hn; exact hn))

theorem RegularityMaximalSpectrum.proof (hO : RegularityOrder.Statement)
    (hZ : RegularityLocalize.Statement) (hI : LocRingInj.Statement) (hS : RegularityMaximalSurjective.Statement) :
    RegularityMaximalSpectrum.Statement := by
  classical
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof
  intro K _ ι _ P hP
  have hPp : P.IsPrime := hP.2.1.1
  have hloc : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, IsLocalRing (locRing P W.1) :=
    fun W => (hL K ι P W.1 hPp W.2.1.1.1 W.2.2).1
  let m : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → Ideal (regRing P) := fun W =>
    regMaxAt P W.1 W.2.1 W.2.2 (hloc W)
  have hm : ∀ W (x : regRing P), x ∉ m W ↔
      ∃ z ∈ locRing P W.1, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 :=
    fun W => not_mem_regMaxAt_iff W.2.1 W.2.2 (hloc W)

  have hsub : ∀ W W', m W = m W' → locRing P W.1 ≤ locRing P W'.1 := by
    intro W W' hWW' y hy
    obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    obtain ⟨z, hz, hsz⟩ := (hm W' s).1 (hWW' ▸ (hm W s).2 hsu)
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W'.2.1 W'.2.2 x) hz
  let f : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → MaximalSpectrum (regRing P) := fun W =>
    ⟨m W, regMaxAt_isMaximal hO hL hP W.2.1 W.2.2 (hloc W)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun W W' h => Subtype.ext (hI K ι P W.1 W'.1 hPp W.2.1.1 W'.2.1.1 W.2.2 W'.2.2
      (le_antisymm (hsub W W' (congrArg MaximalSpectrum.asIdeal h))
        (hsub W' W (congrArg MaximalSpectrum.asIdeal h).symm))), ?_⟩
    rintro ⟨M, hM⟩
    obtain ⟨W, hWc, hPW, hW⟩ := hS K ι P hP M hM
    refine ⟨⟨W, hWc, hPW⟩, ?_⟩
    have hle : M ≤ m ⟨W, hWc, hPW⟩ := fun x hx => by
      by_contra hc
      obtain ⟨z, hz, h⟩ := (hm _ x).1 hc
      exact hW x hx z hz h
    exact MaximalSpectrum.ext (hM.eq_of_le (regMaxAt_isMaximal hO hL hP hWc hPW _).ne_top hle).symm
  refine ⟨Equiv.ofBijective f hbij, fun W y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    exact ⟨x, s, (hm W s).2 hsu, hys⟩
  · rintro ⟨x, s, hs, hys⟩
    obtain ⟨z, hz, hsz⟩ := (hm W s).1 hs
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W.2.1 W.2.2 x) hz

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem semiLocRing_le_empty {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (𝒲 : Set (Ideal (MRing ι))) : semiLocRing P 𝒲 ≤ semiLocRing P ∅ := by
  unfold semiLocRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, fun _ h => h.elim, hu, hwa, rfl⟩

theorem SemilocFinite.proof (h₁ : SemilocIntegral.Statement) (h₂ : LocRingIntClosureFinite.Statement)
    (h₃ : LocRingDimOne.Statement) : SemilocFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW
  have := hP'.2.1.1
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hN : IsNoetherianRing (locRing (imageZ v P') W) := (h₃ K ι (imageZ v P') s α W hQ.2.1 hs hsQ hW).1
  have hint := h₁ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
  refine ⟨?_, ?_⟩
  · let _ := ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype).toAlgebra
    let _ : Module (locRing (imageZ v P') W) (FractionRing (MRing ι' ⧸ P')) := Algebra.toModule
    obtain ⟨t, ht⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW
    let g : semiLocRing P' (fibreOver v P' W) →ₗ[locRing (imageZ v P') W] FractionRing (MRing ι' ⧸ P') :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : ∀ b, g b ∈ Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P'))) :=
      fun b => ht _ (semiLocRing_le_empty P' _ b.2)
        ((hint.isIntegral b).map_of_comp_eq (RingHom.id (locRing (imageZ v P') W)) (semiLocRing P' (fibreOver v P' W)).subtype
          (RingHom.ext fun _ => rfl))
    have : IsNoetherian (locRing (imageZ v P') W)
        (Submodule.span (locRing (imageZ v P') W) (t : Set (FractionRing (MRing ι' ⧸ P')))) :=
      isNoetherian_span_of_finite _ t.finite_toSet
    exact Module.Finite.of_injective (g.codRestrict _ hg)
      fun b c hbc => by
        have h := congrArg Subtype.val hbc
        exact Subtype.ext h
  · have := imageZ_isPrime_of_prime v P'
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro a b hab
    exact Subtype.val_injective ((fracMapZ v P').injective (congrArg Subtype.val hab))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocRankAdjoin.chart_congr {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by
  subst h
  rfl

theorem SemilocRankAdjoin.isMultiHomogIdeal_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℚ) : MRing ι →+* MRingOver ℚ ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, fun m hm => ha m (MvPolynomial.support_map_subset _ _ hm)⟩

theorem SemilocRankAdjoin.chain (hT : ChartScalingIndep.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') (i' : ∀ k', ι' k')
    (F : Type) [Field F] [Algebra F G.Φ] [Algebra F G.Φ'] [IsScalarTower F G.Φ G.Φ'] (hv : IsBlockMap κ v)
    (hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0)
    (hmh : IsMultiHomogIdeal (RingHom.ker (aeval G.x' : MRingOver F ι' →ₐ[F] G.Φ'))) :
    IntermediateField.relfinrank
        (IntermediateField.adjoin F (Set.range ((fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin F (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩)) =
      Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩)) := by
  let y' : (Σ k', ι' k') → G.Φ' := fun q => G.x' q / G.x' ⟨q.1, i' q.1⟩
  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom F G.Φ G.Φ').fieldRange
  let L₀ := IntermediateField.adjoin F (Set.range (y' ∘ v))
  let L := IntermediateField.adjoin F (Set.range y')
  let E := IntermediateField.adjoin F (Set.range t)
  have mono : ∀ {A B : Set G.Φ'}, A ⊆ B → IntermediateField.adjoin F A ≤ IntermediateField.adjoin F B :=
    fun h => IntermediateField.adjoin_le_iff.2 (h.trans (IntermediateField.subset_adjoin _ _))
  have hchart : ∀ q : Σ k, ι k, G.x' ⟨(v q).1, i' (v q).1⟩ = t q.1 :=
    fun q => SemilocRankAdjoin.chart_congr G.x' i' (hv.2.2.1 q)
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hyv : ∀ q, y' (v q) ∈ Φ₁ := fun q => by
    show G.x' (v q) / G.x' ⟨(v q).1, i' (v q).1⟩ ∈ Φ₁
    rw [hchart, G.compat]
    exact div_mem (hmem _) (ht1 q.1)
  have hL₀E : L₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨q, rfl⟩
      exact hyv q
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ L₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          have hq : G.x' (v q) = y' (v q) * t q.1 := by
            show _ = G.x' (v q) / G.x' ⟨(v q).1, i' (v q).1⟩ * t q.1
            rw [hchart, div_mul_cancel₀ _ (hx (κ q.1))]
          rw [hq]
          exact mul_mem ((le_sup_left : L₀ ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩))
            ((le_sup_right : E ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom F G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ L₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)
  have hLE : L ⊔ E = Φ₁ ⊔ IntermediateField.adjoin F
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i' q.1.1⟩) := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_)
      (((le_sup_right : E ≤ L₀ ⊔ E).trans hL₀E.le).trans le_sup_left)) (sup_le ?_ ?_)
    · rintro _ ⟨q, rfl⟩
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hv.2.2.2 q hq
        exact (le_sup_left : Φ₁ ≤ _) (hyv r)
      · exact (le_sup_right : IntermediateField.adjoin _ _ ≤ _)
          (IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩)
    · rw [← hL₀E]
      exact sup_le_sup_right (mono (Set.range_comp_subset_range v y')) E
    · refine (mono ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact ⟨⟨q.1.1, q.2⟩, rfl⟩
  have hindep : AlgebraicIndependent L t := (hT F G.Φ' K' ι' G.x' i' hx hmh).comp κ hv.1
  rw [← AdjoinIndepRelfinrank.proof F G.Φ' L₀ L K t (mono (Set.range_comp_subset_range v y')) hindep,
    FinrankAdjoinRange.proof F G.Φ G.Φ']
  change IntermediateField.relfinrank (L₀ ⊔ E) (L ⊔ E) = _
  rw [hL₀E, hLE]

theorem SemilocRankAdjoin.proof (hF : SemilocRankFrac.Statement) (hT : ChartScalingIndep.Statement) :
    SemilocRankAdjoin.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G s α W i' hv hP' hZ hs hsP hW hi'

  have hker : ∀ f : MRing ι', aeval G.x' f = 0 ↔ f ∈ P' := fun f => by rw [← RingHom.mem_ker, G.genericFibre_ker_target]
  have : CharZero G.Φ' := charZero_of_inj_zero fun m hm => by
    have h : (C (m : ℤ) : MRing ι') ∈ P' := (hker _).1 (by rw [aeval_C]; exact_mod_cast hm)
    have h' : (m : ℤ) ∈ P'.comap (C : ℤ →+* MRing ι') := h
    rw [hP'.2.2.1, Ideal.mem_bot] at h'
    exact_mod_cast h'
  have : CharZero G.Φ := (RingHom.charZero_iff (algebraMap G.Φ G.Φ').injective).2 inferInstance
  have : IsScalarTower ℚ G.Φ G.Φ' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

  have hkerQ : RingHom.ker (aeval G.x' : MRingOver ℚ ι' →ₐ[ℚ] G.Φ') =
      P'.map (MvPolynomial.map (Int.castRingHom ℚ) : MRing ι' →+* MRingOver ℚ ι') := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k', ι' k') (R := ℤ) (S := ℚ)
    have _ : IsLocalization ((nonZeroDivisors ℤ).map (C (σ := Σ k', ι' k') (R := ℤ))) (MRingOver ℚ ι') :=
      MvPolynomial.isLocalization _ _
    refine (IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k', ι' k') (R := ℤ))) (MRingOver ℚ ι')
      (RingHom.ker (aeval G.x' : MRingOver ℚ ι' →ₐ[ℚ] G.Φ'))).symm.trans ?_
    congr 1
    ext f
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_def, aeval_map_algebraMap, hker]
  have hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hi' k' ((hker _).1 (by rw [aeval_X, h]))
  rw [hF K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi',
    SemilocRankAdjoin.chain hT G i' ℚ hv hx (hkerQ ▸ SemilocRankAdjoin.isMultiHomogIdeal_map hP'.2.1.2.1)]

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocRank.proof (hDim : FibreDimStatement) (hAdj : SemilocRankAdjoin.Statement) :
    SemilocRank.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W hv hP' hZ hJ hs hsP hW
  have hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ P' := hP'.2.1.2.2
  choose i' hi' using hrel
  have hfib : IsProjVarF (fibreIdeal κ G) 0 := hDim K ι K' ι' κ v P' (n + 1) 0 G hv hP' hZ
  have hz : ∀ k : FibreBlock κ, G.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hi' k.1
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h0
  have hj : IsChart (fibreIdeal κ G) (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  rw [hJ.1 _ Fin.elim0 _ hfib hj, hAdj K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi']
  congr 1
  exact (ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩)
    (fun k => i' k.1) hz hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
end
end
