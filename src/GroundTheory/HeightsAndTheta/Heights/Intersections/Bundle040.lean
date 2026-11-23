module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsLocalizationConeVarMap
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle039
public import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Lie.OfAssociative
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section



theorem regularityLocalFlat_holds.proof : regularityLocalFlat_holds.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP.1
  have := hW.1
  choose v hv using hW.2.2
  have hA := regularityLocalFlat_holds.isLocalRing (P := P) (W := W) hPW
  have hloc := regularityLocalFlat_holds.isLocalization_coneVarMap hPW hP.2.1 hW.2.1 v hv
  let _ := (regularityLocalFlat_holds.coneVarMap P W hPW v).toRingHom.toAlgebra
  have := regularityLocalFlat_holds.isPrime_map_C K (maximalIdeal (locRing P W))
  have : IsScalarTower (locRing P W) (MvPolynomial K (locRing P W)) (coneLocRing P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((regularityLocalFlat_holds.coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocRing P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocRing P W hPW)
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocRing P W hPW)
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _)).primeCompl
    have : Module.Free (locRing P W) (MvPolynomial K (locRing P W)) :=
      Module.Free.of_basis (MvPolynomial.basisMonomials K (locRing P W))
    have : Module.Flat (locRing P W) (MvPolynomial K (locRing P W)) := Module.Flat.of_free
    exact Module.Flat.trans _ (MvPolynomial K (locRing P W)) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))
      (coneLocRing P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VerticalDegreeAfterAdjoining.chart_congr {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by
  subst h
  rfl

theorem VerticalDegreeAfterAdjoining.proof (hA : RankAdjoinFrac.Statement) (hB : FnDegAdjoin.Statement)
    (hT : ChartScalingIndep.Statement) (hC : AdjoinIndepRelfinrank.Statement)
    (hD : FinrankAdjoinRange.Statement) : VerticalDegreeAfterAdjoining.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n i' hv hp hW _ hc G'

  have hpΩ : ((p : ℕ) : G'.Φ') = 0 := by
    have h : ((p : ℕ) : MRing ι') ∈ RingHom.ker (aeval G'.x' : MRing ι' →ₐ[ℤ] G'.Φ') := G'.genericFibre_ker_target.symm ▸ hp
    rwa [RingHom.mem_ker, map_natCast] at h
  have : CharP G'.Φ' p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpΩ
  have : CharP G'.Φ p := ((algebraMap G'.Φ G'.Φ').charP_iff_charP p).2 inferInstance
  let : Algebra (ZMod p) G'.Φ' := ZMod.algebra _ p
  let : Algebra (ZMod p) G'.Φ := ZMod.algebra _ p
  have : IsScalarTower (ZMod p) G'.Φ G'.Φ' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)

  have hker : RingHom.ker (aeval G'.x' : MRingOver (ZMod p) ι' →ₐ[ZMod p] G'.Φ') =
      W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))) := by
    ext g
    obtain ⟨f, rfl⟩ := PointVertical.red_surjective (ι := ι') p g
    have e : aeval G'.x' (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = aeval G'.x' f := by
      rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
    rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, e, ← RingHom.mem_ker, G'.genericFibre_ker_target]
  rw [← hker] at hW hc ⊢
  have hx : ∀ k', G'.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hc k' (by rw [RingHom.mem_ker, aeval_X, h])
  have hmh := hW.1.2.1

  let y' : (Σ k', ι' k') → G'.Φ' := fun q => G'.x' q / G'.x' ⟨q.1, i' q.1⟩
  let t : K → G'.Φ' := fun k => G'.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom (ZMod p) G'.Φ G'.Φ').fieldRange
  let L₀ := IntermediateField.adjoin (ZMod p) (Set.range (y' ∘ v))
  let L := IntermediateField.adjoin (ZMod p) (Set.range y')
  let E := IntermediateField.adjoin (ZMod p) (Set.range t)
  have mono : ∀ {A B : Set G'.Φ'}, A ⊆ B → IntermediateField.adjoin (ZMod p) A ≤ IntermediateField.adjoin (ZMod p) B :=
    fun h => IntermediateField.adjoin_le_iff.2 (h.trans (IntermediateField.subset_adjoin _ _))
  have hchart : ∀ q : Σ k, ι k, G'.x' ⟨(v q).1, i' (v q).1⟩ = t q.1 :=
    fun q => VerticalDegreeAfterAdjoining.chart_congr G'.x' i' (hv.2.2.1 q)
  have hmem : ∀ c, algebraMap G'.Φ G'.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    show G'.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G'.compat]
    exact hmem _
  have hyv : ∀ q, y' (v q) ∈ Φ₁ := fun q => by
    show G'.x' (v q) / G'.x' ⟨(v q).1, i' (v q).1⟩ ∈ Φ₁
    rw [hchart, G'.compat]
    exact div_mem (hmem _) (ht1 q.1)
  have hL₀E : L₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨q, rfl⟩
      exact hyv q
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G'.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G'.Φ G'.Φ' (aeval G'.x f) ∈ L₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G'.compat]
          refine mul_mem hf ?_
          have hq : G'.x' (v q) = y' (v q) * t q.1 := by
            show _ = G'.x' (v q) / G'.x' ⟨(v q).1, i' (v q).1⟩ * t q.1
            rw [hchart, div_mul_cancel₀ _ (hx (κ q.1))]
          rw [hq]
          exact mul_mem ((le_sup_left : L₀ ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩))
            ((le_sup_right : E ≤ L₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom (ZMod p) G'.Φ G'.Φ' (aeval G'.x f / aeval G'.x g) ∈ L₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)
  have hLE : L ⊔ E = Φ₁ ⊔ IntermediateField.adjoin (ZMod p)
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩) := by
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

  have hindep : AlgebraicIndependent L t := (hT (ZMod p) G'.Φ' K' ι' G'.x' i' hx hmh).comp κ hv.1
  refine Eq.trans (hB (ZMod p) G'.Φ' K ι K' ι' v G'.x' i' hx hmh)
    (Eq.trans (hA (ZMod p) G'.Φ' _ _ (Set.range_comp_subset_range v y')) ?_)
  rw [← hC (ZMod p) G'.Φ' L₀ L K t (mono (Set.range_comp_subset_range v y')) hindep, hD (ZMod p) G'.Φ G'.Φ']
  change IntermediateField.relfinrank (L₀ ⊔ E) (L ⊔ E) = _
  rw [hL₀E, hLE]

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreTranscendence

theorem aeval_red {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) :
    aeval y (MvPolynomial.map (Int.castRingHom (ZMod p)) g) = aeval y g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f i hf => simp only [map_mul, hf, map_X, aeval_X]

theorem aeval_mem_adjoin {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) : aeval y g ∈ IntermediateField.adjoin (ZMod p) (Set.range y) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf =>
    simpa using mul_mem hf (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

variable {K : Type} {ι : K → Type}

theorem ker_aeval_F {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] (y : (Σ k, ι k) → L)
    {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) :
    RingHom.ker (aeval y : MRingOver (ZMod p) ι →ₐ[ZMod p] L) = J.map (PointVertical.red (ι := ι) p) := by
  ext f
  obtain ⟨g, rfl⟩ := PointVertical.red_surjective (ι := ι) p f
  rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, ← hJ, RingHom.mem_ker]
  exact iff_of_eq (congrArg (· = 0) (aeval_red p y g))

theorem trdeg_adjoin [Fintype K] [∀ k, Fintype (ι k)] (hE : EvalKerKrullDim.Statement) {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L]
    (y : (Σ k, ι k) → L) {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J)
    (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) {n : ℕ} (hV : IsProjVarF (J.map (PointVertical.red (ι := ι) p)) n) :
    Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y)) = ((n + Fintype.card K : ℕ) : Cardinal) := by
  have h := hE K ι (ZMod p) L y
  rw [ker_aeval_F p y hp hJ, hV.2] at h
  have h' : (Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y))).toENat =
      ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h.symm
  exact Cardinal.toENat_eq_natCast.mp h'

end FibreTranscendence


open FibreTranscendence in
theorem FibreTranscendenceDegreeAlt.proof (hE : EvalKerKrullDim.Statement) : FibreTranscendenceDegreeAlt.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  classical
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W' := by
    show rename v ((p : ℕ) : MRing ι) ∈ W'
    simpa using hp
  have hΦp : ((p : ℕ) : G'.Φ) = 0 := by
    have h := hpI
    rw [← G'.ker_x, RingHom.mem_ker] at h
    simpa using h
  have hΦ'p : ((p : ℕ) : G'.Φ') = 0 := by
    have h := hp
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker] at h
    simpa using h
  have : CharP G'.Φ p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hΦp
  have : CharP G'.Φ' p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hΦ'p
  let _ : Algebra (ZMod p) G'.Φ := ZMod.algebra _ p
  let _ : Algebra (ZMod p) G'.Φ' := ZMod.algebra _ p
  have : IsScalarTower (ZMod p) G'.Φ G'.Φ' := IsScalarTower.of_algebraMap_eq fun a =>
    DFunLike.congr_fun (Subsingleton.elim (algebraMap (ZMod p) G'.Φ')
      ((algebraMap G'.Φ G'.Φ').comp (algebraMap (ZMod p) G'.Φ))) a

  have hx := trdeg_adjoin hE p G'.x hpI G'.ker_x
    (by rw [← PointVertical.imageVar_red p v hp]; exact hV)
  have htop : IntermediateField.adjoin (ZMod p) (Set.range G'.x) = ⊤ := by
    refine eq_top_iff.2 fun c _ => ?_
    obtain ⟨f, g, -, rfl⟩ := G'.gen c
    exact div_mem (aeval_mem_adjoin p _ f) (aeval_mem_adjoin p _ g)
  have hΦ : Algebra.trdeg (ZMod p) G'.Φ = ((n + Fintype.card K : ℕ) : Cardinal) := by
    rw [← hx, htop, IntermediateField.topEquiv.trdeg_eq]

  set E := IntermediateField.adjoin G'.Φ
    (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G'.x' ⟨q.1.1, q.2⟩) with hEdef
  have hEeq : E.restrictScalars (ZMod p) = IntermediateField.adjoin (ZMod p) (Set.range G'.x') := by
    refine le_antisymm (fun c hc => ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · have hle : E.toSubfield ≤ (IntermediateField.adjoin (ZMod p) (Set.range G'.x')).toSubfield := by
        rw [hEdef, IntermediateField.adjoin_toSubfield]
        refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
        · rintro _ ⟨c, rfl⟩
          obtain ⟨f, g, -, rfl⟩ := G'.gen c
          have key : ∀ f : MRing ι, algebraMap G'.Φ G'.Φ' (aeval G'.x f) = aeval G'.x' (rename v f) := by
            intro f
            induction f using MvPolynomial.induction_on with
            | C a => simp
            | add f g hf hg => simp only [map_add (f := _), hf, hg]
            | mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G'.compat]
          rw [map_div₀, key, key]
          exact div_mem (aeval_mem_adjoin p _ _) (aeval_mem_adjoin p _ _)
        · rintro _ ⟨q, rfl⟩
          exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      exact hle hc
    · rintro _ ⟨q, rfl⟩
      show G'.x' q ∈ E
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨q0, rfl⟩ := hv.2.2.2 q hq
        rw [G'.compat]
        exact E.algebraMap_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩
  have hEt : Algebra.trdeg (ZMod p) E = ((n + Fintype.card K' : ℕ) : Cardinal) := by
    rw [← trdeg_adjoin hE p G'.x' hp G'.genericFibre_ker_target hW, ← hEeq]
    rfl

  have hadd := trdeg_add_eq (ZMod p) G'.Φ (A := E)
  rw [hΦ, hEt] at hadd
  have hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K' := by
    simp only [← Nat.card_eq_fintype_card]
    have h1 := Set.ncard_add_ncard_compl (Set.range κ)
    rw [Set.ncard_range_of_injective hv.1, add_comm] at h1
    exact h1
  have hlt : Algebra.trdeg G'.Φ E < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (le_add_self.trans_eq hadd) Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hm] at hadd ⊢
  have : n + Fintype.card K + m = n + Fintype.card K' := by exact_mod_cast hadd
  exact_mod_cast (by omega : m = Fintype.card (FibreBlock κ))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace FibreMultiHomogeneous

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

theorem component_map {σ R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S) (w : σ → ℕ) (n : ℕ)
    (F : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (map g F) = map g (weightedHomogeneousComponent w n F) := by
  ext m
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem component_mem [Fintype K'] [∀ k, Fintype (ι' k)] {p : ℕ} {W' : Ideal (MRing ι')} (hp : ((p : ℕ) : MRing ι') ∈ W')
    (hW : IsMultiHomogIdeal (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) [DecidableEq K'] (k : K')
    (n : ℕ) {g : MRing ι'} (hg : g ∈ W') : weightedHomogeneousComponent (cycBlockWt k) n g ∈ W' := by
  rw [← PointVertical.mem_map_red_iff p hp, PointVertical.red, ← component_map]
  exact weightedHomogeneousComponent_mem_of_mem _ _ (cyc_isHomogeneous_of_isMultiHomogIdeal hW k)
    ((PointVertical.mem_map_red_iff p hp g).2 hg) n

theorem exists_clear [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W') {τ : Type*}
    (f : MvPolynomial τ G.Φ) : ∃ b : MRing ι, aeval G.x b ≠ 0 ∧
      ∃ F : MvPolynomial τ (MRing ι), C (aeval G.x b) * f = map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F := by
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    obtain ⟨a, b, hb, rfl⟩ := G.gen c
    refine ⟨b, hb, monomial m a, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    field_simp
  | add f g hf hg =>
    obtain ⟨b₁, hb₁, F₁, e₁⟩ := hf
    obtain ⟨b₂, hb₂, F₂, e₂⟩ := hg
    refine ⟨b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, C b₂ * F₁ + C b₁ * F₂, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e₁, ← e₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring

def liftZ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) →+* MRing ι' :=
  eval₂Hom (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom fun q => X ⟨q.1.1, q.2⟩

theorem aeval_liftZ [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W')
    (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    aeval G.x' (liftZ κ v F) = aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)
      (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F) := by
  have h : (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom.comp (liftZ κ v) =
      (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)).toRingHom.comp
        (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · have e : G.x' ∘ v = algebraMap G.Φ G.Φ' ∘ G.x := funext G.compat
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftZ, coe_eval₂Hom, eval₂_C,
        MvPolynomial.map_C, aeval_C]
      rw [aeval_rename, e, aeval_algebraMap_apply]
    · simp [liftZ]
  exact DFunLike.congr_fun h F

theorem liftZ_component [Fintype K'] [∀ k, Fintype (ι' k)] [DecidableEq K'] {κ : K → K'} [DecidableEq (FibreBlock κ)] {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) (k : FibreBlock κ) (n : ℕ) (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) =
      liftZ κ v (weightedHomogeneousComponent (cycBlockWt k) n F) := by
  induction F using MvPolynomial.induction_on' with
  | add F G hF hG => simp only [map_add (f := _), hF, hG]
  | monomial m a =>
    have hj : ∀ q : Σ k : FibreBlock κ, ι' k.1,
        cycBlockWt (ι := ι') k.1 ⟨q.1.1, q.2⟩ = cycBlockWt (ι := fun k : FibreBlock κ => ι' k.1) k q := by
      intro q
      simp only [cycBlockWt, Subtype.ext_iff]
    have h0 : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1) (rename v a) 0 := by
      intro d hd
      obtain ⟨u, rfl, -⟩ : ∃ u, u.mapDomain v = d ∧ AddMonoidAlgebra.coeff a u ≠ 0 := by
        by_contra! h
        exact hd (coeff_rename_eq_zero _ _ _ h)
      rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
      refine Finset.sum_eq_zero fun q _ => ?_
      have : (v q).1 ≠ k.1 := fun h => k.2 ⟨q.1, by rw [← hv.2.2.1 q, h]⟩
      simp [cycBlockWt, this]
    have h1 : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1)
        (m.prod fun q e => (X ⟨q.1.1, q.2⟩ : MRing ι') ^ e) (Finsupp.weight (cycBlockWt k) m) := by
      rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
      convert IsWeightedHomogeneous.prod m.support (fun q => (X ⟨q.1.1, q.2⟩ : MRing ι') ^ m q)
        (fun q => m q • cycBlockWt (ι := ι') k.1 ⟨q.1.1, q.2⟩)
        (fun q _ => (isWeightedHomogeneous_X ℤ _ _).pow (m q)) using 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hj]
    have hw : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1) (liftZ κ v (monomial m a))
        (Finsupp.weight (cycBlockWt k) m) := by
      have := h0.mul h1
      rw [zero_add] at this
      simpa [liftZ, eval₂_monomial] using this
    by_cases h : Finsupp.weight (cycBlockWt k) m = n
    · subst h
      rw [hw.weightedHomogeneousComponent_same,
        (isWeightedHomogeneous_monomial _ _ _ rfl).weightedHomogeneousComponent_same]
    · rw [hw.weightedHomogeneousComponent_ne _ (Ne.symm h),
        (isWeightedHomogeneous_monomial _ _ _ rfl).weightedHomogeneousComponent_ne _ (Ne.symm h), map_zero]

end FibreMultiHomogeneous


open FibreMultiHomogeneous in
theorem ArithmeticIntersectionFibreMultiHomogeneous.proof : ArithmeticIntersectionFibreMultiHomogeneous.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' hv hp hW G'
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_
  rw [show (DirectSum.decompose (weightedHomogeneousSubmodule G'.Φ (cycBlockWt k)) f n : MvPolynomial _ G'.Φ) =
    weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]
  obtain ⟨b, hb, F, e⟩ := exists_clear G' f
  rw [fibreIdeal, RingHom.mem_ker] at hf ⊢
  have hF : liftZ κ v F ∈ W' := by
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]
    simp [hf]
  have hc := component_mem hp hW k.1 n hF
  rw [liftZ_component hv, ← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e,
    weightedHomogeneousComponent_C_mul, map_mul, aeval_C] at hc
  exact (mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)

end GroundTheory.Heights₂.Heights.Inter
end
end
