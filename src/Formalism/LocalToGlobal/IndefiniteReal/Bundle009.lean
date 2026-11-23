module

public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
public import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsStrictHenselianAbsolutelyClosedLocalRing
public import Formalism.LocalToGlobal.IndefiniteReal.FinrankIntSelf
public import Formalism.LocalToGlobal.IndefiniteReal.OpNormAtLeOfPoints
import Formalism.LocalToGlobal.IndefiniteReal.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory IsDedekindDomain NumberField Topology
open scoped RestrictedProduct Classical

namespace Formalism.IndefR.PHeisFC

variable (F : Type) [Field F] [NumberField F]

abbrev eM : InfiniteAdeleRing F ≃+* mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem eM_apply (x : InfiniteAdeleRing F) :
    eM F x = ((fun v : {w : InfinitePlace F // w.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)),
      fun v : {w : InfinitePlace F // w.IsComplex} => InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) :=
  InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x

def Pinf : Set (InfiniteAdeleRing F) := eM F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem eM_algebraMap (a : F) : eM F (algebraMap F (InfiniteAdeleRing F) a) = mixedEmbedding F a := by
  first
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp).symm
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
  | exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (x := a)).symm

theorem inf_exU (x : InfiniteAdeleRing F) : ∃! a : 𝓞 F, algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F := by
  have key : ∀ a : 𝓞 F, (algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F) ↔
      mixedEmbedding F (a : F) + eM F x ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) := by
    intro a
    show eM F (algebraMap F (InfiniteAdeleRing F) (a : F) + x) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) ↔ _
    rw [map_add (f := _), eM_algebraMap]
  have hmem : ∀ a : 𝓞 F, mixedEmbedding F (a : F) ∈
      Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := by
    intro a
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨a, rfl⟩
  obtain ⟨v, hv, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F) (eM F x)
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 F, mixedEmbedding F (a : F) = (v : mixedEmbedding.mixedSpace F) := by
    have hv2 := v.2
    rw [mixedEmbedding.mem_span_latticeBasis] at hv2
    obtain ⟨a, ha⟩ := hv2
    exact ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩
  · show algebraMap F (InfiniteAdeleRing F) (a : F) + x ∈ Pinf F
    rw [key, ha]
    simpa [Submodule.vadd_def] using hv
  · intro b hb0
    have hb : algebraMap F (InfiniteAdeleRing F) (b : F) + x ∈ Pinf F := hb0
    rw [key] at hb
    have h1 : (⟨mixedEmbedding F (b : F), hmem b⟩ :
        Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) = v := by
      apply hu
      simpa [Submodule.vadd_def] using hb
    have h2 : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      exact congrArg Subtype.val h1
    have h3 : (b : F) = (a : F) := mixedEmbedding_injective F h2
    first | exact RingOfIntegers.ext h3 | exact RingOfIntegers.coe_injective h3 | exact Subtype.ext h3

theorem measurableSet_Pinf : MeasurableSet (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem Pinf_sub_compact : ∃ K : Set (InfiniteAdeleRing F), IsCompact K ∧ Pinf F ⊆ K := by
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).subset_closedBall 0
  refine ⟨Set.pi Set.univ (fun w => (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R),
    ?_, ?_⟩
  · refine isCompact_univ_pi fun w => ?_
    have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
    first
    | exact hi.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)
    | exact hi.closedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)
  · intro x hx
    have hx' : ‖eM F x‖ ≤ R := mem_closedBall_zero_iff.mp (hR (show eM F x ∈ _ from hx))
    show ∀ w ∈ (Set.univ : Set (InfinitePlace F)),
      x w ∈ (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R
    intro w _
    have hn : ‖InfinitePlace.Completion.extensionEmbedding w (x w)‖ = ‖x w‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x w)
    show InfinitePlace.Completion.extensionEmbedding w (x w) ∈ Metric.closedBall 0 R
    rw [mem_closedBall_zero_iff, hn]
    by_cases hw : w.IsReal
    · have hr : ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w)‖ = ‖x w‖ :=
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) (x w)
      have e : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x w) = (eM F x).1 ⟨w, hw⟩ := by
        rw [eM_apply]
      rw [← hr, e]
      exact ((norm_le_pi_norm _ _).trans (norm_fst_le _)).trans hx'
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have e : InfinitePlace.Completion.extensionEmbedding w (x w) = (eM F x).2 ⟨w, hc⟩ := by
        rw [eM_apply]
      rw [← hn, e]
      exact ((norm_le_pi_norm _ _).trans (norm_snd_le _)).trans hx'

abbrev Ohat : Set (FiniteAdeleRing (𝓞 F) F) := (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F : Set (FiniteAdeleRing (𝓞 F) F))

theorem isOpen_Ohat : IsOpen (Ohat F) := by
  first | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd F | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd

theorem isCompact_Ohat : IsCompact (Ohat F) := Formalism.L2.Col.rlt_isCompact_intAd

def F0 : Set (AdeleRing (𝓞 F) F) := {x | x.1 ∈ Pinf F ∧ x.2 ∈ Ohat F}

theorem ad_exU (x : AdeleRing (𝓞 F) F) : ∃! q : F, algebraMap F (AdeleRing (𝓞 F) F) q + x ∈ F0 F := by
  have hOa : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
    intro a
    show ∀ v : HeightOneSpectrum (𝓞 F), (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v ∈ v.adicCompletionIntegers F
    intro v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v = ((a : F) : v.adicCompletion F) := rfl
    rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    first
    | exact HeightOneSpectrum.valuation_le_one v a
    | (rw [show (a : F) = algebraMap (𝓞 F) F a from rfl, HeightOneSpectrum.valuation_of_algebraMap];
       exact HeightOneSpectrum.intValuation_le_one v a)
  have hint : ∀ q : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) q ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F →
      ∃ a : 𝓞 F, (a : F) = q := by
    intro q hq
    have hr := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) q (by
      intro v
      have h1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) q) v ∈ v.adicCompletionIntegers F := hq v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      have h2 : Valued.v ((q : v.adicCompletion F)) ≤ 1 := h1
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2)
    obtain ⟨a, ha⟩ := hr
    first | exact ⟨a, ha⟩ | exact ⟨a, by simpa using ha⟩
  obtain ⟨u, hu⟩ : ∃ u : F, x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd F x.2
    | exact Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨a, ha, hauniq⟩ := inf_exU F (algebraMap F (InfiniteAdeleRing F) (-u) + x.1)
  refine ⟨-u + (a : F), ?_, ?_⟩
  · simp only [F0, Set.mem_setOf_eq]
    constructor
    · change algebraMap F (InfiniteAdeleRing F) (-u + (a : F)) + x.1 ∈ Pinf F
      have e : algebraMap F (InfiniteAdeleRing F) (-u + (a : F)) + x.1 =
          algebraMap F (InfiniteAdeleRing F) (a : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) := by
        rw [map_add (f := _)]; abel
      rw [e]; exact ha
    · change algebraMap F (FiniteAdeleRing (𝓞 F) F) (-u + (a : F)) + x.2 ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) (-u + (a : F)) + x.2 =
          (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u) + algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) := by
        rw [map_add (f := _), map_neg]; abel
      rw [e]; exact add_mem hu (hOa a)
  · intro q hq
    simp only [F0, Set.mem_setOf_eq] at hq
    obtain ⟨h1, h2⟩ := hq
    have h2' : algebraMap F (FiniteAdeleRing (𝓞 F) F) q + x.2 ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := h2
    have h1' : algebraMap F (InfiniteAdeleRing F) q + x.1 ∈ Pinf F := h1
    have h3 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (q + u) ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F := by
      have h4 := sub_mem h2' hu
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) (q + u) =
          algebraMap F (FiniteAdeleRing (𝓞 F) F) q + x.2 - (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) u) := by
        rw [map_add (f := _)]; abel
      rw [e]; exact h4
    obtain ⟨b, hb⟩ := hint (q + u) h3
    have h5 : algebraMap F (InfiniteAdeleRing F) (b : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) ∈ Pinf F := by
      have e : algebraMap F (InfiniteAdeleRing F) (b : F) + (algebraMap F (InfiniteAdeleRing F) (-u) + x.1) =
          algebraMap F (InfiniteAdeleRing F) q + x.1 := by
        rw [hb, map_add (f := _), map_neg]; abel
      rw [e]; exact h1'
    have hba : b = a := hauniq b h5
    rw [hba] at hb
    rw [hb]; ring

theorem fundamental_set_subset_compact : ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ F0 F ⊆ K := by
  obtain ⟨K1, hK1, hsub⟩ := Pinf_sub_compact F
  refine ⟨K1 ×ˢ Ohat F, hK1.prod (isCompact_Ohat F), ?_⟩
  intro x hx
  simp only [F0, Set.mem_setOf_eq] at hx
  exact ⟨hsub hx.1, hx.2⟩

instance instT2SpaceFiniteAdeles : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ (v : HeightOneSpectrum (𝓞 F)), [v.adicCompletion F, v.adicCompletionIntegers F]))

instance t2Space_numberFieldInfiniteAdeles : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

instance t2AF : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

instance wlcAfin : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) where
  exists_compact_mem_nhds x := by
    refine ⟨(fun y => x + y) '' Ohat F, (isCompact_Ohat F).image (continuous_const.add continuous_id), ?_⟩
    have ho : IsOpen ((fun y => y - x) ⁻¹' Ohat F) := (isOpen_Ohat F).preimage (continuous_id.sub continuous_const)
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · show x - x ∈ Ohat F
      rw [sub_self]; exact zero_mem (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd F)
    · intro y hy
      exact ⟨y - x, hy, by simp⟩

instance lcAfin : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := WeaklyLocallyCompactSpace.locallyCompactSpace

instance lcAF : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Formalism.IndefR.PHeisFC

end
end

section

namespace Formalism.IndefR.LatticeTransfer

theorem dimSq : DimSq := dimSq_of schur

theorem idemP : IdemP := idemP_of charFacts

theorem core : Core := core_of charFacts keyZero schur idemP

theorem all_parts_transfer_holds : AllPartsTransfer := all_parts_transfer_of_facts idemE idemP core dimSq metric

end Formalism.IndefR.LatticeTransfer
end

section

open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.DIV Formalism.L2.Col

structure AdPts {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) {G Γ : Type} [Group G] [Group Γ]
    (ι : Γ →* G) (J : Subgroup G) where
  K1 : Subgroup G
  principal_congruence_le : K1 ≤ J
  q : G → S.D
  gl : Γ × J →* S.G
  gl_surj : Function.Surjective gl
  gl_ker : ∀ (γ : Γ) (k : J), gl (γ, k) = 1 ↔ γ = 1 ∧ (k : G) ∈ K1
  q_surj : Function.Surjective q
  q_eqv : ∀ (γ : Γ) (k : J) (x : G), q (ι γ * x * (k : G)⁻¹) = gl (γ, k) • q x
  q_fib : ∀ x x' : G, q x = q x' ↔ ∃ k1 ∈ K1, x' = x * k1

section Stab

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {J : Subgroup G}

def stabJ {y : G} (γ : stab ι J y) : J := ⟨y⁻¹ * ι (γ : Γ) * y, (mem_stab ι).1 γ.2⟩

theorem stabK_eq_inv {y : G} (γ : stab ι J y) : stabK ι γ = (stabJ γ)⁻¹ := rfl

def stabHom (y : G) : stab ι J y →* Γ × J where
  toFun γ := ((γ : Γ), stabJ γ)
  map_one' := Prod.ext rfl (Subtype.ext (by simp [stabJ]))
  map_mul' a b := Prod.ext rfl (Subtype.ext (by
    show y⁻¹ * ι ((a : Γ) * (b : Γ)) * y = (y⁻¹ * ι (a : Γ) * y) * (y⁻¹ * ι (b : Γ) * y)
    rw [map_mul]; group))

end Stab

namespace AdPts

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G} (A : AdPts S ι J)

theorem q_mul (γ : Γ) (x : G) (k : J) : A.q (ι γ * x * (k : G)) = A.gl (γ, k⁻¹) • A.q x := by
  have h := A.q_eqv γ k⁻¹ x
  simpa using h

def y (c : S.Cl) : G := Function.surjInv A.q_surj (S.outSec.rep c)

theorem q_y (c : S.Cl) : A.q (A.y c) = S.outSec.rep c := Function.surjInv_eq A.q_surj _

theorem isReps : IsReps ι J A.y := by
  intro h
  refine ⟨S.cls (A.q h), ?_, ?_⟩
  · obtain ⟨g, hg⟩ := S.outSec.exists_mv (A.q h)
    obtain ⟨⟨γ, k⟩, rfl⟩ := A.gl_surj g
    rw [← A.q_y, ← A.q_eqv] at hg
    obtain ⟨k1, hk1, e⟩ := (A.q_fib _ _).1 hg
    refine ⟨γ, k⁻¹ * ⟨k1, A.principal_congruence_le hk1⟩, e.trans ?_⟩
    simp [mul_assoc]
  · rintro c ⟨γ, k, rfl⟩
    rw [A.q_mul, S.cls_smul, A.q_y, S.outSec.spec]

def toStab (c : S.Cl) : stab ι J (A.y c) →* MulAction.stabilizer S.G (S.outSec.rep c) :=
  (A.gl.comp (stabHom (A.y c))).codRestrict _ (fun γ => by
    rw [MulAction.mem_stabilizer_iff]
    show A.gl ((γ : Γ), stabJ γ) • S.outSec.rep c = S.outSec.rep c
    rw [← A.q_y, ← A.q_eqv]
    congr 1
    show ι (γ : Γ) * A.y c * ((A.y c)⁻¹ * ι (γ : Γ) * A.y c)⁻¹ = A.y c
    group)

theorem toStab_coe (c : S.Cl) (γ : stab ι J (A.y c)) :
    ((A.toStab c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) = A.gl ((γ : Γ), stabJ γ) := rfl

theorem toStab_bij (c : S.Cl) : Function.Bijective (A.toStab c) := by
  constructor
  · refine (injective_iff_map_eq_one _).2 fun γ hγ => ?_
    have h1 : A.gl ((γ : Γ), stabJ γ) = 1 := by
      rw [← A.toStab_coe, hγ]
      rfl
    exact Subtype.ext ((A.gl_ker _ _).1 h1).1
  · intro g
    obtain ⟨⟨γ, k⟩, hg⟩ := A.gl_surj g
    have hfix : A.gl (γ, k) • S.outSec.rep c = S.outSec.rep c := by
      rw [hg]
      exact g.2
    rw [← A.q_y, ← A.q_eqv] at hfix
    obtain ⟨k1, hk1, e⟩ := (A.q_fib _ _).1 hfix.symm
    have hmem : (A.y c)⁻¹ * ι γ * A.y c = k1 * (k : G) := by
      calc (A.y c)⁻¹ * ι γ * A.y c = (A.y c)⁻¹ * (ι γ * A.y c * (k : G)⁻¹) * k := by group
        _ = k1 * (k : G) := by rw [e]; group
    have hs : γ ∈ stab ι J (A.y c) := by
      rw [mem_stab, hmem]
      exact J.mul_mem (A.principal_congruence_le hk1) k.2
    refine ⟨⟨γ, hs⟩, Subtype.ext ?_⟩
    rw [toStab_coe, ← hg]
    have hJ : (stabJ (⟨γ, hs⟩ : stab ι J (A.y c)) : J) = ⟨k1, A.principal_congruence_le hk1⟩ * k := Subtype.ext hmem
    have h1 : A.gl ((1 : Γ), (⟨k1, A.principal_congruence_le hk1⟩ : J)) = 1 := (A.gl_ker _ _).2 ⟨rfl, hk1⟩
    have e2 : ((γ, stabJ (⟨γ, hs⟩ : stab ι J (A.y c))) : Γ × J) = ((1 : Γ), (⟨k1, A.principal_congruence_le hk1⟩ : J)) * (γ, k) := by
      rw [hJ]
      exact Prod.ext (one_mul γ).symm rfl
    rw [e2, map_mul, h1, one_mul]

def stabEquiv (c : S.Cl) : stab ι J (A.y c) ≃* MulAction.stabilizer S.G (S.outSec.rep c) :=
  MulEquiv.ofBijective (A.toStab c) (A.toStab_bij c)

end AdPts

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def classPresOf {S : GSD K} {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {J : Subgroup G} (A : AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (_hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v)) :
    ClassPres ι (S.toCSD h) σ ρ J χ where
  y := A.y
  reps := A.isReps
  stabI c := (A.stabEquiv c).symm
  coef := coef
  coef_li := hli
  coef_span := hspan
  coef_pair := hpair
  coef_act := by
    intro c g x
    obtain ⟨γ, rfl⟩ := (A.stabEquiv c).surjective g
    show coef (S.ρ ((A.stabEquiv c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) x) =
      (χ (stabK ι ((A.stabEquiv c).symm (A.stabEquiv c γ))) : ℂ) • ρ (((A.stabEquiv c).symm (A.stabEquiv c γ)) : Γ) (coef x)
    rw [MulEquiv.symm_apply_apply]
    have e1 : ((A.stabEquiv c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) = A.gl ((γ : Γ), stabJ γ) := rfl
    rw [e1, hgl, Units.smul_def, stabK_eq_inv, map_inv]

namespace ClassPres

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'}
  {χ' : J' →* ℂˣ}

theorem mem_stab_transport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) (γ : Γ) : eΓ γ ∈ stab ι' J' (eG y) ↔ γ ∈ stab ι J y := by
  rw [mem_stab, mem_stab, hJ, hι]
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]

def stabTransport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) : stab ι J y ≃* stab ι' J' (eG y) where
  toFun γ := ⟨eΓ γ, (mem_stab_transport eG eΓ hι hJ y γ).2 γ.2⟩
  invFun γ' := ⟨eΓ.symm γ', (mem_stab_transport eG eΓ hι hJ y _).1 (by rw [MulEquiv.apply_symm_apply]; exact γ'.2)⟩
  left_inv γ := Subtype.ext (eΓ.symm_apply_apply _)
  right_inv γ' := Subtype.ext (eΓ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul eΓ _ _)

theorem stabK_transport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) (γ : stab ι J y) :
    ((stabK ι' (stabTransport eG eΓ hι hJ y γ) : J') : G') = eG (stabK ι γ : G) := by
  show ((eG y)⁻¹ * ι' (eΓ (γ : Γ)) * eG y)⁻¹ = eG ((y⁻¹ * ι (γ : Γ) * y)⁻¹)
  rw [hι]
  simp only [map_mul, map_inv]

def transport (P : ClassPres ι S σ ρ J χ) (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ) (hJ : J' = J.map eG.toMonoidHom)
    (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k) : ClassPres ι' S σ ρ' J' χ' :=
  have hJ' : ∀ x, x ∈ J' ↔ eG.symm x ∈ J := fun x => by subst hJ; exact Subgroup.mem_map_equiv
  { y := fun c => eG (P.y c)
    reps := by
      intro h'
      obtain ⟨c, ⟨γ, k, hk⟩, hu⟩ := P.reps (eG.symm h')
      refine ⟨c, ⟨eΓ γ, ⟨eG k, (hJ' _).2 (by rw [MulEquiv.symm_apply_apply]; exact k.2)⟩, ?_⟩, ?_⟩
      · show h' = ι' (eΓ γ) * eG (P.y c) * eG (k : G)
        rw [hι, ← map_mul, ← map_mul, ← hk, MulEquiv.apply_symm_apply]
      · rintro c' ⟨γ', k', hk'⟩
        refine hu c' ⟨eΓ.symm γ', ⟨eG.symm k', (hJ' _).1 k'.2⟩, ?_⟩
        rw [hk']
        have e : ι (eΓ.symm γ') = eG.symm (ι' γ') := by
          rw [MulEquiv.eq_symm_apply, ← hι, MulEquiv.apply_symm_apply]
        rw [e]
        simp only [map_mul, MulEquiv.symm_apply_apply]
    stabI := fun c => (P.stabI c).trans (stabTransport eG eΓ hι hJ' (P.y c))
    coef := P.coef
    coef_li := P.coef_li
    coef_span := P.coef_span
    coef_pair := P.coef_pair
    coef_act := by
      intro c g x
      have hk : stabK ι' (stabTransport eG eΓ hι hJ' (P.y c) (P.stabI c g)) =
          ⟨eG (stabK ι (P.stabI c g) : G), (hJ' _).2 (by rw [MulEquiv.symm_apply_apply]; exact (stabK ι (P.stabI c g)).2)⟩ :=
        Subtype.ext (stabK_transport eG eΓ hι hJ' (P.y c) (P.stabI c g))
      show P.coef (S.ρ c g x) = (χ' (stabK ι' (stabTransport eG eΓ hι hJ' (P.y c) (P.stabI c g))) : ℂ) •
        ρ' (eΓ (P.stabI c g : Γ)) (P.coef x)
      rw [hk, hχ, hρ, P.coef_act] }

end ClassPres

end Formalism.IndefR.Bridge
end
end
