module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

theorem eq_sum_pureA_coset_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (K : Set (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact K →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
        (∀ r ∈ R, Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
          (∀ x, (fun i => (x i).2) ∉ K → Φ x = 0) →
            Φ = ∑ r ∈ R, GlobalTheory.WeilM.pureA F (GlobalTheory.WeilAdm.slice F Φ r) (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ U K hUo hUc hK
  classical
  have hcov : K ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ K, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  have hSB : ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    intro r
    have hcl : IsClopen {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      ⟨(AddSubgroup.isClosed_of_isOpen U hUo).preimage (continuous_id.sub continuous_const),
        hUo.preimage (continuous_id.sub continuous_const)⟩
    have hco : IsCompact {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      (Homeomorph.subRight r).isCompact_preimage.2 hUc
    refine ⟨?_, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U}
      · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} from hy),
          Set.indicator_of_mem hx]
      · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
        simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)
  refine ⟨R, fun r _ => hSB r, fun Φ hinv hsupp => ?_⟩
  funext x
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, (fun i => (x i).2) - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have hm : (fun i => (x i).2) ∈ {y | y - r0 ∈ U} := hxr0
      simp only [GlobalTheory.WeilM.pureA, GlobalTheory.WeilAdm.slice, RingEquiv.symm_apply_apply, Set.indicator_of_mem hm, mul_one]
      obtain ⟨x', hx'⟩ : ∃ x' : κ → AdeleRing (𝓞 F) F, x' = fun i => ((x i).1, r0 i) := ⟨_, rfl⟩
      have e : x = x' + GlobalTheory.WeilAdm.finE F ((fun i => (x i).2) - r0) := by
        subst hx'
        funext i
        refine Prod.ext ?_ ?_
        · show (x i).1 = (x i).1 + 0
          rw [add_zero]
        · show (x i).2 = r0 i + ((x i).2 - r0 i)
          rw [add_sub_cancel]
      conv_lhs => rw [e]
      rw [hinv x' _ hxr0, hx']
    · intro r hr hne
      simp only [GlobalTheory.WeilM.pureA]
      have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : (fun i => (x i).2) ∉ K := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [hsupp x hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    simp only [GlobalTheory.WeilM.pureA]
    have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.WeilAdm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.WeilAdm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infPart (w : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1

theorem infPart_infE (z : κ → mixedEmbedding.mixedSpace F) : infPart (infE F z) = z := by
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem infE_infPart (w : κ → AdeleRing (𝓞 F) F) (h : ∀ i, (w i).2 = 0) : infE F (infPart w) = w := by
  funext i
  refine Prod.ext ?_ (h i).symm
  exact RingEquiv.symm_apply_apply _ _

def eInf : AdeleRing (𝓞 F) F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem eInf_smul_snd (w : κ → AdeleRing (𝓞 F) F) (i : κ) : ((eInf (F := F) • w) i).2 = 0 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = 0
  exact zero_mul _

theorem eInf_smul_infE (z : κ → mixedEmbedding.mixedSpace F) : eInf (F := F) • infE F z = infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · show (1 : InfiniteAdeleRing F) * _ = _
    exact one_mul _
  · show (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    exact zero_mul _

theorem infE_add (z z' : κ → mixedEmbedding.mixedSpace F) : infE F (z + z') = infE F z + infE F z' := by
  funext i
  refine Prod.ext ?_ ?_
  · exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 + 0
    exact (add_zero _).symm

theorem infPart_add (w w' : κ → AdeleRing (𝓞 F) F) : infPart (w + w') = infPart w + infPart w' := by
  funext i
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (w i).1 (w' i).1

def rAd (t : ℝ) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)), 0)

theorem infE_smul (t : ℝ) (z : κ → mixedEmbedding.mixedSpace F) : infE F (t • z) = rAd (F := F) t • infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • z i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i)
    rw [← map_mul, smul_mul_assoc, one_mul]
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    exact (zero_mul _).symm

theorem infPart_smul (t : ℝ) (w : κ → AdeleRing (𝓞 F) F) : infPart (rAd (F := F) t • w) = t • infPart w := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)) * (w i).1) =
    t • InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1
  rw [map_mul, RingEquiv.apply_symm_apply, smul_mul_assoc, one_mul]

def infPart2 (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) := (infPart w.1, infPart w.2)

theorem archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    infPart2 (mixedSpaceVecPairAsAdeles F v) = v := by
  simp only [infPart2, mixedSpaceVecPairAsAdeles, infPart_infE]

theorem archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    eInf (F := F) • mixedSpaceVecPairAsAdeles F v = mixedSpaceVecPairAsAdeles F v := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.smul_mk, eInf_smul_infE]

theorem mixedSpaceVecPair_archimedeanPart_idempotent_smul (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    mixedSpaceVecPairAsAdeles F (infPart2 (eInf (F := F) • w)) = eInf (F := F) • w := by
  show (infE F (infPart (eInf (F := F) • w.1)), infE F (infPart (eInf (F := F) • w.2))) =
    (eInf (F := F) • w.1, eInf (F := F) • w.2)
  rw [infE_infPart _ (eInf_smul_snd w.1), infE_infPart _ (eInf_smul_snd w.2)]

theorem mixedSpaceVecPair_archimedeanPart_linearMap_apply (f : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) →ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (infPart2 (f (mixedSpaceVecPairAsAdeles F v))) = f (mixedSpaceVecPairAsAdeles F v) := by
  rw [← archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles v, map_smul]
  exact mixedSpaceVecPair_archimedeanPart_idempotent_smul _

theorem mixedSpaceVecPairAsAdeles_add (v v' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (v + v') = mixedSpaceVecPairAsAdeles F v + mixedSpaceVecPairAsAdeles F v' := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.fst_add, Prod.snd_add, infE_add, Prod.mk_add_mk]

theorem mixedSpaceVecPairAsAdeles_real_smul (t : ℝ) (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (t • v) = rAd (F := F) t • mixedSpaceVecPairAsAdeles F v := by
  simp only [mixedSpaceVecPairAsAdeles, Prod.smul_fst, Prod.smul_snd, infE_smul, Prod.smul_mk]

theorem infPart2_add (w w' : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (w + w') = infPart2 w + infPart2 w' := by
  simp only [infPart2, Prod.fst_add, Prod.snd_add, infPart_add, Prod.mk_add_mk]

theorem infPart2_smul (t : ℝ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (rAd (F := F) t • w) = t • infPart2 w := by
  simp only [infPart2, Prod.smul_fst, Prod.smul_snd, infPart_smul, Prod.smul_mk]

theorem exists_infLin (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∀ v, B (mixedSpaceVecPairAsAdeles F v) = mixedSpaceVecPairAsAdeles F (L v) := by
  refine ⟨{ toFun := fun v => infPart2 (B (mixedSpaceVecPairAsAdeles F v))
            invFun := fun v => infPart2 (B.symm (mixedSpaceVecPairAsAdeles F v))
            map_add' := fun v v' => by simp only [mixedSpaceVecPairAsAdeles_add, map_add (f := _), infPart2_add]
            map_smul' := fun t v => by simp only [mixedSpaceVecPairAsAdeles_real_smul, map_smul, infPart2_smul, RingHom.id_apply]
            left_inv := fun v => by
              show infPart2 (B.symm (mixedSpaceVecPairAsAdeles F (infPart2 (B.toLinearMap (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [mixedSpaceVecPair_archimedeanPart_linearMap_apply]
              simp [archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]
            right_inv := fun v => by
              show infPart2 (B (mixedSpaceVecPairAsAdeles F (infPart2 (B.symm.toLinearMap (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [mixedSpaceVecPair_archimedeanPart_linearMap_apply]
              simp [archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles] }, fun v => ?_⟩
  exact (mixedSpaceVecPair_archimedeanPart_linearMap_apply B.toLinearMap v).symm

theorem infLin_main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))),
      ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
        ∀ v, B (GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F v) = GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F (L v) :=
  fun _ _ _ _ _ B => exists_infLin B

end GlobalTheory.WeilAdm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.WeilAdm

theorem fintrans_cont (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    Continuous B :=
  IsModuleTopology.continuous_of_linearMap B.toLinearMap

def finIdem (F : Type) [Field F] [NumberField F] : AdeleRing (𝓞 F) F := (0, 1)

theorem finIdem_mul (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) :
    finIdem F * a = (0, a.2) := by
  change ((0 : InfiniteAdeleRing F) * a.1, (1 : FiniteAdeleRing (𝓞 F) F) * a.2) = _
  rw [zero_mul, one_mul]

theorem finiteAdelesVecPairAsAdeles_eq_idempotent_smul (F : Type) [Field F] [NumberField F] (κ : Type)
    (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    finE2 F m = finIdem F • finE2 F m := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change _ = finIdem F * (show AdeleRing (𝓞 F) F from (0, m.1 i)); rw [finIdem_mul]; rfl
  · change _ = finIdem F * (show AdeleRing (𝓞 F) F from (0, m.2 i)); rw [finIdem_mul]; rfl

theorem finiteAdeleIdempotent_smul_eq_finiteAdelesVecPair (F : Type) [Field F] [NumberField F] (κ : Type)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    finIdem F • w = finE2 F (fun i => (w.1 i).2, fun i => (w.2 i).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change finIdem F * w.1 i = _; rw [finIdem_mul]; rfl
  · change finIdem F * w.2 i = _; rw [finIdem_mul]; rfl

theorem finiteAdelesVecPairAsAdeles_add (F : Type) [Field F] [NumberField F] (κ : Type)
    (a b : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    finE2 F (a + b) = finE2 F a + finE2 F b := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · change ((0 : InfiniteAdeleRing F), a.1 i + b.1 i) = ((0 : InfiniteAdeleRing F) + 0, a.1 i + b.1 i)
    rw [add_zero]
  · change ((0 : InfiniteAdeleRing F), a.2 i + b.2 i) = ((0 : InfiniteAdeleRing F) + 0, a.2 i + b.2 i)
    rw [add_zero]

theorem finiteAdelesVecPairAsAdeles_zero (F : Type) [Field F] [NumberField F] (κ : Type) :
    finE2 F (0 : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rfl

theorem fintrans : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) →
      ∃ M' : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M' : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m' ∈ M', ∃ m ∈ M, B (GlobalTheory.WeilAdm.finE2 F m) = GlobalTheory.WeilAdm.finE2 F m' := by
  intro F _ _ κ _ B M hM
  let g : ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) →+
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    { toFun := fun m' => (fun i => ((B.symm (finE2 F m')).1 i).2, fun i => ((B.symm (finE2 F m')).2 i).2)
      map_zero' := by
        simp only [finiteAdelesVecPairAsAdeles_zero, map_zero]; rfl
      map_add' := fun a b => by
        simp only [finiteAdelesVecPairAsAdeles_add, map_add (f := _)]; rfl }
  have hg : ∀ m', finE2 F (g m') = B.symm (finE2 F m') := by
    intro m'
    rw [finiteAdelesVecPairAsAdeles_eq_idempotent_smul F κ m', map_smul, finiteAdeleIdempotent_smul_eq_finiteAdelesVecPair]
    rfl
  have hgc : Continuous g := by
    have h1 : Continuous fun m' : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => B.symm (finE2 F m') := by
      refine (fintrans_cont F κ B.symm).comp ?_
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
      · exact continuous_const.prodMk ((continuous_apply i).comp continuous_fst)
      · exact continuous_const.prodMk ((continuous_apply i).comp continuous_snd)
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
    · exact continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp h1))
    · exact continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp h1))
  refine ⟨M.comap g, hM.preimage hgc, fun m' hm' => ⟨g m', hm', ?_⟩⟩
  rw [hg, LinearEquiv.apply_symm_apply]

end GlobalTheory.WeilAdm
end
end

section

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

noncomputable def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem evI_eq_evIHom {F : Type} [Field F] [NumberField F] (a : AF F) : evI F a = evIHom F a := rfl

theorem trace_evI_heis {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {κ : Type} [Fintype κ]
    (x a b : κ → AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ b + ⅟(2 : AF F) * a ⬝ᵥ b)) =
      trP F κ (locV x) (locV b) + trP F κ (locV a) (locV b) / 2 := by
  have hdot : ∀ y : κ → AF F, evIHom F (y ⬝ᵥ b) = ∑ i, locV y i * locV b i := by
    intro y

    simp only [dotProduct, map_sum, map_mul, locV, evI_eq_evIHom]
  have h2 : ∀ t : AF F, evIHom F (⅟(2 : AF F) * t) = (1 / 2 : ℝ) • evIHom F t := by
    intro t
    have h : (2 : ℝ) • evIHom F (⅟(2 : AF F) * t) = evIHom F t := by
      rw [two_smul, ← map_add (f := _), ← two_mul, ← mul_assoc, mul_invOf_self, one_mul]
    rw [← h, smul_smul]
    norm_num
  rw [evI_eq_evIHom, map_add (f := _), h2, hdot, hdot, map_add (f := _), map_smul, trP, trP, smul_eq_mul]
  ring

theorem acts_rho_of_at_inf : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F} {κ : Type} [Fintype κ]
      (dc : Darboux Bf κ) (w : W'), At (evI F) w → ∀ f f₁ : SInf F κ,
      ⇑f₁ = schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) ⇑f → Acts (evI F) (dc.rho ψ w) ⇑f ⇑f₁ := by
  intro F _ _ ψ hψ W' _ _ Bf κ _ dc w hw f f₁ hf r hr
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add (f := _)]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr.1 x _ ha, hf, hloc, schrF]
  exact (mul_assoc _ _ _).symm

end GlobalTheory.ArchUniq
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.CayleyStab

theorem cayley_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)) (Y : Matrix (Fin d) (Fin d) (AE F E)), At (evFin F v) Y →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ h ∈ GlobalTheory.InertSph.KAt σ W v, mat h * (1 + Y) = 1 - Y := by
  intro F E _ _ _ _ _ σ d W v Y hY hYL hskew ⟨Np, hP1, hP2, hPL⟩ ⟨Nm, hM1, hM2, hML⟩
  set J := incM F W.J with hJ
  have hmap : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (A * B).map (cA σ) = A.map (cA σ) * B.map (cA σ) :=
    fun A B => Matrix.map_mul (f := (cA σ).toRingHom)
  have hmap1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (cA σ) = 1 :=
    Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))
  have hGP : (1 - Y) * Np * (1 + Y) = 1 - Y := by rw [Matrix.mul_assoc, hP2, Matrix.mul_one]
  have h1 : (1 - Y) * Np * ((1 + Y) * Nm) = 1 := by
    rw [← Matrix.mul_assoc, hGP, hM1]
  have h2 : (1 + Y) * Nm * ((1 - Y) * Np) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (1 + Y), hM2, Matrix.mul_one, hP1]

  have hQP : (1 - Y)ᵀ * J * (1 - Y).map (cA σ) = (1 + Y)ᵀ * J * (1 + Y).map (cA σ) := by
    rw [Matrix.map_sub _ (map_sub (cA σ)), Matrix.map_add _ (map_add (cA σ)), hmap1, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]
    have e : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (1 - A) * J * (1 - B) = (1 + A) * J * (1 + B) - 2 * (A * J + J * B) := by
      intro A B; noncomm_ring
    rw [e, hskew, mul_zero, sub_zero]
  have hU : ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ) = J := by
    have eT : Npᵀ * (1 + Y)ᵀ = 1 := by rw [← Matrix.transpose_mul, hP1, Matrix.transpose_one]
    have eM : (1 + Y).map (cA σ) * Np.map (cA σ) = 1 := by rw [← hmap, hP1, hmap1]
    calc ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ)
        = (Npᵀ * (1 + Y)ᵀ) * (((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ)) * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by
          rw [eT, eM, Matrix.one_mul, Matrix.mul_one]
      _ = Npᵀ * (((1 - Y) * Np * (1 + Y))ᵀ * J * ((1 - Y) * Np * (1 + Y)).map (cA σ)) * Np.map (cA σ) := by
          rw [hmap ((1 - Y) * Np), Matrix.transpose_mul ((1 - Y) * Np)]
          simp only [Matrix.mul_assoc]
      _ = Npᵀ * ((1 + Y)ᵀ * J * (1 + Y).map (cA σ)) * Np.map (cA σ) := by rw [hGP, hQP]
      _ = (Npᵀ * (1 + Y)ᵀ) * J * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [eT, eM, Matrix.one_mul, Matrix.mul_one]
  let g : GL (Fin d) (AE F E) := ⟨(1 - Y) * Np, (1 + Y) * Nm, h1, h2⟩
  have hg : g ∈ UG (cA σ) (incM F W.J) := hU
  let h : UA σ W.J := ⟨g, hg⟩
  have hmat : mat h = (1 - Y) * Np := rfl
  have hmatinv : mat h⁻¹ = (1 + Y) * Nm := rfl
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have e : mat h - 1 = -(Y * Np) - Y * Np := by
      rw [hmat]
      calc (1 - Y) * Np - 1 = (1 - Y) * Np - (1 + Y) * Np := by rw [hP1]
        _ = -(Y * Np) - Y * Np := by noncomm_ring
    have hYu : u • Y = 0 := hY u hu
    rw [e, smul_sub, smul_neg, ← Matrix.smul_mul, hYu, Matrix.zero_mul, neg_zero, sub_zero]
  · intro z hz
    refine ⟨?_, ?_⟩
    · rw [hmat, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hPL z hz) (hYL _ (hPL z hz))
    · rw [hmatinv, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
      exact add_mem (hML z hz) (hYL _ (hML z hz))
  · rw [hmat, hGP]

end GlobalTheory.CayleyStab
end
