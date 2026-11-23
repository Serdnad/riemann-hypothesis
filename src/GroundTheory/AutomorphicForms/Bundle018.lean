module

public import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
public import GroundTheory.AutomorphicForms.GeometricLemmaCellKernel
public import GroundTheory.AutomorphicForms.GeometricLemmaCellSurjective
public import GroundTheory.AutomorphicForms.GeometricLemmaGraded
public import GroundTheory.AutomorphicForms.LeviStagesJacquet
import GroundTheory.AutomorphicForms.AdmissibleInduction
public import GroundTheory.AutomorphicForms.SphericalSatake
public import GroundTheory.AutomorphicForms.SphericalIntegral
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem cellUnion_mul_mem {k : ℕ} (w : Fin k → Equiv.Perm (Fin n)) (j : ℕ) :
    (∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) j, ∀ q ∈ blockUpper F n γ, g * q ∈ cellUnion (fun l => doubleCoset
          (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j) ∧
      (∀ p ∈ blockUpper F n β, ∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j, p * g ∈ cellUnion
          (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
            (blockUpper F n γ)) j) := by
  constructor
  · intro g hg q hq
    obtain ⟨l, hl, hgl⟩ := (mem_cellUnion _).1 hg
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_doubleCoset.1 hgl
    exact (mem_cellUnion _).2 ⟨l, hl, mem_doubleCoset.2 ⟨p', hp', q' * q,
      (blockUpper F n γ).mul_mem hq' hq, by group⟩⟩
  · intro p hp g hg
    obtain ⟨l, hl, hgl⟩ := (mem_cellUnion _).1 hg
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_doubleCoset.1 hgl
    exact (mem_cellUnion _).2 ⟨l, hl, mem_doubleCoset.2 ⟨p * p',
      (blockUpper F n β).mul_mem hp hp', q', hq', by group⟩⟩

theorem exists_filtration_jacquetModule_parabolicInd (hσ : IsSmooth σ) :
    ∃ (k : ℕ) (w : Fin k → Equiv.Perm (Fin n)),
      (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
      ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
        V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
        ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
          ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
              ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
              (twist ((invSqrtModular F n γ).comp leviIncl)
                (indRep (cellLeviSub F β γ (w j)) (cellInducing β γ (w j) σ))),
            Function.Surjective Ψ ∧
              ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  obtain ⟨k, w, hcov, hanti⟩ := exists_cellEnumeration (F := F) β γ
  set C : Fin k → Set (GL (Fin n) F) := fun l =>
    doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro g hgi hgj
    obtain ⟨l, -, hl⟩ := hcov g
    exact hij ((hl i hgi).trans (hl j hgj).symm)
  have hcov' : ∀ g, ∃ l, g ∈ C l := fun g => (hcov g).exists
  have hcl := closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨k, w, hcov, fun i => jacquetFiltration γ (σ := σ) (cellUnion C i), ?_, ?_, ?_, ?_⟩
  · show jacquetFiltration γ (cellUnion C 0) = ⊥
    rw [cellUnion_zero, jacquetFiltration_empty]
  · show jacquetFiltration γ (cellUnion C k) = ⊤
    rw [cellUnion_of_cover hcov', jacquetFiltration_univ]
  · exact fun i i' h => jacquetFiltration_mono γ (cellUnion_mono h)
  refine ⟨fun i m => jacquetFiltration_le_comap γ (cellUnion_mul_mem w i).1 m, fun j => ?_⟩
  have hYo : IsOpen (cellUnion C ((j : ℕ) + 1)) := isOpen_cellUnion hdisj hcov' hcl _
  have hCY : closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j :=
    closure_inter_cellUnion_succ hdisj hcl j
  have hYQ := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).1
  have hYP := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).2
  have hdiff : cellUnion C ((j : ℕ) + 1) \ C j = cellUnion C j := by
    rw [cellUnion_succ j, union_sdiff_right, (disjoint_cellUnion hdisj j).symm.sdiff_eq_left]
  refine ⟨⟨gradedJacquetMap γ (w j) σ hYo hCY hYQ, fun m => ?_⟩, ?_, fun x => ?_⟩
  · refine LinearMap.ext fun x => ?_
    exact gradedJacquetMap_jacquetRep σ hYo hCY hYQ m x
  · exact gradedJacquetMap_surjective σ hYo hCY hYQ (cellJacquetMap_surjective hYo hCY hYP hYQ hσ)
  · have := gradedJacquetMap_eq_zero_iff σ hYo hCY hYQ
      (fun f hf h0 => exists_sub_mem_ker_of_cellJacquet_eq_zero σ hσ hYo hCY hYQ hf h0) x
    rw [hdiff] at this
    exact this

end Parabolic

end GroundTheory.Automorphic
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ}

section Compact

theorem isClosed_leviUnipotent :
    IsClosed ((leviUnipotent F n β γ : Subgroup (levi F n β)) : Set (levi F n β)) := by
  rw [leviUnipotent, Subgroup.coe_subgroupOf]
  exact isClosed_unipotentRadical.preimage continuous_subtype_val

theorem isClosedEmbedding_leviUnipotent :
    IsClosedEmbedding fun u : leviUnipotent F n β γ => ((u : levi F n β) : GL (Fin n) F) :=
  isClosed_levi.isClosedEmbedding_subtypeVal.comp
    isClosed_leviUnipotent.isClosedEmbedding_subtypeVal

instance locallyCompactSpace_leviUnipotent : LocallyCompactSpace (leviUnipotent F n β γ) :=
  isClosedEmbedding_leviUnipotent.locallyCompactSpace


variable (F n β γ) in
def leviUnipotentToUnipotent : leviUnipotent F n β γ →* unipotentRadical F n γ where
  toFun u := ⟨((u : levi F n β) : GL (Fin n) F), Subgroup.mem_subgroupOf.1 u.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem isClosedEmbedding_leviUnipotentToUnipotent :
    IsClosedEmbedding (leviUnipotentToUnipotent F n β γ) := by
  have hN : IsClosedEmbedding
      (Subtype.val : unipotentRadical F n γ → GL (Fin n) F) :=
    isClosed_unipotentRadical.isClosedEmbedding_subtypeVal
  exact (hN.of_comp_iff).1 isClosedEmbedding_leviUnipotent

theorem exists_compactOpen_leviUnipotent (s : Finset (leviUnipotent F n β γ)) :
    ∃ K : Subgroup (leviUnipotent F n β γ), IsCompact (K : Set (leviUnipotent F n β γ)) ∧
      IsOpen (K : Set (leviUnipotent F n β γ)) ∧ ∀ x ∈ s, x ∈ K := by
  classical
  obtain ⟨K₀, hKc, hKo, hK⟩ :=
    exists_compactOpen_unipotentRadical (s.image (leviUnipotentToUnipotent F n β γ))
  have he := isClosedEmbedding_leviUnipotentToUnipotent (F := F) (n := n) (β := β) (γ := γ)
  refine ⟨K₀.comap (leviUnipotentToUnipotent F n β γ), ?_, ?_, fun x hx => ?_⟩
  · rw [Subgroup.coe_comap]
    exact he.isCompact_preimage hKc
  · rw [Subgroup.coe_comap]
    exact hKo.preimage he.continuous
  · exact Subgroup.mem_comap.2 (hK _ (Finset.mem_image_of_mem _ hx))

end Compact

section Functor

variable {U U' U'' : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup U''] [Module ℂ U''] {σ : Representation ℂ (levi F n β) U}
  {σ' : Representation ℂ (levi F n β) U'} {σ'' : Representation ℂ (levi F n β) U''}


variable (γ) in
def restrictLeviUnipotent (f : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (σ.comp (leviUnipotent F n β γ).subtype)
      (σ'.comp (leviUnipotent F n β γ).subtype) :=
  ⟨f.toLinearMap, fun u => f.isIntertwining' u⟩

def leviJacquetMap (h : Refines β γ) (f : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (leviJacquetRep h σ) (leviJacquetRep h σ') :=
  ⟨Representation.Coinvariants.map _ _ (restrictLeviUnipotent γ f), fun m =>
    Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, leviJacquetRep_mk, map_smul,
        Representation.Coinvariants.map_mk]
      congr 2
      exact Representation.IntertwiningMap.isIntertwining _ _ f (h.leviIncl F m) v)⟩

theorem leviJacquetMap_mk (h : Refines β γ) (f : Representation.IntertwiningMap σ σ') (v : U) :
    leviJacquetMap h f (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (f v) := rfl

theorem exact_leviJacquetMap (h : Refines β γ) (hσ' : IsSmooth σ') (hσ'' : IsSmooth σ'')
    (f : Representation.IntertwiningMap σ σ') (g : Representation.IntertwiningMap σ' σ'')
    (hfg : Function.Exact f g) :
    Function.Exact (leviJacquetMap h f) (leviJacquetMap h g) :=
  exact_coinvariantsMap exists_compactOpen_leviUnipotent
    (isSmooth_comp_subtype hσ' _) (isSmooth_comp_subtype hσ'' _)
    (restrictLeviUnipotent γ f) (restrictLeviUnipotent γ g) hfg

end Functor

end Parabolic

end GroundTheory.Automorphic
end
end

section

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa Parabolic HeckeAlgebra HeckeAlgebraLevel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Characters

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem exists_ker_sphericalCharacter_eq (I : Ideal (SphericalHecke μ (F := F) (n := n)))
    [I.IsMaximal] : ∃ w : Fin n → ℂˣ,
      RingHom.ker (sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w)) = I := by
  haveI := isIntegral_satake (μ := μ) (F := F) (n := n)
  obtain ⟨w, hw⟩ := exists_ker_evalAt_comp_eq (satakeHom μ) satakeHom_injective I
  exact ⟨w, by rw [← evalAt_comp_satakeHom]; exact hw⟩

end Characters

end Spherical

end GroundTheory.Automorphic
end
end
