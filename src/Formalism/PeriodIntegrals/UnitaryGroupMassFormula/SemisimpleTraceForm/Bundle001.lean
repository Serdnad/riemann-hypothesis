module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

namespace PI.SSAscent.UnitaryGroupMassFormula

open Matrix

theorem traceFormNondegenerate_baseChange : AscendStep := by
  intro K L _ _ _ a S hK
  classical
  set f : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) L :=
    (algebraMap K L).mapMatrix with hf
  set P : Submodule K (Matrix (Fin a) (Fin a) K) :=
    Subalgebra.toSubmodule (Algebra.adjoin K S) with hP
  let b := Module.finBasis K P
  set m := Module.finrank K P
  let β : Fin m → Matrix (Fin a) (Fin a) K := fun i => (b i : Matrix (Fin a) (Fin a) K)
  have hβA : ∀ i, β i ∈ Algebra.adjoin K S := fun i => (b i).2
  have hspanA : ∀ x ∈ Algebra.adjoin K S, ∃ d : Fin m → K, ∑ i, d i • β i = x := by
    intro x hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : P))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1
  have hli : LinearIndependent K β :=
    b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  let G : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => Matrix.trace (β i * β j)
  have hG : G.det ≠ 0 := by
    intro h0
    obtain ⟨d, hd0, hd⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hd0
    have hz : ∑ i, d i • β i = 0 := by
      apply hK
      · exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hβA i) _
      · intro y hy
        obtain ⟨e, rfl⟩ := hspanA y hy
        rw [Finset.mul_sum, trace_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hj : (d ᵥ* G) j = 0 := by rw [hd]; rfl
        rw [mul_smul_comm, trace_smul, Finset.sum_mul, trace_sum]
        simp only [smul_mul_assoc, trace_smul, smul_eq_mul]
        simp only [vecMul, dotProduct, G, Matrix.of_apply] at hj
        rw [hj, mul_zero]
    funext i
    exact (Fintype.linearIndependent_iff.mp hli) d hz i

  have hfA : ∀ y ∈ Algebra.adjoin K S, f y ∈ Algebra.adjoin L (f '' S) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r =>
        have : f (algebraMap K _ r) = algebraMap L (Matrix (Fin a) (Fin a) L) (algebraMap K L r) := by
          ext i j
          rw [hf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply,
            Matrix.algebraMap_matrix_apply]
          split_ifs <;> simp
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hfsmul : ∀ (c : K) (M : Matrix (Fin a) (Fin a) K), f (c • M) = algebraMap K L c • f M := by
    intro c M
    ext i j
    simp [hf]

  have hBspan : ∀ x ∈ Algebra.adjoin L (f '' S),
      x ∈ Submodule.span L (Set.range fun i => f (β i)) := by
    intro x hx
    have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin L (f '' S)) := hx
    rw [Algebra.adjoin_eq_span] at hx'
    refine (Submodule.span_le.mpr ?_) hx'
    have hcl : (Submonoid.closure (f '' S) : Set (Matrix (Fin a) (Fin a) L)) ⊆
        (Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L)
          (Algebra.adjoin K S).toSubmonoid : Set _) := by
      have : Submonoid.closure (f '' S) ≤
          Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L)
            (Algebra.adjoin K S).toSubmonoid := by
        rw [Submonoid.closure_le]
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨s, Algebra.subset_adjoin hs, rfl⟩
      exact this
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hcl hz
    obtain ⟨d, rfl⟩ := hspanA y hy
    show f (∑ i, d i • β i) ∈ _

    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hfsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro x hx hxy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp (hBspan x hx)
  have hG' : (G.map (algebraMap K L)).det ≠ 0 := by
    have := RingHom.map_det (algebraMap K L) G
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero _).mpr hG
  have hc : c ᵥ* G.map (algebraMap K L) = 0 := by
    funext j
    have h1 := hxy (f (β j)) (hfA _ (hβA j))
    rw [Finset.sum_mul, trace_sum] at h1
    simp only [vecMul, dotProduct, Matrix.map_apply, G, Matrix.of_apply, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, trace_smul, smul_eq_mul, ← map_mul, AddMonoidHom.map_trace]
    rfl
  by_contra hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  exact hG' (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc0, hc⟩)

end PI.SSAscent.UnitaryGroupMassFormula
end

section

namespace PI.SSAscent.UnitaryGroupMassFormula

open PI.SSAscent
open Matrix

section Bridge

variable {k : Type} [Field k] {a : ℕ}

def stabAlg (W : Submodule k (Fin a → k)) : Subalgebra k (Matrix (Fin a) (Fin a) k) where
  carrier := {x | ∀ v ∈ W, x *ᵥ v ∈ W}
  mul_mem' := by
    intro x y hx hy v hv
    rw [← Matrix.mulVec_mulVec]
    exact hx _ (hy v hv)
  add_mem' := by
    intro x y hx hy v hv
    rw [Matrix.add_mulVec]
    exact W.add_mem (hx v hv) (hy v hv)
  algebraMap_mem' := by
    intro c v hv
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem c hv

private theorem mem_stabAlg_iff (W : Submodule k (Fin a → k))
    (x : Matrix (Fin a) (Fin a) k) : x ∈ stabAlg W ↔ ∀ v ∈ W, x *ᵥ v ∈ W :=
  Iff.rfl

theorem imAlg_le_stabAlg {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (h : IsInv ρ W) : imAlg ρ ≤ stabAlg W := by
  unfold imAlg
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨g, rfl⟩
  exact (mem_stabAlg_iff W _).mpr (fun v hv => h g v hv)

instance towerSub (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) :
    IsScalarTower k A (Fin a → k) where
  smul_assoc c x v := by
    change ((c • x : A) : Matrix (Fin a) (Fin a) k) *ᵥ v = c • ((x : Matrix (Fin a) (Fin a) k) *ᵥ v)
    rw [Subalgebra.coe_smul, Matrix.smul_mulVec]

theorem smul_sub_def (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) (x : A) (v : Fin a → k) :
    x • v = (x : Matrix (Fin a) (Fin a) k) *ᵥ v := rfl

def liftSub (A : Subalgebra k (Matrix (Fin a) (Fin a) k)) (W : Submodule k (Fin a → k))
    (h : A ≤ stabAlg W) : Submodule A (Fin a → k) where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' x v hv := by
    rw [smul_sub_def]
    exact h x.2 v hv

theorem isInv_restrict {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k)
    (N : Submodule (imAlg ρ) (Fin a → k)) : IsInv ρ (N.restrictScalars k) := by
  intro g v hv
  have hg : (ρ g : Matrix (Fin a) (Fin a) k) ∈ imAlg ρ :=
    Algebra.subset_adjoin ⟨g, rfl⟩
  have hmem : (⟨_, hg⟩ : imAlg ρ) • v ∈ N := N.smul_mem _ hv
  rw [smul_sub_def] at hmem
  exact hmem

private theorem mem_liftSub_iff (A : Subalgebra k (Matrix (Fin a) (Fin a) k))
    (W : Submodule k (Fin a → k)) (h : A ≤ stabAlg W) (v : Fin a → k) :
    v ∈ liftSub A W h ↔ v ∈ W :=
  Iff.rfl

private theorem exists_isCompl_of_isSSRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k)
    (hρ : PI.SSAscent.IsSSRep ρ) (N : Submodule (imAlg ρ) (Fin a → k)) :
    ∃ N', IsCompl N N' := by
  obtain ⟨W', hW', hc⟩ := hρ (N.restrictScalars k) (isInv_restrict ρ N)
  have hle : imAlg ρ ≤ stabAlg W' := imAlg_le_stabAlg ρ W' hW'
  refine ⟨liftSub (imAlg ρ) W' hle, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxN hxW'
    exact (Submodule.disjoint_def.mp hc.disjoint) x hxN
      ((mem_liftSub_iff _ W' hle x).mp hxW')
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : x ∈ N.restrictScalars k ⊔ W' := by
      rw [codisjoint_iff.mp hc.codisjoint]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr ⟨y, hy, z, (mem_liftSub_iff _ W' hle z).mpr hz, hyz⟩

theorem isSemisimple_of_isSSRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (hρ : IsSSRep ρ) :
    IsSemisimpleModule (imAlg ρ) (Fin a → k) := by
  have key : ∀ N : Submodule (imAlg ρ) (Fin a → k), ∃ N', IsCompl N N' :=
    exists_isCompl_of_isSSRep ρ hρ
  haveI : ComplementedLattice (Submodule (imAlg ρ) (Fin a → k)) := ⟨key⟩
  exact ⟨⟩

theorem isSSRep_of_isSemisimple {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k)
    (h : IsSemisimpleModule (imAlg ρ) (Fin a → k)) : IsSSRep ρ := by
  intro W hW
  have hle : imAlg ρ ≤ stabAlg W := imAlg_le_stabAlg ρ W hW
  obtain ⟨N', hc⟩ := exists_isCompl (liftSub (imAlg ρ) W hle)
  refine ⟨N'.restrictScalars k, isInv_restrict ρ N', ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxW hxN'
    exact (Submodule.disjoint_def.mp hc.disjoint) x
      ((mem_liftSub_iff _ W hle x).mpr hxW) hxN'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : x ∈ liftSub (imAlg ρ) W hle ⊔ N' := by
      rw [codisjoint_iff.mp hc.codisjoint]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr ⟨y, (mem_liftSub_iff _ W hle y).mp hy, z, hz, hyz⟩

end Bridge

end PI.SSAscent.UnitaryGroupMassFormula
end

section

namespace PI.SSAscent.UnitaryGroupMassFormula

open PI.SSAscent

theorem range_mapRep {Γ : Type} [Group Γ] {K L : Type} [Field K] [Field L] [Algebra K L] {a : ℕ}
    (ρ : Γ →* GL (Fin a) K) :
    (Set.range fun g => ((mapRep (algebraMap K L) ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) =
      (algebraMap K L).mapMatrix '' Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K) := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(ρ g : Matrix (Fin a) (Fin a) K), ⟨g, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

theorem ssAscent_of (hD : DownStep) (hA : AscendStep) (hU : UpStep) : PI.SSAscent := by
  intro K L _ _ _ _ Γ _ a ρ hρ
  apply hU L Γ a
  have h1 : TrNondeg (imAlg ρ) := hD K Γ a ρ hρ
  have h2 := hA K L a (Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K)) h1
  have h3 : imAlg (mapRep (algebraMap K L) ρ) =
      Algebra.adjoin L ((algebraMap K L).mapMatrix '' Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K)) :=
    congrArg (Algebra.adjoin L) (range_mapRep (L := L) ρ)
  rw [h3]
  exact h2

end PI.SSAscent.UnitaryGroupMassFormula
end
