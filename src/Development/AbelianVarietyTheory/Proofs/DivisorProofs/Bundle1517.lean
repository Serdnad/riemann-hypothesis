module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import GroundTheory.GlobalFields.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle205
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.CentCpt

section Closed
variable {L : Type} [NormedField L] [IsAlgClosed L] {n : ℕ}

theorem exists_eigenbasis (y : Matrix (Fin n) (Fin n) L) (hs : y.charpoly.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → Fin n → L) (l : ι → L), LinearIndependent L v ∧
      Fintype.card ι = n ∧ ∀ i, Module.End.HasEigenvector (Matrix.toLin' y) (l i) (v i) := by
  classical
  have hnd : y.charpoly.roots.Nodup := nodup_roots hs
  have hcard : y.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hev : ∀ r : y.charpoly.roots.toFinset, ∃ v : Fin n → L,
      Module.End.HasEigenvector (Matrix.toLin' y) r.1 v := fun r =>
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by
      rw [Matrix.charpoly_toLin']
      exact isRoot_of_mem_roots (Multiset.mem_toFinset.1 r.2))).exists_hasEigenvector
  choose v hv using hev
  exact ⟨_, inferInstance, v, fun r => r.1,
    Module.End.eigenvectors_linearIndependent' _ _ Subtype.val_injective v hv,
    by rw [Fintype.card_coe, hcard], hv⟩

theorem aeval_mulVec_eigen (y : Matrix (Fin n) (Fin n) L) {μ : L} {x : Fin n → L}
    (h : Module.End.HasEigenvector (Matrix.toLin' y) μ x) (q : L[X]) :
    aeval y q *ᵥ x = q.eval μ • x := by
  rw [← Module.End.aeval_apply_of_hasEigenvector h]
  have h1 := aeval_algHom_apply (toLinAlgEquiv' (R := L) (n := Fin n)).toAlgHom y q
  exact (LinearMap.congr_fun h1 x).symm

theorem exists_bound (y : Matrix (Fin n) (Fin n) L) (hs : y.charpoly.Separable) :
    ∃ M : ℝ, ∀ t : Matrix (Fin n) (Fin n) L, t * y = y * t →
      (∃ B : ℝ, ∀ k : ℕ, ∀ i j, ‖(t ^ k) i j‖ ≤ B) → ∀ i j, ‖t i j‖ ≤ M := by
  classical
  obtain ⟨ι, _, v, l, hli, hcard, hv⟩ := exists_eigenbasis y hs
  let b : Module.Basis ι L (Fin n → L) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by rw [hcard, Module.finrank_fin_fun])
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  let c : Fin n → ι → L := fun j i => b.repr (Pi.single j 1) i
  refine ⟨∑ a, ∑ j, ∑ i, ‖c j i‖ * ‖v i a‖, fun t ht ⟨B, hB⟩ a j => ?_⟩
  obtain ⟨p, hp⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm y t hs ht.symm
  have hpow : ∀ k : ℕ, ∀ i, (t ^ k) *ᵥ v i = (p.eval (l i)) ^ k • v i := by
    intro k i
    rw [hp, ← map_pow, aeval_mulVec_eigen y (hv i), eval_pow]
  have hd : ∀ i, ‖p.eval (l i)‖ ≤ 1 := by
    intro i
    obtain ⟨a0, ha0⟩ : ∃ a0, v i a0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact (hv i).2 (funext h)
    have hk : ∀ k : ℕ, ‖p.eval (l i)‖ ^ k ≤ (B * ∑ j, ‖v i j‖) / ‖v i a0‖ := by
      intro k
      rw [le_div_iff₀ (norm_pos_iff.2 ha0), ← norm_pow, ← norm_mul]
      have e := congrFun (hpow k i) a0
      rw [Pi.smul_apply, smul_eq_mul] at e
      rw [← e, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB k a0 j) (norm_nonneg _)
    by_contra h1
    push_neg at h1
    obtain ⟨k, hk'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop
      ((B * ∑ j, ‖v i j‖) / ‖v i a0‖)).exists
    exact absurd (hk k) (not_le.2 hk')
  have hcol : t a j = (t *ᵥ Pi.single j 1) a := by
    rw [Matrix.mulVec_single_one]; rfl
  have hexp : (Pi.single j 1 : Fin n → L) = ∑ i, c j i • v i := by
    rw [← hb]; exact (b.sum_repr _).symm
  have hval : t a j = ∑ i, c j i * (p.eval (l i) * v i a) := by
    rw [hcol, hexp, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hpow 1 i
    rw [pow_one, pow_one] at this
    rw [Matrix.mulVec_smul, this, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hval]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ i, ‖c j i * (p.eval (l i) * v i a)‖ ≤ ∑ i, ‖c j i‖ * ‖v i a‖ := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (by
      simpa using mul_le_mul_of_nonneg_right (hd i) (norm_nonneg (v i a))) (norm_nonneg _)
  refine h1.trans ?_
  have hnn : ∀ a' j', 0 ≤ ∑ i, ‖c j' i‖ * ‖v i a'‖ := fun _ _ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ∑ i, ‖c j i‖ * ‖v i a‖ ≤ ∑ j', ∑ i, ‖c j' i‖ * ‖v i a‖ :=
        Finset.single_le_sum (f := fun j' => ∑ i, ‖c j' i‖ * ‖v i a‖) (fun j' _ => hnn a j') (Finset.mem_univ j)
    _ ≤ ∑ a', ∑ j', ∑ i, ‖c j' i‖ * ‖v i a'‖ :=
        Finset.single_le_sum (f := fun a' => ∑ j', ∑ i, ‖c j' i‖ * ‖v i a'‖)
          (fun a' _ => Finset.sum_nonneg fun j' _ => hnn a' j') (Finset.mem_univ a)

end Closed
end GlobalTheory.CentCpt

namespace GlobalTheory.CentCpt

section Local
variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] {n : ℕ}

theorem exists_bound_local (y : Matrix (Fin n) (Fin n) F) (hs : y.charpoly.Separable) :
    ∃ M : ℝ, ∀ t : Matrix (Fin n) (Fin n) F, t * y = y * t →
      (∃ B : ℝ, ∀ k : ℕ, ∀ i j, ‖(t ^ k) i j‖ ≤ B) → ∀ i j, ‖t i j‖ ≤ M := by
  letI : NormedField (AlgebraicClosure F) := spectralNorm.normedField F (AlgebraicClosure F)
  let f : F →+* AlgebraicClosure F := algebraMap F _
  have hf : ∀ x : F, ‖f x‖ = ‖x‖ := fun x => spectralNorm_extends (L := AlgebraicClosure F) x
  obtain ⟨M, hM⟩ := exists_bound (y.map f) (by rw [Matrix.charpoly_map]; exact hs.map)
  refine ⟨M, fun t ht ⟨B, hB⟩ i j => ?_⟩
  have := hM (t.map f) (by rw [← Matrix.map_mul, ht, Matrix.map_mul]) ⟨B, fun k a b => by
      rw [← Matrix.map_pow, Matrix.map_apply, hf]; exact hB k a b⟩ i j
  rwa [Matrix.map_apply, hf] at this

theorem isCompact_bdd [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ i j, ‖(g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ i j, ‖((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  first
  | exact @_root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
  | exact _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
  | (apply _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> assumption)
  | (intros; apply _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units ..)

end Local

theorem norm_le_sum {F : Type} [NormedField F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    ‖A i j‖ ≤ ∑ a, ∑ b, ‖A a b‖ :=
  (Finset.single_le_sum (f := fun b => ‖A i b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i))

end GlobalTheory.CentCpt

namespace GlobalTheory.CentCpt

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w),
    y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ t ∈ twCent (MonoidHom.id (UL n w)) y,
      IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) → t ∈ Ω := by
  intro E _ _ _ _ n w y hs
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist (w.adicCompletion E) :=
    inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
      (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
  haveI : CompleteSpace (w.adicCompletion E) := inferInstance
  haveI : ProperSpace (w.adicCompletion E) :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (w.adicCompletion E)
  obtain ⟨M, hM⟩ := exists_bound_local (y.1.val) hs
  refine ⟨Subtype.val ⁻¹' {g : GLw n w | (∀ i j, ‖(g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M) ∧
      ∀ i j, ‖((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M},
    (GlobalTheory.LocFinU.isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_bdd (n := n) M), ?_⟩
  have hbd : ∀ s ∈ twCent (MonoidHom.id (UL n w)) y, IsCompact (closure (Subgroup.zpowers s : Set (UL n w))) →
      ∀ i j, ‖(s.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M := by
    intro s hs' hcs
    have hcont : Continuous fun g : UL n w =>
        ∑ a, ∑ b, ‖(g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) a b‖ :=
      continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        ((Units.continuous_val.comp continuous_subtype_val).matrix_elem a b).norm
    obtain ⟨B, hB⟩ := (hcs.image hcont).bddAbove
    refine hM _ ?_ ⟨B, fun k a b => ?_⟩
    · have h1 : s * y = y * s := hs'
      have h2 := congrArg (fun g : UL n w => (g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) h1
      simpa using h2
    · have hk : s ^ k ∈ closure (Subgroup.zpowers s : Set (UL n w)) :=
        subset_closure (Subgroup.npow_mem_zpowers s k)
      have e : ((s ^ k).1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
          (s.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ^ k := by
        simp [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      rw [← e]
      exact (norm_le_sum _ a b).trans (hB ⟨_, hk, rfl⟩)
  intro t ht hc
  refine ⟨hbd t ht hc, ?_⟩
  have := hbd t⁻¹ (inv_mem ht) (by rwa [Subgroup.zpowers_inv])
  simpa using this

end GlobalTheory.CentCpt
end

section

open Filter GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.AvgRestr

private lemma mem_rStab_iff_forall_mul_right_invariant {H : Type} [Group H] (u : H → ℂ) (k : H) :
    k ∈ rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

private lemma avg_eq_inv_index_mul_finsum_rStab_quotient {H : Type} [Group H] (u : H → ℂ) :
    avg u = ((rStab u).index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ rStab u, u q.out := rfl

lemma apply_out {H : Type} [Group H] (u : H → ℂ) (x : H) : u ((x : H ⧸ rStab u).out) = u x := by
  have h : ((x : H ⧸ rStab u).out)⁻¹ * x ∈ rStab u :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : H ⧸ rStab u))
  have h2 := (mem_rStab_iff_forall_mul_right_invariant u _).mp h ((x : H ⧸ rStab u).out)
  rw [mul_inv_cancel_left] at h2
  exact h2.symm

private lemma rStab_comp_eq_comap_of_surjective {A B : Type} [Group A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (v : B → ℂ) : rStab (v ∘ π) = (rStab v).comap π := by
  ext k
  rw [Subgroup.mem_comap, mem_rStab_iff_forall_mul_right_invariant, mem_rStab_iff_forall_mul_right_invariant]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hπ y
    have h2 := h x
    simpa [Function.comp, map_mul] using h2
  · intro h x
    simp only [Function.comp_apply, map_mul]
    exact h (π x)

private lemma bijective_quotient_comap_of_surjective {A B : Type} [Group A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (S : Subgroup B) :
    Function.Bijective (fun q : A ⧸ S.comap π => ((π q.out : B) : B ⧸ S)) := by
  constructor
  · intro q q' h
    have h2 := QuotientGroup.eq.mp h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_comap,
      map_mul, map_inv]
    exact h2
  · intro z
    obtain ⟨a, ha⟩ := hπ z.out
    refine ⟨(a : A ⧸ S.comap π), ?_⟩
    have h2 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : A ⧸ S.comap π))
    rw [Subgroup.mem_comap, map_mul, map_inv] at h2
    show ((π (a : A ⧸ S.comap π).out : B) : B ⧸ S) = z
    rw [← QuotientGroup.out_eq' z, ← ha, QuotientGroup.eq]
    exact h2

theorem avg_comp_surj {A B : Type} [Group A] [Group B] (π : A →* B) (hπ : Function.Surjective π) (v : B → ℂ) :
    avg (v ∘ π) = avg v := by
  rw [avg_eq_inv_index_mul_finsum_rStab_quotient, avg_eq_inv_index_mul_finsum_rStab_quotient, rStab_comp_eq_comap_of_surjective π hπ v]
  let e := Equiv.ofBijective _ (bijective_quotient_comap_of_surjective π hπ (rStab v))
  have hidx : ((rStab v).comap π).index = (rStab v).index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Nat.card_congr e
  rw [hidx]
  congr 1
  refine (finsum_congr ?_).trans (finsum_comp_equiv e (f := fun z : B ⧸ rStab v => v z.out))
  intro q
  exact (apply_out v (π q.out)).symm

private lemma bijective_pi_quotient_to_quotient_pi {J : Type} (M : J → Type) [∀ j, Group (M j)] (R : ∀ j, Subgroup (M j)) :
    Function.Bijective
      (fun q : (∀ j, M j) ⧸ Subgroup.pi Set.univ R => fun j => ((q.out j : M j) : M j ⧸ R j)) := by
  constructor
  · intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_pi]
    intro j _
    have h2 := QuotientGroup.eq.mp (congrFun h j)
    simpa only [Pi.mul_apply, Pi.inv_apply] using h2
  · intro z
    refine ⟨(((fun j => (z j).out) : ∀ j, M j) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R), ?_⟩
    funext j
    have hm := QuotientGroup.eq.mp
      (QuotientGroup.out_eq' ((((fun j => (z j).out) : ∀ j, M j)) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R))
    have hj := (Subgroup.mem_pi _).mp hm j (Set.mem_univ j)
    simp only [Pi.mul_apply, Pi.inv_apply] at hj
    show ((_ : M j) : M j ⧸ R j) = z j
    rw [← QuotientGroup.out_eq' (z j), QuotientGroup.eq]
    exact hj

theorem avg_pi {J : Type} [Fintype J] (M : J → Type) [∀ j, Group (M j)] (v : ∀ j, M j → ℂ)
    (hv : ∀ j, (rStab (v j)).index ≠ 0) :
    avg (fun x : (∀ j, M j) => ∏ j, v j (x j)) = ∏ j, avg (v j) := by
  classical
  haveI : ∀ j, (rStab (v j)).FiniteIndex := fun j => ⟨hv j⟩
  haveI : ∀ j, Fintype (M j ⧸ rStab (v j)) := fun j => Fintype.ofFinite _
  let S : Subgroup (∀ j, M j) := Subgroup.pi Set.univ (fun j => rStab (v j))
  have hS : S ≤ rStab (fun x : (∀ j, M j) => ∏ j, v j (x j)) := by
    intro k hk
    rw [mem_rStab_iff_forall_mul_right_invariant]
    intro x
    refine Finset.prod_congr rfl (fun j _ => ?_)
    exact (mem_rStab_iff_forall_mul_right_invariant (v j) (k j)).mp ((Subgroup.mem_pi _).mp hk j (Set.mem_univ j)) (x j)
  let e := Equiv.ofBijective _ (bijective_pi_quotient_to_quotient_pi M (fun j => rStab (v j)))
  have hidx : S.index = ∏ j, (rStab (v j)).index := by
    rw [Subgroup.index_eq_card, Nat.card_congr e, Nat.card_pi]
    simp only [Subgroup.index_eq_card]
  have hS0 : S.index ≠ 0 := by
    rw [hidx]; exact Finset.prod_ne_zero_iff.mpr (fun j _ => hv j)
  have hsum : (∑ᶠ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j)) = ∏ j, ∑ᶠ q : M j ⧸ rStab (v j), v j q.out := by
    have h1 : ∀ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j) = ∏ j, v j ((e q j).out) := by
      intro q
      refine Finset.prod_congr rfl (fun j _ => ?_)
      exact (apply_out (v j) (q.out j)).symm
    rw [finsum_congr h1]
    refine (finsum_comp_equiv e (f := fun z : (∀ j, M j ⧸ rStab (v j)) => ∏ j, v j (z j).out)).trans ?_
    rw [finsum_eq_sum_of_fintype]
    simp only [finsum_eq_sum_of_fintype]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [GlobalTheory.BCT.avg_eq_of_le_rStab _ _ S hS hS0]
  simp only [avg_eq_inv_index_mul_finsum_rStab_quotient]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Nat.cast_prod, ← hidx, hsum]

theorem avg_restrProd : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (u : ∀ i, KH i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ i, (rStab (u i)).index ≠ 0) → (∀ᶠ i in cofinite, ∀ k, u i k = 1) → avg (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) = ∏ᶠ i, avg (u i) := by
  intro ι G _ H _ p K KH hK u happ hu h1
  classical
  have hs := Filter.eventually_cofinite.mp h1
  let T := hs.toFinset
  let π : K →* ∀ j : T, KH j :=
    MonoidHom.pi (fun j : T => ((p j).comp K.subtype).codRestrict (KH j) (fun k => (hK k).1 k.2 j))
  have hπ : Function.Surjective π := by
    intro y
    let y' : ∀ i, H i := fun i => if h : i ∈ T then ((y ⟨i, h⟩ : KH i) : H i) else 1
    have hy' : ∀ i, y' i ∈ KH i := by
      intro i
      simp only [y']
      split_ifs with h
      · exact (y ⟨i, h⟩).2
      · exact (KH i).one_mem
    obtain ⟨x, hx⟩ := happ y' (Filter.Eventually.of_forall hy')
    have hxK : x ∈ K := (hK x).2 (fun i => by rw [hx i]; exact hy' i)
    refine ⟨⟨x, hxK⟩, ?_⟩
    funext j
    apply Subtype.ext
    change p (j : ι) x = ((y j : KH (j : ι)) : H (j : ι))
    rw [hx]
    simp [y', j.2]
  have hfun : (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) =
      (fun y : (∀ j : T, KH j) => ∏ j : T, u j (y j)) ∘ π := by
    funext k
    rw [Function.comp_apply, finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · exact (Finset.prod_coe_sort T (fun i => u i ⟨p i k, (hK k).1 k.2 i⟩)).symm
    · intro i hi
      simp only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hall
      exact (Function.mem_mulSupport.mp hi) (hall _)
  rw [hfun, avg_comp_surj π hπ]
  refine (avg_pi (fun j : T => (KH j : Type)) (fun j => u j) (fun j => hu j)).trans ?_
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
  · exact Finset.prod_coe_sort T (fun i => avg (u i))
  · intro i hi
    simp only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro hall
    apply Function.mem_mulSupport.mp hi
    have hc : u i = fun _ => 1 := funext hall
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (u i) (u i) 1 1 (hu i) (hu i)).2.2.2

end GlobalTheory.AvgRestr
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinChar

theorem norm_coeff_le_of_mem_ell (E : Type) [Field E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (τ : E →+* ℂ) (k : ℕ) :
    ‖τ (P.coeff k)‖ ≤ (2 : ℝ) ^ n := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) k hm (IsAlgClosed.splits _) (fun z hz => (hr τ z hz).le)
  rw [Polynomial.coeff_map, one_pow, one_mul, hd] at h
  exact h.trans (by exact_mod_cast Nat.choose_le_two_pow n k)

theorem finite_ell_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w (n := n)) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ n S hS C hC hK
  set T := {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P} with hT
  choose σ hσ using fun w => (hS w).exists
  choose B hB using fun w => GlobalTheory.T.charpoly_coeffs_valued_bounded_on_compact_GL E n w (C w) (hC w)
  have loc : ∀ P ∈ T, ∀ u ∈ S, (∀ k, u.valuation E (P.coeff k) ≤ B u) ∧ u.valuation E (P.coeff 0)⁻¹ ≤ B u ∧
      (C u ⊆ GlobalTheory.LFun.KGL u (n := n) → (∀ k, u.valuation E (P.coeff k) ≤ 1) ∧ u.valuation E (P.coeff 0) = 1) := by
    intro P hP u hu
    obtain ⟨g, hg, hgP⟩ := hP.2 u hu
    have e : ∀ k, u.valuation E (P.coeff k) = Valued.v (g.val.charpoly.coeff k) := fun k => by
      rw [hgP, Polynomial.coeff_map]; exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).symm
    refine ⟨fun k => (e k).trans_le ((hB u g hg).1 k), ?_, fun hsub => ?_⟩
    · rw [map_inv₀, e, ← map_inv₀]; exact (hB u g hg).2
    · have := GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact E n u g (hsub hg)
      exact ⟨fun k => (e k).trans_le (this.1 k), (e 0).trans this.2⟩
  have glob : ∀ P ∈ T, ∀ w : Pl E, ∀ k, w.valuation E (P.coeff k) ≤ max (B (σ w)) (B (σ w) * B (σ w)) ∧
      (C (σ w) ⊆ GlobalTheory.LFun.KGL (σ w) (n := n) → w.valuation E (P.coeff k) ≤ 1) := by
    intro P hP w k
    have hu := loc P hP (σ w) (hσ w).1
    obtain ⟨h0, hc⟩ := GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff E n P hP.1
    rcases GlobalTheory.T.valuation_eq_or_conj_of_under_maximalRealSubfield_eq E w (σ w) (hσ w).2 with h | h
    · rw [h]
      exact ⟨(hu.1 k).trans (le_max_left _ _), fun hs => (hu.2.2 hs).1 k⟩
    · rw [h]
      by_cases hk : k ≤ n
      · have e : IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) * (P.coeff 0)⁻¹ := by
          rw [← hc k hk]; field_simp
        rw [e, map_mul]
        refine ⟨(mul_le_mul' (hu.1 _) hu.2.1).trans (le_max_right _ _), fun hs => ?_⟩
        rw [map_inv₀, (hu.2.2 hs).2, inv_one, mul_one]; exact (hu.2.2 hs).1 _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega), map_zero, map_zero]
        exact ⟨zero_le', fun _ => zero_le'⟩
  set A := {x : E | ∃ P ∈ T, ∃ k, P.coeff k = x} with hA
  have hAfin : A.Finite := by
    refine GlobalTheory.T.finite_of_bounded_embeddings_and_valuations E A ((2 : ℝ) ^ n) ?_ ?_ ?_
    · rintro _ ⟨P, hP, k, rfl⟩ τ; exact norm_coeff_le_of_mem_ell E n P hP.1 τ k
    · intro w; exact ⟨_, by rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).1⟩
    · have hbad : {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u (n := n)}.Finite := Filter.eventually_cofinite.1 hK
      have : {w : Pl E | ¬ ∀ x ∈ A, w.valuation E x ≤ 1} ⊆ ⋃ u ∈ {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u (n := n)},
          {w : Pl E | w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))} := by
        intro w hw
        simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hw ⊢
        refine ⟨σ w, fun hs => hw ?_, (hσ w).2.symm⟩
        rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).2 hs
      refine Filter.eventually_cofinite.2 (Set.Finite.subset (hbad.biUnion fun u _ => ?_) this)
      exact ((IsDedekindDomain.primesOver_finite (u.under (𝓞 (maximalRealSubfield E))).asIdeal (𝓞 E)).preimage
        (fun a _ b _ h => HeightOneSpectrum.ext h)).subset fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Set.Finite.of_finite_image (f := fun P : E[X] => fun k : Fin (n + 1) => P.coeff k) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : Fin (n + 1) => A) fun _ => hAfin).subset ?_
    rintro _ ⟨P, hP, rfl⟩ k _
    exact ⟨P, hP, k, rfl⟩
  · intro P hP Q hQ h
    ext k
    by_cases hk : k ≤ n
    · exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.FinChar
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryLocalSign_eq_one_of_integral_separable_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    γ ∈ KL n w → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → kapSign n w Q₁ γ.1 = 1 := by
  first | exact @GlobalTheory.BCT.kapSign_eq_one_of_integral | exact GlobalTheory.BCT.kapSign_eq_one_of_integral | (intros; apply GlobalTheory.BCT.kapSign_eq_one_of_integral <;> assumption)
end
