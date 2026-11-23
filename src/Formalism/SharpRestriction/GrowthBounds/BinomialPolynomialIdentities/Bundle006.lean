module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ContragredientIrreducibleGeneratedByHighestWeigh
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DividedPowerReverseDividedPowerEqSelf
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.HighestWeightSpaceEqSpanHighestWeightVector
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.FormalSeriesConditionsB1ToB4
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

theorem span_inter_eq_span_image {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    {σ X : Type} (bO : X → MvPolynomial σ O) (bK : X → MvPolynomial σ Kf)
    (hmap : ∀ x, MvPolynomial.map (algebraMap O Kf) (bO x) = bK x) (hLI : LinearIndependent Kf bK)
    (Y : Submodule Kf (MvPolynomial σ Kf)) (A : Set X)
    (hY : Submodule.span Kf (Set.range bK) ⊓ Y = Submodule.span Kf (bK '' A)) :
    {f | f ∈ Submodule.span O (Set.range bO) ∧ MvPolynomial.map (algebraMap O Kf) f ∈ Y} =
      (Submodule.span O (bO '' A) : Set _) := by
  classical
  have hmaplc : ∀ c : X →₀ O, MvPolynomial.map (algebraMap O Kf) (Finsupp.linearCombination O bO c) =
      Finsupp.linearCombination Kf bK (c.mapRange (algebraMap O Kf) (map_zero _)) := by
    intro c

    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (by intro i; exact zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hmap, ← MvPolynomial.smul_eq_C_mul]
  ext G
  constructor
  · rintro ⟨hG, hGY⟩
    obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hG
    change (c.sum fun x a => a • bO x) ∈ Submodule.span O (bO '' A)
    refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)
    have h1 : MvPolynomial.map (algebraMap O Kf) (Finsupp.linearCombination O bO c) ∈
        Submodule.span Kf (bK '' A) := by
      rw [← hY]
      refine ⟨?_, hGY⟩
      rw [hmaplc]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩
    obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination Kf).1 h1
    rw [hmaplc] at hle
    have hlc := hLI hle
    have hxl : x ∈ l.support := by
      rw [hlc, Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      intro h0
      exact (Finsupp.mem_support_iff.1 hx) (hinj (by rw [h0, map_zero]))
    exact (Finsupp.mem_supported Kf l).1 hl hxl
  · intro hG
    change G ∈ Submodule.span O (bO '' A) at hG
    induction hG using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
      rw [hmap]
      have : bK x ∈ Submodule.span Kf (Set.range bK) ⊓ Y := by
        rw [hY]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      exact this.2
    | zero => exact ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨Submodule.add_mem _ hx.1 hy.1, by rw [map_add (f := _)]; exact Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx =>
      exact ⟨Submodule.smul_mem _ _ hx.1, by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
        exact Submodule.smul_mem _ _ hx.2⟩

abbrev GLWeightLabels (N r K : ℕ) : Fin (N + 1) ⊕ Fin (N + 1) → Type
  | .inl _ => Fin r → ℤ
  | .inr _ => Fin K → ℤ

structure ExternalProductHyps : Prop where
  p16 : ExternalProductBasis
  e1 : GlOperatorsFormRepresentation
  e2 : IsotypicZeroOfNonDominant
  e3 : ProjectorsPreserveMultidegree
  e5a : ProjectorsCommuteNested
  e5b : ProjectorsCommuteDisjoint
  lowPl : RestLowPl
  lowTan : RestLowTan
  sum : RestJointSum

section

variable (D : Formalism.BasicNotions.D7) (H : ExternalProductHyps) {F : Type} [Field F] [CharZero F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N))
  (B : Fin N → ℕ)

include D H in
theorem exists_decSys_isoSub_glOpsE_of_injective {m k : ℕ} (S : Set (Fin N)) (e : Fin m → Fin k) (he : Function.Injective e) :
    ∃ pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F), DecSys (isoSub (glOpsE F LL S e)) pr :=
  isoDecomp (glOpsE F LL S e) D (weight_condition_from_integral_form D) (H.e1 F N m k LL S e he)

abbrev EPl (F : Type) [Field F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (i : Fin (N + 1)) :
    GLOps r F (MvPolynomial (Fin N × Fin (r + K)) F) := glOpsE F LL {j | j.val < i.val} (Fin.castAdd K)

abbrev ETan (F : Type) [Field F] {N : ℕ} (r K : ℕ) (LL : Letters (Fin N)) (i : Fin (N + 1)) :
    GLOps K F (MvPolynomial (Fin N × Fin (r + K)) F) := glOpsE F LL {j | j.val < i.val} (Fin.natAdd r)

def prPl (i : Fin (N + 1)) : (Fin r → ℤ) → Module.End F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  Classical.choose (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.castAdd K) (Fin.castAdd_injective r K))

def prTan (i : Fin (N + 1)) : (Fin K → ℤ) → Module.End F (MvPolynomial (Fin N × Fin (r + K)) F) :=
  Classical.choose (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.natAdd r) (Fin.natAdd_injective K r))

theorem prPl_sys (i : Fin (N + 1)) : DecSys (isoSub (EPl F r K LL i)) (prPl D H r K LL i) :=
  Classical.choose_spec (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.castAdd K) (Fin.castAdd_injective r K))

theorem prTan_sys (i : Fin (N + 1)) : DecSys (isoSub (ETan F r K LL i)) (prTan D H r K LL i) :=
  Classical.choose_spec (exists_decSys_isoSub_glOpsE_of_injective (F := F) D H LL {j | j.val < i.val} (Fin.natAdd r) (Fin.natAdd_injective K r))

theorem initialSegments_nested (i j : Fin (N + 1)) :
    ({l : Fin N | l.val < i.val} ⊆ {l : Fin N | l.val < j.val}) ∨
      ({l : Fin N | l.val < j.val} ⊆ {l : Fin N | l.val < i.val}) := by
  rcases le_total i j with h | h
  · exact Or.inl fun l (hl : l.val < i.val) => lt_of_lt_of_le hl h
  · exact Or.inr fun l (hl : l.val < j.val) => lt_of_lt_of_le hl h

theorem fin_castAdd_ne_natAdd (a : Fin r) (b : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r b := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

def externalProductJointData : JointData F (MvPolynomial (Fin N × Fin (r + K)) F) (Fin (N + 1) ⊕ Fin (N + 1)) (GLWeightLabels N r K)
    (PIdx r K LL B) where
  le := fun s => match s with
    | .inl _ => DomLE
    | .inr _ => DomLE
  dom := fun s => match s with
    | .inl _ => Dominant
    | .inr _ => Dominant
  le_refl := fun s => match s with
    | .inl _ => fun a => dominance_refl a
    | .inr _ => fun a => dominance_refl a
  le_trans := fun s => match s with
    | .inl _ => fun _ _ _ h1 h2 => dominance_trans h1 h2
    | .inr _ => fun _ _ _ h1 h2 => dominance_trans h1 h2
  le_antisymm := fun s => match s with
    | .inl _ => fun _ _ h1 h2 => dominance_antisymm h1 h2
    | .inr _ => fun _ _ h1 h2 => dominance_antisymm h1 h2
  W := fun s => match s with
    | .inl i => isoSub (EPl F r K LL i)
    | .inr i => isoSub (ETan F r K LL i)
  e := fun s => match s with
    | .inl i => prPl D H r K LL i
    | .inr i => prTan D H r K LL i
  sys := fun s => match s with
    | .inl i => prPl_sys D H r K LL i
    | .inr i => prTan_sys D H r K LL i
  comm := fun s t => match s, t with
    | .inl i, .inl j => fun a b => H.e5a F N r (r + K) LL _ _ _ (Fin.castAdd_injective r K) (initialSegments_nested i j) _ _
        (prPl_sys D H r K LL i) (prPl_sys D H r K LL j) a b
    | .inr i, .inr j => fun a b => H.e5a F N K (r + K) LL _ _ _ (Fin.natAdd_injective K r) (initialSegments_nested i j) _ _
        (prTan_sys D H r K LL i) (prTan_sys D H r K LL j) a b
    | .inl i, .inr j => fun a b => H.e5b F N r K (r + K) LL _ _ _ _ (Fin.castAdd_injective r K)
        (Fin.natAdd_injective K r) (fin_castAdd_ne_natAdd r K) _ _ (prPl_sys D H r K LL i) (prTan_sys D H r K LL j) a b
    | .inr i, .inl j => fun a b => (H.e5b F N r K (r + K) LL _ _ _ _ (Fin.castAdd_injective r K)
        (Fin.natAdd_injective K r) (fin_castAdd_ne_natAdd r K) _ _ (prPl_sys D H r K LL j) (prTan_sys D H r K LL i) b a).symm
  bot := fun s => match s with
    | .inl i => fun a h => H.e2 F N r (r + K) LL _ _ (Fin.castAdd_injective r K) a h
    | .inr i => fun a h => H.e2 F N K (r + K) LL _ _ (Fin.natAdd_injective K r) a h
  Pl := Pol F (r + K) B
  stab := fun s => match s with
    | .inl i => fun a x hx => H.e3 F N r (r + K) LL _ _ (Fin.castAdd_injective r K) _ (prPl_sys D H r K LL i) B a x hx
    | .inr i => fun a x hx => H.e3 F N K (r + K) LL _ _ (Fin.natAdd_injective K r) _ (prTan_sys D H r K LL i) B a x hx
  b := pvec F r K LL B
  P := fun x s => match s with
    | .inl i => x.1.1.1 i
    | .inr i => x.1.2.1 i
  Pdom := fun x s => match s with
    | .inl i => by
        obtain ⟨_, _, _, ⟨P1, h1⟩, _⟩ := x.2.1
        exact h1 ▸ P1.dom i
    | .inr i => by
        obtain ⟨_, _, _, _, ⟨P2, h2⟩⟩ := x.2.1
        exact h2 ▸ P2.dom i
  li := (H.p16 F N r K LL B).1
  span := (H.p16 F N r K LL B).2
  low := fun s => match s with
    | .inl i => fun pi h1 h2 => H.lowPl F N r K LL B i pi ⟨h1, h2⟩
    | .inr i => fun pi h1 h2 => H.lowTan F N r K LL B i pi ⟨h1, h2⟩

end

end Formalism.MainNotions.G.ColumnFamilies
end
end

section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem lattice_generated_lowest_weight (D : Formalism.BasicNotions.D7) : DeltaGeneratedByLowestWeightVector := deltaGenerated_of_extremalVector_of_dualInjective lowest_weight_extremal_vector (dualFunctional_lowestWeight_injective D)

theorem lattice_nabla_eq (D : Formalism.BasicNotions.D7) : NablaContragredientEqDualLatticeDelta := nablaDualLattice_of_irreducible_lowest_generated (contragredientIrreducible_generated D) (dualFunctional_lowestWeight_injective D) (lattice_generated_lowest_weight D)

theorem admissible_lattice_biduality (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.WeylDualityLattice D :=
  weylDualityLattice_of_nabla_fg_bidual D (lattice_nabla_eq D) (contragredientLatticeFG_of_irreducible (contragredientIrreducible_generated D)) integral_lattice_bidual

end Formalism.MainNotions.G.ColumnFamilies
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

section

variable {R : Type} [CommRing R] {N r K : ℕ}

theorem multideg_mapDomain_headVar (m : Fin N × Fin r →₀ ℕ) (i : Fin N) :
    multideg (m.mapDomain (plVar (K := K))) i = multideg m i := by
  classical
  unfold multideg
  rw [Fin.sum_univ_add]
  have h1 : ∀ c : Fin r, (m.mapDomain (plVar (K := K))) (i, Fin.castAdd K c) = m (i, c) := by
    intro c
    have : (i, Fin.castAdd K c) = plVar (K := K) (i, c) := rfl
    rw [this, Finsupp.mapDomain_apply_of_injective (by
      intro a b h
      simp only [plVar, Prod.mk.injEq] at h
      exact Prod.ext h.1 (Fin.castAdd_injective r K h.2))]
  have h2 : ∀ c : Fin K, (m.mapDomain (plVar (K := K))) (i, Fin.natAdd r c) = 0 := by
    intro c
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨l, a⟩, h⟩
    simp only [plVar, Prod.mk.injEq] at h
    have := congrArg Fin.val h.2
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

theorem multideg_mapDomain_tailVar (m : Fin N × Fin K →₀ ℕ) (i : Fin N) :
    multideg (m.mapDomain (tanVar (r := r))) i = multideg m i := by
  classical
  unfold multideg
  rw [Fin.sum_univ_add]
  have h1 : ∀ c : Fin K, (m.mapDomain (tanVar (r := r))) (i, Fin.natAdd r c) = m (i, c) := by
    intro c
    have : (i, Fin.natAdd r c) = tanVar (r := r) (i, c) := rfl
    rw [this, Finsupp.mapDomain_apply_of_injective (by
      intro a b h
      simp only [tanVar, Prod.mk.injEq] at h
      exact Prod.ext h.1 (Fin.natAdd_injective K r h.2))]
  have h2 : ∀ c : Fin r, (m.mapDomain (tanVar (r := r))) (i, Fin.castAdd K c) = 0 := by
    intro c
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨l, a⟩, h⟩
    simp only [tanVar, Prod.mk.injEq] at h
    have := congrArg Fin.val h.2
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  simp only [h1, h2, Finset.sum_const_zero, zero_add]

theorem multideg_add_apply {n : ℕ} (x y : Fin N × Fin n →₀ ℕ) (i : Fin N) :
    multideg (x + y) i = multideg x i + multideg y i := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

theorem rename_mul_rename_mem_multihomogeneous {b' b'' B : Fin N → ℕ} (hb : ∀ i, b' i + b'' i = B i) {G1 : MvPolynomial (Fin N × Fin r) R}
    {G2 : MvPolynomial (Fin N × Fin K) R} (h1 : G1 ∈ Pol R r b') (h2 : G2 ∈ Pol R K b'') :
    rename (plVar (K := K)) G1 * rename (tanVar (r := r)) G2 ∈ Pol R (r + K) B := by
  classical
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at h1 h2 ⊢
  intro m hm
  have hm' := MvPolynomial.support_mul _ _ (Finset.mem_coe.1 hm)
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.1 hm'
  have g1 := MvPolynomial.support_rename_of_injective (p := G1) (f := plVar (K := K)) (by
    intro a b h
    simp only [plVar, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective r K h.2))
  have g2 := MvPolynomial.support_rename_of_injective (p := G2) (f := tanVar (r := r)) (by
    intro a b h
    simp only [tanVar, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective K r h.2))
  rw [g1] at hm1
  rw [g2] at hm2
  obtain ⟨n1, hn1, rfl⟩ := Finset.mem_image.1 hm1
  obtain ⟨n2, hn2, rfl⟩ := Finset.mem_image.1 hm2
  intro i
  rw [multideg_add_apply, multideg_mapDomain_headVar, multideg_mapDomain_tailVar, h1 (Finset.mem_coe.2 hn1) i, h2 (Finset.mem_coe.2 hn2) i, hb i]

end

theorem productBasis_mem_multihomogeneous (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (x : PIdx r K LL B) : pvec R r K LL B x ∈ Pol R (r + K) B := by
  obtain ⟨b', b'', hb, ⟨P1, h1⟩, ⟨P2, h2⟩⟩ := x.2.1
  unfold pvec PsiPl PsiTan
  refine rename_mul_rename_mem_multihomogeneous hb ?_ ?_
  · rw [← h1]
    exact standardWord_mem_multihomogeneous R P1 _ (h1 ▸ x.2.2.1)
  · rw [← h2]
    exact standardWord_mem_multihomogeneous R P2 _ (h2 ▸ x.2.2.2)

theorem rename_mul_rename_mem_span_productBasis (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ)
    {b' b'' : Fin N → ℕ} (hb : ∀ i, b' i + b'' i = B i) {G1 : MvPolynomial (Fin N × Fin r) R}
    {G2 : MvPolynomial (Fin N × Fin K) R} (h1 : G1 ∈ Pol R r b') (h2 : G2 ∈ Pol R K b'') :
    rename (plVar (K := K)) G1 * rename (tanVar (r := r)) G2 ∈ Submodule.span R (Set.range (pvec R r K LL B)) := by
  rw [← (standardPath_basis_any_ring R N r LL b').2] at h1
  rw [← (standardPath_basis_any_ring R N K LL b'').2] at h2
  induction h1 using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨P1, I', hI', rfl⟩ := hy
    induction h2 using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨P2, I'', hI'', rfl⟩ := hz
      exact Submodule.subset_span
        ⟨⟨((P1.mu, I'), (P2.mu, I'')), ⟨b', b'', hb, ⟨P1, rfl⟩, ⟨P2, rfl⟩⟩, hI', hI''⟩, rfl⟩
    | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _), mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul, mul_smul_comm]; exact Submodule.smul_mem _ _ ha
  | zero => rw [map_zero, zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _), add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

theorem headVar_injective (N r K : ℕ) : Function.Injective (plVar (N := N) (r := r) (K := K)) := by
  intro a b h
  simp only [plVar, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castAdd_injective r K h.2)

theorem tailVar_injective (N r K : ℕ) : Function.Injective (tanVar (N := N) (r := r) (K := K)) := by
  intro a b h
  simp only [tanVar, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.natAdd_injective K r h.2)

theorem finsupp_eq_head_add_tail {N r K : ℕ} (m : Fin N × Fin (r + K) →₀ ℕ) :
    m = (m.comapDomain plVar (headVar_injective N r K).injOn).mapDomain plVar +
      (m.comapDomain tanVar (tailVar_injective N r K).injOn).mapDomain tanVar := by
  classical
  ext ⟨i, c⟩
  rw [Finsupp.add_apply]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) c
  · have e1 : (i, Fin.castAdd K a) = plVar (K := K) (i, a) := rfl
    rw [e1, Finsupp.mapDomain_apply_of_injective (headVar_injective N r K), Finsupp.comapDomain_apply,
      Finsupp.mapDomain_of_notMem_range, add_zero]
    rintro ⟨⟨l, b⟩, h⟩
    simp only [tanVar, plVar, Prod.mk.injEq] at h
    have := congrArg Fin.val h.2
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  · have e1 : (i, Fin.natAdd r a) = tanVar (r := r) (i, a) := rfl
    rw [e1, Finsupp.mapDomain_apply_of_injective (tailVar_injective N r K), Finsupp.comapDomain_apply,
      Finsupp.mapDomain_of_notMem_range, zero_add]
    rintro ⟨⟨l, b⟩, h⟩
    simp only [tanVar, plVar, Prod.mk.injEq] at h
    have := congrArg Fin.val h.2
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega

theorem monomial_mem_multihomogeneous_multideg (R : Type) [CommRing R] {N n : ℕ} (m : Fin N × Fin n →₀ ℕ) :
    monomial m (1 : R) ∈ Pol R n (fun i => multideg m i) := by
  classical
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro m' hm'
  have := MvPolynomial.support_monomial_subset (Finset.mem_coe.1 hm')
  rw [Finset.mem_singleton] at this
  subst this
  intro i
  rfl

theorem span_productBasis_eq_multihomogeneous (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    Submodule.span R (Set.range (pvec R r K LL B)) = Pol R (r + K) B := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact productBasis_mem_multihomogeneous R N r K LL B x
  · intro G hG
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hG
    rw [G.as_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hB := hG (Finset.mem_coe.2 hm)
    set m1 := m.comapDomain plVar (headVar_injective N r K).injOn with hm1
    set m2 := m.comapDomain tanVar (tailVar_injective N r K).injOn with hm2
    have hs : m = m1.mapDomain plVar + m2.mapDomain tanVar := finsupp_eq_head_add_tail m
    have hmon : monomial m (AddMonoidAlgebra.coeff G m) = AddMonoidAlgebra.coeff G m •
        (rename (plVar (K := K)) (monomial m1 (1 : R)) * rename (tanVar (r := r)) (monomial m2 (1 : R))) := by
      rw [rename_monomial, rename_monomial, monomial_mul, ← hs, smul_monomial, one_mul, smul_eq_mul, mul_one]
    rw [hmon]
    refine Submodule.smul_mem _ _ (rename_mul_rename_mem_span_productBasis R N r K LL B (b' := fun i => multideg m1 i)
      (b'' := fun i => multideg m2 i) ?_ (monomial_mem_multihomogeneous_multideg R m1) (monomial_mem_multihomogeneous_multideg R m2))
    intro i
    have := hB i
    rw [hs, multideg_add_apply, multideg_mapDomain_headVar, multideg_mapDomain_tailVar] at this
    exact this

end Formalism.MainNotions.G.ColumnFamilies
end
end
