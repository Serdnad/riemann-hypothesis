module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section TopNil

variable {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M]

def topNil (I : Ideal R) (T : κ → Module.End R M) : Submodule R M where
  carrier := {m | ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M)}
  add_mem' ha hb i j := ((ha i j).and (hb i j)).mono fun _ h => by
    rw [map_add]; exact add_mem h.1 h.2
  zero_mem' _ _ := Eventually.of_forall fun _ => by rw [map_zero]; exact zero_mem _
  smul_mem' c _ h i j := (h i j).mono fun _ h => by
    rw [map_smul]; exact Submodule.smul_mem _ c h

theorem mem_topNil {I : Ideal R} {T : κ → Module.End R M} {m : M} :
    m ∈ topNil I T ↔ ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M) := Iff.rfl

theorem mem_topNil_iff_exists {I : Ideal R} {T : κ → Module.End R M} {m : M} :
    m ∈ topNil I T ↔ ∀ i (j : ℕ), ∃ r : ℕ, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M) := by
  rw [mem_topNil]
  refine forall₂_congr fun i j => ⟨fun h => h.exists, fun ⟨r, hr⟩ => ?_⟩
  filter_upwards [eventually_ge_atTop r] with s hs
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [add_comm r t, pow_add, Module.End.mul_apply]
  have hle : (I ^ j • ⊤ : Submodule R M).map (T i ^ t) ≤ I ^ j • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨_, hr, rfl⟩

end TopNil

section Split

open Polynomial

variable {R : Type} [CommRing R] (P : R[X]) (n : ℕ)

def splitIdeal : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun k : ℕ =>
    (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) - P.map MvPolynomial.C).coeff k)

abbrev SplitAlg : Type := MvPolynomial (Fin n) R ⧸ splitIdeal P n

def SplitAlg.root (i : Fin n) : SplitAlg P n := Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem SplitAlg.prod_root :
    ∏ i : Fin n, (X - C (SplitAlg.root P n i)) = P.map (algebraMap R (SplitAlg P n)) := by
  have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) -
      P.map MvPolynomial.C).map (Ideal.Quotient.mk (splitIdeal P n)) = 0 := by
    ext k
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨k, rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero] at h2
  simp only [Polynomial.map_sub, map_X, map_C] at h2
  exact h2

def SplitAlg.lift {A : Type} [CommRing A] [Algebra R A] (a : Fin n → A)
    (h : ∏ i : Fin n, (X - C (a i)) = P.map (algebraMap R A)) : SplitAlg P n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval a) fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A))).2 ?_ hx
    rintro _ ⟨k, rfl⟩
    have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) - P.map MvPolynomial.C).map
        (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero]
      have h3 : (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom.comp MvPolynomial.C =
          algebraMap R A := RingHom.ext fun r => by simp
      rw [h3, ← h]
      simp
    have h4 := congrArg (fun q => q.coeff k) h2
    simp only [coeff_map, coeff_zero] at h4
    exact h4

theorem SplitAlg.lift_root {A : Type} [CommRing A] [Algebra R A] (a : Fin n → A)
    (h : ∏ i : Fin n, (X - C (a i)) = P.map (algebraMap R A)) (i : Fin n) :
    SplitAlg.lift P n a h (SplitAlg.root P n i) = a i := by
  show MvPolynomial.aeval a (MvPolynomial.X i) = a i
  exact MvPolynomial.aeval_X a i

theorem SplitAlg.hom_ext {A : Type} [CommRing A] [Algebra R A] {f g : SplitAlg P n →ₐ[R] A}
    (h : ∀ i, f (SplitAlg.root P n i) = g (SplitAlg.root P n i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

end Split

end UpperTheory.V.AlgebraTools
end
end

section

noncomputable section

open Polynomial

namespace UpperTheory.V.AlgebraTools

variable {R κ : Type} [CommRing R] (P : κ → R[X]) (n : ℕ)

def mSplitIdeal : Ideal (MvPolynomial (κ × Fin n) R) :=
  Ideal.span (Set.range fun jk : κ × ℕ =>
    (∏ i : Fin n, (X - C (MvPolynomial.X (jk.1, i) : MvPolynomial (κ × Fin n) R)) -
      (P jk.1).map MvPolynomial.C).coeff jk.2)

abbrev MSplitAlg : Type := MvPolynomial (κ × Fin n) R ⧸ mSplitIdeal P n

def MSplitAlg.root (j : κ) (i : Fin n) : MSplitAlg P n := Ideal.Quotient.mk _ (MvPolynomial.X (j, i))

theorem MSplitAlg.prod_root (j : κ) :
    ∏ i : Fin n, (X - C (MSplitAlg.root P n j i)) = (P j).map (algebraMap R (MSplitAlg P n)) := by
  have h : (∏ i : Fin n, (X - C (MvPolynomial.X (j, i) : MvPolynomial (κ × Fin n) R)) -
      (P j).map MvPolynomial.C).map (Ideal.Quotient.mk (mSplitIdeal P n)) = 0 := by
    ext k
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨(j, k), rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero] at h
  simp only [Polynomial.map_sub, map_X, map_C] at h
  exact h

def MSplitAlg.lift {A : Type} [CommRing A] [Algebra R A] (a : κ → Fin n → A)
    (h : ∀ j, ∏ i : Fin n, (X - C (a j i)) = (P j).map (algebraMap R A)) : MSplitAlg P n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2) fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker
      (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 : MvPolynomial (κ × Fin n) R →ₐ[R] A))).2 ?_ hx
    rintro _ ⟨⟨j, k⟩, rfl⟩
    have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X (j, i) : MvPolynomial (κ × Fin n) R)) -
        (P j).map MvPolynomial.C).map
        (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 : MvPolynomial (κ × Fin n) R →ₐ[R] A).toRingHom = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero]
      have h3 : (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 :
          MvPolynomial (κ × Fin n) R →ₐ[R] A).toRingHom.comp MvPolynomial.C = algebraMap R A :=
        RingHom.ext fun r => by simp
      rw [h3, ← h j]
      simp
    have h4 := congrArg (fun q => q.coeff k) h2
    simp only [coeff_map, coeff_zero] at h4
    exact h4

theorem MSplitAlg.lift_root {A : Type} [CommRing A] [Algebra R A] (a : κ → Fin n → A)
    (h : ∀ j, ∏ i : Fin n, (X - C (a j i)) = (P j).map (algebraMap R A)) (j : κ) (i : Fin n) :
    MSplitAlg.lift P n a h (MSplitAlg.root P n j i) = a j i :=
  MvPolynomial.aeval_X (fun p : κ × Fin n => a p.1 p.2) (j, i)

theorem MSplitAlg.hom_ext {A : Type} [CommRing A] [Algebra R A] {f g : MSplitAlg P n →ₐ[R] A}
    (h : ∀ j i, f (MSplitAlg.root P n j i) = g (MSplitAlg.root P n j i)) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun p => h p.1 p.2)

end UpperTheory.V.AlgebraTools
end
end

section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.der_inner :
    ∀ {K E : Type} [CommRing K] [Ring E] [Algebra K E] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (j : (∀ s, Matrix (d s) (d s) K) →ₐ[K] E) (D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E), (∀ x y, D (x * y) = D x * j y + j x * D y) → ∃ Y : E, ∀ x, D x = Y * j x - j x * Y := by
  intro K E _ _ _ σ _ _ d _ _ _ j D hD
  let i0 : ∀ s, d s := fun s => Classical.arbitrary (d s)
  let u : ∀ s, d s → d s → (∀ s, Matrix (d s) (d s) K) :=
    fun s p q => Pi.single s (Matrix.single p q (1 : K))
  have hsame : ∀ s (p q r w : d s), u s p q * u s r w = if q = r then u s p w else 0 := by
    intro s p q r w
    simp only [u, ← Pi.single_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]
  have hne : ∀ s t (p q : d s) (r w : d t), s ≠ t → u s p q * u t r w = 0 := by
    intro s t p q r w h
    funext x
    simp only [u, Pi.mul_apply, Pi.zero_apply]
    by_cases hx : x = s
    · subst hx
      rw [Pi.single_eq_of_ne h, mul_zero]
    · rw [Pi.single_eq_of_ne hx, zero_mul]
  have hone : ∑ s, ∑ k, u s k k = 1 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · rw [Finset.sum_apply]
      ext a b
      simp only [u, Pi.single_eq_same, Matrix.sum_apply, Matrix.single_apply, Pi.one_apply,
        Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Finset.sum_eq_zero fun k _ => if_neg fun h => hab (h.1.symm.trans h.2)]
        simp [hab]
    · intro s _ hs
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => Pi.single_eq_of_ne (Ne.symm hs) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  let a : E := ∑ s, ∑ k, j (u s k (i0 s)) * D (u s (i0 s) k)
  have key : ∀ t (p q : d t), D (u t p q) = j (u t p q) * a - a * j (u t p q) := by
    intro t p q
    have h1 : j (u t p q) * a = j (u t p (i0 t)) * D (u t (i0 t) q) := by
      simp only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single q]
        · rw [hsame, if_pos rfl]
        · intro k _ hk
          rw [hsame, if_neg (Ne.symm hk), map_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hne t s _ _ _ _ (Ne.symm hs), map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hS1 : ∑ s, ∑ k, j (u s k (i0 s)) * D (u s (i0 s) k * u t p q)
        = j (u t p (i0 t)) * D (u t (i0 t) q) := by
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single p]
        · rw [hsame, if_pos rfl]
        · intro k _ hk
          rw [hsame, if_neg hk, map_zero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hne s t _ _ _ _ hs, map_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hS2 : ∑ s, ∑ k, j (u s k (i0 s)) * j (u s (i0 s) k) = 1 := by
      simp only [← map_mul, hsame, eq_self_iff_true, if_true]

      simp only [← map_sum]
      rw [hone, map_one]
    have e : a * j (u t p q) = ∑ s, ∑ k, (j (u s k (i0 s)) * D (u s (i0 s) k * u t p q)
        - j (u s k (i0 s)) * j (u s (i0 s) k) * D (u t p q)) := by
      simp only [a, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hD]
      noncomm_ring
    rw [h1, e]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hS1, hS2, one_mul]
    abel
  refine ⟨-a, fun x => ?_⟩
  have hlin : D = (LinearMap.mulRight K a).comp j.toLinearMap
      - (LinearMap.mulLeft K a).comp j.toLinearMap := by
    refine (Pi.basis fun s => Matrix.stdBasis K (d s) (d s)).ext fun ji => ?_
    obtain ⟨t, p, q⟩ := ji
    rw [Pi.basis_apply, Matrix.stdBasis_eq_single]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
    exact key t p q
  have hx := LinearMap.congr_fun hlin x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply] at hx
  rw [hx]
  noncomm_ring
end

section

noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

variable (l : ℕ) (G : Type) [Group G] [TopologicalSpace G]

def IsProL : Prop := ∀ N : OpenNormalSubgroup G, IsPGroup l (G ⧸ N.toSubgroup)

theorem isProL_iff : IsProL l G ↔ ∀ (N : OpenNormalSubgroup G) (g : G), ∃ k : ℕ, g ^ l ^ k ∈ N.toSubgroup := by
  unfold IsProL
  refine forall_congr' fun N => ?_
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (g : G ⧸ N.toSubgroup)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

def proLRes : Subgroup G :=
  ⨅ N : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ N.toSubgroup)}, N.1.toSubgroup

variable {l G} in
theorem mem_proLRes {g : G} :
    g ∈ proLRes l G ↔ ∀ N : OpenNormalSubgroup G, IsPGroup l (G ⧸ N.toSubgroup) → g ∈ N.toSubgroup := by
  simp only [proLRes, Subgroup.mem_iInf, Subtype.forall]

theorem isClosed_proLRes [ContinuousMul G] : IsClosed (proLRes l G : Set G) := by
  rw [proLRes, Subgroup.coe_iInf]
  exact isClosed_iInter fun N => N.1.toOpenSubgroup.isClosed


variable {G} in
def proLResOf (H : Subgroup G) : Subgroup G := (proLRes l H).map H.subtype


variable {G} in
def TopGen (s : Set G) : Prop := Dense (Subgroup.closure s : Set G)

def TopFG : Prop := ∃ s : Set G, s.Finite ∧ TopGen s

variable {G} in
theorem topGen_iff [IsTopologicalGroup G] (s : Set G) :
    TopGen s ↔ (Subgroup.closure s).topologicalClosure = ⊤ := by
  rw [TopGen, dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, ← Subgroup.coe_top,
    SetLike.coe_set_eq]


variable {G} in
def limKer {ι : Type} (F : Filter ι) (K : ι → Subgroup G) : Subgroup G where
  carrier := {g | ∀ O : OpenNormalSubgroup G, ∀ᶠ i in F, g ∈ K i ⊔ O.toSubgroup}
  mul_mem' ha hb O := ((ha O).and (hb O)).mono fun _ h => mul_mem h.1 h.2
  one_mem' _ := Eventually.of_forall fun _ => one_mem _
  inv_mem' h O := (h O).mono fun _ h => inv_mem h

variable {G} in
theorem mem_limKer {ι : Type} {F : Filter ι} {K : ι → Subgroup G} {g : G} :
    g ∈ limKer F K ↔ ∀ O : OpenNormalSubgroup G, ∀ᶠ i in F, g ∈ K i ⊔ O.toSubgroup := Iff.rfl

variable {G} in
instance limKer_normal {ι : Type} (F : Filter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal] :
    (limKer F K).Normal :=
  ⟨fun _ h g O => (h O).mono fun i hi => by
    haveI := O.isNormal'
    exact (Subgroup.sup_normal (K i) O.toSubgroup).conj_mem _ hi g⟩

end UpperTheory.V.AlgebraTools
end
end

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.exists_unit_entry {R : Type} [CommRing R] [IsLocalRing R] {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    ∃ a b, IsUnit (e a b) := by
  classical
  by_contra h
  push_neg at h
  have hm : ∀ a b, e a b ∈ maximalIdeal R := fun a b => (mem_maximalIdeal _).2 (h a b)
  have hmap : (1 - e).map (residue R) = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [(residue_eq_zero_iff _).2 (hm a a)]
    · simp [Matrix.one_apply_ne hab, (residue_eq_zero_iff _).2 (hm a b)]
  have hdet : IsUnit (1 - e).det := by
    have h1 : residue R (1 - e).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, det_one]
    exact (isUnit_map_iff (residue R) _).1 (h1 ▸ isUnit_one)
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  apply h0
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  exact hu.mul_right_eq_zero.1 h2

theorem UpperTheory.V.AlgebraTools.coi_conj_single :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Matrix ι ι R), CompleteOrthogonalIdempotents f → (∀ i, f i ≠ 0) → ∃ g : GL ι R, ∀ i, (g : Matrix ι ι R) * f i * ((g⁻¹ : GL ι R) : Matrix ι ι R) = single i i 1 := by
  intro R _ _ ι _ _ f hf h0
  classical
  have hc : ∀ i, ∃ a b, IsUnit (f i a b) := fun i =>
    UpperTheory.V.AlgebraTools.exists_unit_entry (f i) (hf.idem i) (h0 i)
  choose a b hu using hc
  set P : Matrix ι ι R := Matrix.of fun k j => f j k (b j) with hP
  set Q : Matrix ι ι R := Matrix.of fun i k => ((hu i).unit⁻¹ : Rˣ) * f i (a i) k with hQ
  have hent : ∀ (M : Matrix ι ι R) (j k : ι),
      (Q * M * P) j k = ((hu j).unit⁻¹ : Rˣ) * (f j * M * f k) (a j) (b k) := by
    intro M j k
    simp only [hP, hQ, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hidem : ∀ i, f i * f i = f i := fun i => (hf.idem i).eq
  have hort : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => hf.ortho hij
  have hQP : Q * P = 1 := by
    ext j k
    have h1 := hent 1 j k
    simp only [Matrix.mul_one] at h1
    rw [h1]
    by_cases hjk : j = k
    · subst hjk
      rw [hidem, Matrix.one_apply_eq, IsUnit.val_inv_mul]
    · rw [hort j k hjk, Matrix.one_apply_ne hjk, Matrix.zero_apply, mul_zero]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  refine ⟨⟨Q, P, hQP, hPQ⟩, fun i => ?_⟩
  change Q * f i * P = single i i 1
  ext j k
  rw [hent, Matrix.single_apply]
  by_cases hji : i = j
  · subst hji
    by_cases hik : i = k
    · subst hik
      rw [hidem, hidem, IsUnit.val_inv_mul, if_pos ⟨rfl, rfl⟩]
    · rw [hidem, hort i k hik, Matrix.zero_apply, mul_zero, if_neg (fun h => hik h.2)]
  · rw [hort j i (Ne.symm hji), zero_mul, Matrix.zero_apply, mul_zero, if_neg (fun h => hji h.1)]
end

section

open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure IsCplAt (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B]
    [Algebra R B] : Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  comap_eq : (maximalIdeal B).comap (algebraMap R B) = p
  dense : ∀ (n : ℕ) (b : B), ∃ a s : R, s ∉ p ∧
    algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n
  strict : ∀ (n : ℕ) (a : R), algebraMap R B a ∈ maximalIdeal B ^ n → ∃ s : R, s ∉ p ∧ s * a ∈ p ^ n

theorem IsCplAt.isPrime {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) : p.IsPrime := by
  rw [← h.comap_eq]
  exact Ideal.comap_isPrime _ _

abbrev CplAt (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] : Type :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)

end UpperTheory.V.AlgebraTools
end
