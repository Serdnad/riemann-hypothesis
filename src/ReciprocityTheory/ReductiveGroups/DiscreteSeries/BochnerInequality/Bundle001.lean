module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Lemmata.SimultaneousEigenvectors.BlSimeig
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section PositionDegree

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

def slRest {k : ℕ} (i : Fin k) :
    (Fin k → Fin n × Fin n) ≃ (Fin n × Fin n) × ({j // j ≠ i} → Fin n × Fin n) :=
  Equiv.funSplitAt i _

def slt {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (A : Big n k M) : Big n 1 M :=
  WithLp.toLp 2 (fun ι : Fin 1 → Fin n × Fin n => A ((slRest i).symm (ι 0, r)))

theorem slRest_symm_self {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n) :
    (slRest i).symm (p, r) i = p := by
  simp [slRest, Equiv.funSplitAt_symm_apply]

theorem update_slRest_symm {k : ℕ} (i : Fin k) (p q : Fin n × Fin n)
    (r : {j // j ≠ i} → Fin n × Fin n) :
    Function.update ((slRest i).symm (p, r)) i q = (slRest i).symm (q, r) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [slRest, Equiv.funSplitAt_symm_apply]
  · simp [slRest, Equiv.funSplitAt_symm_apply, h]

theorem update_eq_slRest {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (q : Fin n × Fin n) :
    Function.update κ i q = (slRest i).symm (q, (slRest i κ).2) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [slRest, Equiv.funSplitAt_symm_apply]
  · simp [slRest, Equiv.funSplitAt_symm_apply, Equiv.funSplitAt_apply, h]

theorem slice_eq_slt {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (A : Big n k M) :
    slice i κ A = slt i (slRest i κ).2 A := by
  simp only [slice, slt, update_eq_slRest]

theorem slt_sum_fin_one_fun {β : Type*} [AddCommMonoid β] (f : (Fin n × Fin n) → β) :
    ∑ ι : Fin 1 → Fin n × Fin n, f (ι 0) = ∑ p, f p := by
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun ι => by simp)

theorem slt_inner_eq_sum {k : ℕ} (i : Fin k) (A B : Big n k M) :
    inner ℂ A B = ∑ r, inner ℂ (slt i r A) (slt i r B) := by
  rw [PiLp.inner_apply, ← (slRest i).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [PiLp.inner_apply]
  exact (slt_sum_fin_one_fun
    (fun p => inner ℂ (A ((slRest i).symm (p, r))) (B ((slRest i).symm (p, r))))).symm

theorem slt_ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    ofCoords k f x κ = f κ x := rfl

theorem slt_coord_apply (k : ℕ) (κ : Fin k → Fin n × Fin n) (F : Big n k M) :
    coord k κ F = F κ := rfl

theorem slt_mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem slt_positionAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  rw [factorAd, slt_ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> simp [slt_coord_apply]

theorem slt_crossOp_apply (k : ℕ) (i : Fin k) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    crossOp ε E k i F κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) -
        (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0)) := by
  rw [← slt_coord_apply k κ (crossOp ε E k i F)]

  simp only [crossOp, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [slt_coord_apply]
  change factorAd k i a b (mAct E k b a F) κ = _
  rw [slt_positionAd_apply, slt_mAct_apply, slt_mAct_apply]

private theorem slt_apply {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n)
    (A : Big n k M) (ι : Fin 1 → Fin n × Fin n) : slt i r A ι = A ((slRest i).symm (ι 0, r)) :=
  rfl

theorem slt_crossOp {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (A : Big n k M) :
    slt i r (crossOp ε E k i A) = crossOp ε E 1 0 (slt i r A) := by
  refine PiLp.ext fun ι => ?_
  rw [slt_apply, slt_crossOp_apply, slt_crossOp_apply, slRest_symm_self]
  simp only [update_slRest_symm, slt_apply, Function.update_self]

end PositionDegree

section PositionB

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem slt_mem_ncV_iff {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap, slt_coord_apply]

theorem slRest_symm_ne {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n)
    {j : Fin k} (h : j ≠ i) : (slRest i).symm (p, r) j = r ⟨j, h⟩ := by
  simp [slRest, Equiv.funSplitAt_symm_apply, h]

theorem slt_eq_slice {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (p : Fin n × Fin n)
    (A : Big n k M) : slt i r A = slice i ((slRest i).symm (p, r)) A := by
  simp only [slice_eq_slt, Equiv.apply_symm_apply]

theorem slt_big_one_eq_zero (he : IsEmpty (Fin n × Fin n)) (x : Big n 1 M) : x = 0 := by
  exact PiLp.ext fun ι => (he.false (ι 0)).elim

theorem slt_slice_mem_ncV {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slice i κ F ∈ ncV ε V 1 := by
  rw [slt_mem_ncV_iff] at hF ⊢
  intro ι
  have h := hF (Function.update κ i (ι 0))
  change F (Function.update κ i (ι 0)) ∈ _
  by_cases c : ∀ j : Fin 1, ε (ι j).1 ≠ ε (ι j).2
  · rw [if_pos c]
    split_ifs at h with c'
    · exact h
    · rw [Submodule.mem_bot] at h
      rw [h]
      exact V.zero_mem
  · rw [if_neg c]
    have c' : ¬ ∀ j, ε ((Function.update κ i (ι 0)) j).1 ≠ ε ((Function.update κ i (ι 0)) j).2 := by
      intro hall
      apply c
      intro j
      have hj := hall i
      rw [Function.update_self] at hj
      rwa [Subsingleton.elim j 0]
    rwa [if_neg c'] at h

theorem slt_mem_ncV {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slt i r F ∈ ncV ε V 1 := by
  by_cases he : IsEmpty (Fin n × Fin n)
  · rw [slt_big_one_eq_zero he (slt i r F)]
    exact Submodule.zero_mem _
  · rw [not_isEmpty_iff] at he
    obtain ⟨p⟩ := he
    rw [slt_eq_slice i r p]
    exact slt_slice_mem_ncV i _ hF

end PositionB

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KUnit

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

def IsKUnitary (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) : Prop :=
  ∀ a b, ε a = ε b → ∀ x y : X, inner ℂ (A a b x) y = inner ℂ x (A b a y)

theorem isKUnitary_of_isInfUnitary (hU : IsInfUnitary ε A) : IsKUnitary ε A := by
  intro a b h x y
  rw [hU a b x y]
  simp [adjSign, h]

theorem kUnit_diag_comm (hA : IsGlRep A) (a c : Fin n) (v : X) :
    A a a (A c c v) = A c c (A a a v) := by
  have h := LinearMap.congr_fun (hA a a c c) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  by_cases hac : a = c
  · subst hac; rfl
  · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
    exact h

theorem kUnit_weight_shift (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X} (hw : ∀ c, A c c w = (μ c : ℂ) • w)
    {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
  have h := LinearMap.congr_fun (hA c c a b) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
  by_cases hca : c = a
  · subst hca
    simp [hab, Ne.symm hab] at h ⊢
    linear_combination (norm := module) h
  · by_cases hcb : c = b
    · subst hcb
      simp [hca] at h ⊢
      linear_combination (norm := module) h
    · simp [hca, hcb, Ne.symm hcb] at h ⊢
      linear_combination (norm := module) h

theorem kUnit_exists_joint (hA : IsGlRep A) (s : Finset (Fin n)) :
    ∀ T : Submodule ℂ X, FiniteDimensional ℂ T → (∀ c, ∀ v ∈ T, A c c v ∈ T) → T ≠ ⊥ →
      ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  first | exact Bl.SimultaneousEigenvectors.goal1 .. | (apply Bl.SimultaneousEigenvectors.goal1 <;> assumption) | (intros; apply Bl.SimultaneousEigenvectors.goal1 <;> assumption)

theorem kUnit_eig_real (hU : IsKUnitary ε A) {c : Fin n} {w : X} (hw0 : w ≠ 0) {z : ℂ}
    (hw : A c c w = z • w) : z = ((z.re : ℝ) : ℂ) := by
  have h := hU c c rfl w w
  rw [hw, inner_smul_left, inner_smul_right] at h
  have hne : inner ℂ w w ≠ (0 : ℂ) := inner_self_ne_zero.mpr hw0
  have h2 : (starRingEnd ℂ) z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm

def kUnitWtLin (μ : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) * μ c

theorem kUnitWtLin_shift (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    kUnitWtLin μ < kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have h : kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      kUnitWtLin μ + ((n : ℝ) - ((a : ℕ) : ℝ)) - ((n : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [kUnitWtLin, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  linarith

theorem exists_khw (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := kUnit_exists_joint hA Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact kUnit_eig_real hU hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => kUnit_weight_shift hA hμ (ne_of_lt hab) c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))

theorem orthogonal_kStable (hU : IsKUnitary ε A) {S : Submodule ℂ X} (hS : IsKStableSub ε A S) :
    IsKStableSub ε A Sᗮ := by
  intro a b hab v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← hU b a hab.symm u v]
  exact hv _ (hS b a hab.symm u hu)

theorem starProjection_comm (hU : IsKUnitary ε A) {S : Submodule ℂ X} [S.HasOrthogonalProjection]
    (hS : IsKStableSub ε A S) {a b : Fin n} (hab : ε a = ε b) (x : X) :
    S.starProjection (A a b x) = A a b (S.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hS a b hab _ (Submodule.starProjection_apply_mem S x)
  · intro w hw
    rw [← map_sub]
    have h1 : x - S.starProjection x ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have h2 := orthogonal_kStable hU hS a b hab _ h1
    rw [Submodule.mem_orthogonal] at h2
    rw [inner_eq_zero_symm]
    exact h2 w hw

end KUnit

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section AlgGen

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}

end AlgGen

section Slots

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    (ofCoords k f x) κ = f κ x := rfl

theorem mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem factorAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  show (ofCoords k _ F) κ = _
  rw [ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> rfl

theorem mem_ncV_iff {k : ℕ} {F : Big n k M} : F ∈ ncV ε V k ↔
    ∀ κ : Fin k → Fin n × Fin n, ((∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ ∈ V) ∧
      ((¬ ∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ = 0) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  refine forall_congr' fun κ => ?_
  split_ifs with h <;> simp [h] <;> rfl

theorem factorAd_mem_ncV {k : ℕ} (i : Fin k) {a b : Fin n} (hab : ε a = ε b) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : factorAd k i a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  rcases hx : κ i with ⟨x, y⟩
  simp only [factorAd_apply, hx]
  constructor
  · intro hκ
    have hxy : ε x ≠ ε y := by simpa [hx] using hκ i
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs with h <;> try exact Submodule.zero_mem _
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [← hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
  · intro hκ
    push Not at hκ
    obtain ⟨j, hj⟩ := hκ
    have key : ∀ p : Fin n × Fin n, ε p.1 = ε p.2 → (¬ ∀ l, ε ((Function.update κ i p) l).1 ≠
        ε ((Function.update κ i p) l).2) := by
      intro p hp h
      by_cases hji : j = i
      · subst hji; exact h j (by simpa using hp)
      · exact h j (by rw [Function.update_of_ne hji]; exact hj)
    have hxy : j = i → ε x = ε y := by intro hji; subst hji; simpa [hx] using hj
    have hc : ∀ p : Fin n × Fin n, (j = i → ε p.1 = ε p.2) → F (Function.update κ i p) = 0 := by
      intro p hp
      by_cases hji : j = i
      · exact (hF _).2 (key p (hp hji))
      · refine (hF _).2 fun h => h j ?_
        rw [Function.update_of_ne hji]; exact hj
    rw [ite_eq_right_iff.2 ?_, ite_eq_right_iff.2 ?_, sub_zero]
    · intro h; subst h; exact hc _ fun hji => by show ε x = ε a; rw [hxy hji, ← hab]
    · intro h; subst h; exact hc _ fun hji => by show ε b = ε y; rw [← hab, hxy hji]

theorem mAct_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) {a b : Fin n} (hab : ε a = ε b)
    {F : Big n k M} (hF : F ∈ ncV ε V k) : mAct E k a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  simp only [mAct_apply]
  exact ⟨fun h => hV a b hab _ ((hF κ).1 h), fun h => by rw [(hF κ).2 h, map_zero]⟩

end Slots

end ReciprocityTheory.ChartRestriction.DS.BigCasimir
end
end
