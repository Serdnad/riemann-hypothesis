module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockbLemmas
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem applyWord_hw_mem_dualWeyl
    (h1 : HWMem) (h2 : RowDivStable)
    (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∀ w : List (Fin r × Fin r × ℕ),
      applyWord R w (hw R hn ν) ∈ dualWeyl R r n ν := fun
  | [] => h1 R r n hn ν hν
  | x :: w => h2 R r n ν x.1 x.2.1 x.2.2 _
      (applyWord_hw_mem_dualWeyl h1 h2 R r n hn ν hν w)

theorem weylLeDual_of (h1 : HWMem) (h2 : RowDivStable) : WeylLeDual := by
  intro R _ r n hn ν hν
  show Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) =>
      applyWord R w (hw R hn ν)) ≤ dualWeyl R r n ν
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact applyWord_hw_mem_dualWeyl h1 h2 R r n hn ν hν w

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem mem_dualWeyl_iff {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔
      IsWeightedHomogeneous (colW r n) f ν ∧
        ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  unfold dualWeyl
  simp only [Submodule.mem_inf, mem_weightedHomogeneousSubmodule, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]

theorem dualWeyl_mul {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ dualWeyl R r n ν) (hg : g ∈ dualWeyl R r n μ) :
    f * g ∈ dualWeyl R r n (ν + μ) := by
  rw [mem_dualWeyl_iff] at *
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

theorem one_mem_dualWeyl {R : Type*} [CommRing R] {r n : ℕ} :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  rw [mem_dualWeyl_iff]
  refine ⟨isWeightedHomogeneous_one _ _, fun l j _ => ?_⟩
  rw [map_one, map_one]

theorem dualWeyl_pow {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (k : ℕ) :
    f ^ k ∈ dualWeyl R r n (k • ν) := by
  induction k with
  | zero => simpa using (one_mem_dualWeyl (R := R) (r := r) (n := n))
  | succ k ih => rw [pow_succ, succ_nsmul]; exact dualWeyl_mul ih hf

theorem dualWeyl_prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (ν : ι → Fin n → ℕ) (f : ι → MvPolynomial (Fin r × Fin n) R)
    (hf : ∀ i ∈ s, f i ∈ dualWeyl R r n (ν i)) :
    (∏ i ∈ s, f i) ∈ dualWeyl R r n (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one_mem_dualWeyl (R := R) (r := r) (n := n))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact dualWeyl_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem dualWeyl_of_eq {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (h : ν = μ) :
    f ∈ dualWeyl R r n μ := h ▸ hf

end Formalism.GradedWeylDivisibility
end
end

section

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

def idPoint (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → R :=
  fun v => if v.1.val = v.2.val then 1 else 0

theorem eval_idPoint_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r)
    (hn : s ≤ n) : eval (idPoint R r n) (lpMinor R s hr hn) = 1 := by
  unfold lpMinor
  rw [RingHom.map_det]
  convert Matrix.det_one (R := R) (n := Fin s)
  ext p q
  simp [RingHom.mapMatrix_apply, idPoint, Matrix.one_apply]
  exact if_congr Fin.val_inj rfl rfl

theorem hwrow_sum_single_castLE {r s : ℕ} (hr : s ≤ r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      fun a => if a.val < s then 1 else 0 := by
  have h1 : (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      ∑ q : Fin s, (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ) :=
    Equiv.sum_comp σ (fun q => (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ))
  rw [h1]
  funext a
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · exact if_pos (Fin.ext rfl)
    · intro b _ hb
      rw [if_neg]
      intro hab
      subst hab
      exact hb (Fin.ext rfl)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hab
    subst hab
    exact h b.isLt

theorem lpMinor_rowHom (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (lpMinor R s hr hn)
      (fun a => if a.val < s then 1 else 0) := by
  unfold lpMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hk : IsWeightedHomogeneous (rowW r n)
      (∏ i, (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) (σ i) i)
      (fun a : Fin r => if a.val < s then 1 else 0) := by
    rw [← hwrow_sum_single_castLE hr σ]
    apply IsWeightedHomogeneous.prod
    intro i _
    simp only [Matrix.of_apply]
    exact isWeightedHomogeneous_X R (rowW r n) _
  rw [← mem_weightedHomogeneousSubmodule] at hk ⊢
  rw [Units.smul_def]
  exact zsmul_mem hk _

end Formalism.GradedWeylDivisibility
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lsat_mem_dualWeyl {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]

theorem lsat_map_colAddGen {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (colAddGen R l j f) = colAddGen S l j (map φ f) := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [colAddGen]
  next p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  next p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [colAddGen, aeval_X]
    split_ifs <;> simp

theorem lsat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] (w : σ → M) (m : M) (f : MvPolynomial σ R)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (map φ f) m := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem rowDiv_add_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add (f := _), Polynomial.coeff_add]

private theorem rowDiv_smul_fock_space_tableaux (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (c : R) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

theorem weylModuleRowDividedPowerStable : WeylRowDivStable := by
  unfold WeylRowDivStable
  intro R _ r n hn ν a b k f hf
  let L : MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R :=
    { toFun := rowDiv R a b k
      map_add' := rowDiv_add_fock_space_tableaux R a b k
      map_smul' := rowDiv_smul_fock_space_tableaux R a b k }
  have key : weyl R r n hn ν ≤ (weyl R r n hn ν).comap L := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  exact key hf

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleRowGraded : DualWeylRowGraded := by
  classical
  intro R _ r n ν μ f hf
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨hcol, hadd⟩ := hf
  refine ⟨?_, fun l j hlj => ?_⟩
  · intro d hd
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with h
    · exact hcol hd
    · exact absurd rfl hd
  · let w' : Option (Fin r × Fin n) → (Fin r → ℕ) := fun o => Option.elim o 0 (rowW r n)
    have key : ∀ F : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R,
        (∀ v, IsWeightedHomogeneous w' (F v) (rowW r n v)) → ∀ φ : MvPolynomial (Fin r × Fin n) R,
        weightedHomogeneousComponent w' μ (aeval F φ) =
          aeval F (weightedHomogeneousComponent (rowW r n) μ φ) := by
      intro F hF φ
      refine MvPolynomial.induction_on' φ (fun u a => ?_) (fun p q hp hq => ?_)
      · have hm : IsWeightedHomogeneous w' (aeval F (monomial u a)) (Finsupp.weight (rowW r n) u) := by
          rw [aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, algebraMap_eq]
          have := (isWeightedHomogeneous_C w' a).mul
            (IsWeightedHomogeneous.prod u.support (fun i => F i ^ u i) (fun i => u i • rowW r n i)
              fun i _ => (hF i).pow (u i))
          rwa [zero_add] at this
        have hm0 : IsWeightedHomogeneous (rowW r n) (monomial u a) (Finsupp.weight (rowW r n) u) :=
          isWeightedHomogeneous_monomial _ _ _ rfl
        rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm),
          weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm0)]
        split_ifs <;> simp
      · simp only [map_add (f := _), hp, hq]
    let G : Fin r × Fin n → MvPolynomial (Option (Fin r × Fin n)) R := fun v =>
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)
    have hG : ∀ v, IsWeightedHomogeneous w' (G v) (rowW r n v) := by
      intro v
      simp only [G]
      split_ifs
      · refine (isWeightedHomogeneous_X R w' (some v)).add ?_
        have := (isWeightedHomogeneous_X R w' none).mul (isWeightedHomogeneous_X R w' (some (v.1, l)))
        rw [show w' none = 0 from rfl, zero_add] at this
        exact this
      · exact isWeightedHomogeneous_X R w' (some v)
    have hGs : ∀ v, IsWeightedHomogeneous w' ((fun v : Fin r × Fin n =>
        (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) v) (rowW r n v) :=
      fun v => isWeightedHomogeneous_X R w' (some v)
    have hA : colAddGen R (r := r) l j = aeval G := rfl
    have hB : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
        aeval (fun v : Fin r × Fin n => (X (some v) : MvPolynomial (Option (Fin r × Fin n)) R)) := by
      ext v; simp
    have h1 := hadd l j hlj
    rw [hA, hB] at h1 ⊢
    rw [← key G hG, ← key _ hGs, h1]

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerWeightOrthogonal_holds : FockWeightOrth := by
  intro σ M _ w μ μ' f g hne hf hg
  unfold Formalism.REAL.fockF
  refine Finset.sum_eq_zero fun m hm => ?_
  have hgm : g.coeff m = 0 := by
    by_contra h
    exact hne ((hf (mem_support_iff.mp hm)).symm.trans (hg h))
  rw [hgm, star_zero, mul_zero, zero_mul]

end Formalism.GradedWeylDivisibility
end
end

section

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

theorem highestWeightVectorNeZero : HWNe := by
  intro R _ _ r n hn ν h
  have key : ∀ (s : ℕ) (hr : s ≤ r) (hs : s ≤ n),
      eval (fun v : Fin r × Fin n => if v.1.val = v.2.val then (1 : R) else 0)
        (lpMinor R s hr hs) = 1 := by
    intro s hr hs
    unfold lpMinor
    rw [RingHom.map_det]
    convert Matrix.det_one (R := R) (n := Fin s)
    ext p q
    simp [RingHom.mapMatrix_apply, Matrix.one_apply, Fin.ext_iff]
  have h2 := congrArg (eval (fun v : Fin r × Fin n => if v.1.val = v.2.val then (1 : R) else 0)) h
  simp [hw, map_prod, map_pow, key] at h2

end Formalism.GradedWeylDivisibility
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerPos : FockPos := by
  intro σ f hf
  rw [LFockb_fockF_self]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  apply Finset.sum_pos
  · intro m hm
    apply mul_pos
    · exact Complex.normSq_pos.mpr (mem_support_iff.mp hm)
    · exact Nat.cast_pos.mpr (Finset.prod_pos fun k _ => Nat.factorial_pos _)
  · exact Finset.nonempty_of_ne_empty fun h => hf (support_eq_empty.mp h)

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerConjSymm_holds : FockHerm := by
  intro σ f g
  exact Formalism.REAL.fischerInner_eq_star g f

end Formalism.GradedWeylDivisibility
end
end
