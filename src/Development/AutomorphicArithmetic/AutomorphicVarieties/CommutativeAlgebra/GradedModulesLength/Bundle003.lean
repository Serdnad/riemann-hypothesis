module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.fix_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ σ : 𝒜 0 →ₐ[O] K, idD 𝒜 ≤ RingHom.ker σ → (∀ b : 𝒜 0, (b : A) ∈ Q.ideal → σ b = 0) →
      ∃ ξ : A →ₐ[O] K, OnS Q.ideal ξ ∧ NegZero 𝒜 ξ ∧ PosZero 𝒜 ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q σ hid hQ
  have hcoe : ∀ z (hz : z ∈ 𝒜 0), DirectSum.decompose 𝒜 z 0 = ⟨z, hz⟩ :=
    fun z hz => Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 hz)
  have dmul : ∀ (i : ℤ) (z : A), z ∈ 𝒜 i → ∀ b : A,
      (DirectSum.decompose 𝒜 (z * b) 0 : A) = z * (DirectSum.decompose 𝒜 b (-i) : A) := by
    intro i z hz b
    have h := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (j := -i) hz (b := b)
    rwa [add_neg_cancel] at h
  have kill : ∀ c : 𝒜 0, ∀ f ∈ 𝒜 (-2), ∀ g ∈ 𝒜 2, (c : A) = f * g → σ c = 0 := by
    intro c f hf g hg h
    exact (RingHom.mem_ker).1 (hid (Ideal.subset_span ⟨f, hf, g, hg, h⟩))
  have kill1 : ∀ c : 𝒜 0, ∀ f ∈ 𝒜 (-1), ∀ g ∈ 𝒜 1, (c : A) = f * g → σ c = 0 := by
    intro c f hf g hg h
    have hff : f * f ∈ 𝒜 (-2) := by
      convert SetLike.mul_mem_graded hf hf using 2
      norm_num
    have hgg : g * g ∈ 𝒜 2 := by
      convert SetLike.mul_mem_graded hg hg using 2
      norm_num
    have h2 : σ (c * c) = 0 := kill (c * c) (f * f) hff (g * g) hgg (by
      rw [SetLike.GradeZero.coe_mul, h]
      ring)
    rw [map_mul] at h2
    exact mul_self_eq_zero.1 h2
  obtain ⟨S, hS, hgen⟩ := hW.gen
  have key : ∀ z ∈ S, ∀ b : A, σ (DirectSum.decompose 𝒜 (z * b) 0) = 0 := by
    intro z hz b
    rcases hS z hz with h | h | h | h
    · refine kill _ z h _ (DirectSum.decompose 𝒜 b 2).2 ?_
      rw [dmul _ z h b, neg_neg]
    · refine kill1 _ z h _ (DirectSum.decompose 𝒜 b 1).2 ?_
      rw [dmul _ z h b, neg_neg]
    · refine kill1 _ _ (DirectSum.decompose 𝒜 b (-1)).2 z h ?_
      rw [dmul _ z h b, mul_comm]
    · refine kill _ _ (DirectSum.decompose 𝒜 b (-2)).2 z h ?_
      rw [dmul _ z h b, mul_comm]
  have h0 : ∀ z ∈ 𝒜 0, ∀ b : A, σ (DirectSum.decompose 𝒜 (z * b) 0) =
      σ (DirectSum.decompose 𝒜 z 0) * σ (DirectSum.decompose 𝒜 b 0) := by
    intro z hz b
    have h1 : DirectSum.decompose 𝒜 (z * b) 0 = ⟨z, hz⟩ * DirectSum.decompose 𝒜 b 0 := by
      apply Subtype.ext
      rw [SetLike.GradeZero.coe_mul]
      have h := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (j := 0) hz (b := b)
      rw [add_zero] at h
      exact h
    rw [h1, hcoe z hz, map_mul]
  have hmul : ∀ a b : A, σ (DirectSum.decompose 𝒜 (a * b) 0) =
      σ (DirectSum.decompose 𝒜 a 0) * σ (DirectSum.decompose 𝒜 b 0) := by
    intro a b
    have ha : a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ S) := by
      rw [hgen]
      trivial
    induction ha using Algebra.adjoin_induction generalizing b with
    | mem z hz =>
      rcases hz with hz | hz
      · exact h0 z hz b
      · have hz0 : DirectSum.decompose 𝒜 z 0 = 0 := by
          apply Subtype.ext
          rcases hS z hz with h | h | h | h <;>
            (rw [DirectSum.decompose_of_mem_ne 𝒜 h (by norm_num)]; rfl)
        rw [key z hz b, hz0, map_zero, zero_mul]
    | algebraMap c => exact h0 _ (SetLike.algebraMap_mem_graded 𝒜 c) b
    | add a a' _ _ iha iha' =>
      rw [add_mul, DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _), iha, iha',
        DirectSum.decompose_add, DirectSum.add_apply, map_add, add_mul]
    | mul a a' _ _ iha iha' =>
      rw [mul_assoc, iha (a' * b), iha' b, iha a']
      ring
  let ξ : A →ₐ[O] K :=
    { toFun := fun a => σ (DirectSum.decompose 𝒜 a 0)
      map_one' := by
        show σ (DirectSum.decompose 𝒜 1 0) = 1
        rw [show DirectSum.decompose 𝒜 (1 : A) 0 = 1 from Subtype.ext (by
          rw [DirectSum.decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜),
            SetLike.GradeZero.coe_one]), map_one]
      map_mul' := hmul
      map_zero' := by simp
      map_add' := by
        intro a b
        show σ (DirectSum.decompose 𝒜 (a + b) 0) =
          σ (DirectSum.decompose 𝒜 a 0) + σ (DirectSum.decompose 𝒜 b 0)
        rw [DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _)]
      commutes' := by
        intro c
        show σ (DirectSum.decompose 𝒜 (algebraMap O A c) 0) = algebraMap O K c
        rw [hcoe _ (SetLike.algebraMap_mem_graded 𝒜 c)]
        rw [show (⟨algebraMap O A c, SetLike.algebraMap_mem_graded 𝒜 c⟩ : 𝒜 0) =
          algebraMap O (𝒜 0) c from Subtype.ext (SetLike.GradeZero.coe_algebraMap 𝒜 c).symm]
        exact σ.commutes c }
  have hξ : ∀ a, ξ a = σ (DirectSum.decompose 𝒜 a 0) := fun a => rfl
  have hne : ∀ j : ℤ, j ≠ 0 → ∀ f ∈ 𝒜 j, ξ f = 0 := by
    intro j hj f hf
    rw [hξ, show DirectSum.decompose 𝒜 f 0 = 0 from Subtype.ext (by
      rw [DirectSum.decompose_of_mem_ne 𝒜 hf hj]; rfl), map_zero]
  refine ⟨ξ, ?_, ?_, ?_, ?_⟩
  · intro f hf
    have hle : Q.ideal ≤ RingHom.ker ξ := by
      unfold Eqns.ideal
      rw [Ideal.span_le]
      intro y hy
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hy with ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · exact hne (-1) (by norm_num) _ (Q.hF i)
      · exact hne (-2) (by norm_num) _ (Q.hG i)
      · exact hne 1 (by norm_num) _ (Q.hE i)
      · exact hne 2 (by norm_num) _ (Q.hE' i)
      · rw [hξ, hcoe _ (Q.hZ i).1]
        exact hQ ⟨Q.Z i, (Q.hZ i).1⟩ (Ideal.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
    exact (RingHom.mem_ker).1 (hle hf)
  · intro j hj f hf
    exact hne j (by omega) f hf
  · intro j hj f hf
    exact hne j (by omega) f hf
  · refine AlgHom.ext fun b => ?_
    show σ (DirectSum.decompose 𝒜 ((b : 𝒜 0) : A) 0) = σ b
    rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private theorem coe_sec_eq_monomial_single (i : Fin k) (f : A) (hf : f ∈ N i) :
    (sec N i f hf : MvPolynomial (Fin k) A) = MvPolynomial.monomial (Finsupp.single i 1) f := rfl

private theorem toDeg_single_one (i : Fin k) : toDeg (Finsupp.single i 1) = e i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [toDeg, e]
  · simp [toDeg, e, h, Finsupp.single_apply, Ne.symm h]

private theorem exists_sec_notMem {p : Ideal (rees N)} (hp : ¬ Irr (reesGr N) ≤ p) (i : Fin k) :
    ∃ (f : A) (hf : f ∈ N i), sec N i f hf ∉ p := by
  by_contra hcon
  push_neg at hcon
  apply hp
  have hle : Ideal.span (reesGr N (e i) : Set (rees N)) ≤ p := by
    rw [Ideal.span_le]
    intro q hq
    have hc : AddMonoidAlgebra.coeff (q : MvPolynomial (Fin k) A) (Finsupp.single i 1) ∈ N i := by
      have := q.2 (Finsupp.single i 1)
      rwa [lat_single] at this
    have hq' : q = sec N i _ hc := by
      apply Subtype.ext
      rw [coe_sec_eq_monomial_single]
      ext m
      rw [MvPolynomial.coeff_monomial]
      split_ifs with hm
      · rw [hm]
      · apply hq m
        intro hd
        apply hm
        apply toDeg_injective
        rw [hd, toDeg_single_one]
    rw [hq']
    exact hcon _ hc
  exact le_trans (le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_univ i))) hle

private theorem sec_mul_sec (i j : Fin k) {f g : A} (hf : f ∈ N i) (hg : g ∈ N i) (hf' : f ∈ N j) (hg' : g ∈ N j) :
    sec N i f hf * sec N j g hg' = sec N i g hg * sec N j f hf' := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, coe_sec_eq_monomial_single, MvPolynomial.monomial_mul]
  rw [mul_comm f g]

end SlopeTestRemainingChoices

private theorem algebraMap_mul_sec_mul_sec_eq_of_mul_eq {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (c : B) (i j : Fin k) {x y x' y' : A} (hx : x ∈ N i) (hy : y ∈ N j)
    (hx' : x' ∈ N i) (hy' : y' ∈ N j) (h : algebraMap B A c * x * y = x' * y') :
    algebraMap B (rees N) c * (sec N i x hx * sec N j y hy) = sec N i x' hx' * sec N j y' hy' := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_sec_eq_monomial_single, MvPolynomial.algebraMap_apply,
    MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial]
  rw [← h, mul_assoc]

theorem UpperTheory.V.Alg.M.zi_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ p : Ideal (mR Q), p.IsPrime → ¬ Irr (mGr Q) ≤ p → secs (ts Q) ≤ p → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p) →
      (∀ b : 𝒜 0, (b : A) ∈ Q.ideal → algebraMap (𝒜 0) (mR Q) b ∈ p) ∧
      ∀ i, sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F i ^ 2) (sq_mem_neg 𝒜 (Q.hF i)) ∈ p := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q P hP hIrr hts hZ
  have hmul : ∀ {i j l : ℤ} {a b : A}, i + j = l → a ∈ 𝒜 i → b ∈ 𝒜 j → a * b ∈ 𝒜 l := by
    rintro i j l a b rfl ha hb
    exact SetLike.mul_mem_graded ha hb
  have m0 : ∀ {a : A}, a ∈ 𝒜 (-2) → a ∈ mN 𝒜 (Q.F (Fin.last r)) 0 := fun h => h
  have m1 : ∀ {a : A}, a ∈ 𝒜 2 → a ∈ mN 𝒜 (Q.F (Fin.last r)) 1 := fun h => h
  have m2 : ∀ {a : A}, a ∈ mN 𝒜 (Q.F (Fin.last r)) 2 → a ∈ 𝒜 (-2) := by
    intro a ha
    have hle : ((𝒜 0) ∙ Q.F (Fin.last r) ^ 2 ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 : Submodule (𝒜 0) A)
        ≤ oz 𝒜 (-2) := by
      apply sup_le
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact sq_mem_neg 𝒜 (Q.hF _)
      · apply Submodule.mul_le.2
        intro u hu v hv
        have hu' : u ∈ oz 𝒜 (-4) :=
          (Submodule.mul_le.2 (fun a ha b hb => hmul (i := -2) (j := -2) (by norm_num) ha hb) :
            oz 𝒜 (-2) * oz 𝒜 (-2) ≤ oz 𝒜 (-4)) hu
        exact hmul (i := -4) (j := 2) (by norm_num) hu' hv
    exact hle ha
  have hF2 : Q.F (Fin.last r) ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 2 :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hmem : ∀ {d : Deg 3} {u : mR Q}, (d, u) ∈ ts Q → u ∈ P := fun h => hts (Ideal.subset_span ⟨_, h⟩)
  obtain ⟨g0, hg0, hg0P⟩ := exists_sec_notMem _ hIrr 0
  obtain ⟨f1, hf1, hf1P⟩ := exists_sec_notMem _ hIrr 1
  obtain ⟨h2, hh2, hh2P⟩ := exists_sec_notMem _ hIrr 2
  have hFlast : sec (mN 𝒜 (Q.F (Fin.last r))) 2 (Q.F (Fin.last r) ^ 2) hF2 ∈ P :=
    hmem (d := e 2) (by simp [ts, tsR])
  have hsq : ∀ i, sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F i ^ 2) (sq_mem_neg 𝒜 (Q.hF i)) ∈ P := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have heq := sec_mul_sec (mN 𝒜 (Q.F (Fin.last r))) 0 2 (sq_mem_neg 𝒜 (Q.hF (Fin.last r)))
        (m0 (m2 hh2)) hF2 hh2
      have hin : sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F (Fin.last r) ^ 2) (sq_mem_neg 𝒜 (Q.hF (Fin.last r))) *
          sec (mN 𝒜 (Q.F (Fin.last r))) 2 h2 hh2 ∈ P := by
        rw [heq]
        exact P.mul_mem_left _ hFlast
      exact (hP.mem_or_mem hin).resolve_right hh2P
    · exact hmem (d := e 0) (by simp [ts, tsF, List.mem_ofFn])
  refine ⟨?_, hsq⟩
  set u := sec (mN 𝒜 (Q.F (Fin.last r))) 0 g0 hg0 * sec (mN 𝒜 (Q.F (Fin.last r))) 1 f1 hf1 with hu_def
  have hu : u ∉ P := fun h => (hP.mem_or_mem h).elim hg0P hf1P
  have key : ∀ w : 𝒜 0, algebraMap (𝒜 0) (mR Q) w * u ∈ P → algebraMap (𝒜 0) (mR Q) w ∈ P :=
    fun w h => (hP.mem_or_mem h).resolve_right hu
  have keysq : ∀ w : 𝒜 0, algebraMap (𝒜 0) (mR Q) (w * w) * u ∈ P → algebraMap (𝒜 0) (mR Q) w ∈ P := by
    intro w h
    have := key _ h
    rw [map_mul] at this
    exact (hP.mem_or_mem this).elim id id
  have hgen : ∀ (d : ℤ) (g : A) (hg : g ∈ 𝒜 d),
      (∀ (j : ℤ) (hj : j + d = 0) (c : A) (hc : c ∈ 𝒜 j),
        algebraMap (𝒜 0) (mR Q) ⟨c * g, hmul hj hc hg⟩ ∈ P) →
      ∀ a : A, algebraMap (𝒜 0) (mR Q) (DirectSum.decompose 𝒜 (a * g) 0) ∈ P := by
    intro d g hg hc a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j a =>
      by_cases hj : j + d = 0
      · have h0 := hc j hj a a.2
        convert h0 using 2
        apply Subtype.ext
        exact DirectSum.decompose_of_mem_same 𝒜 (hmul hj a.2 hg)
      · have h0 : DirectSum.decompose 𝒜 ((a : A) * g) 0 = 0 :=
          Subtype.ext (DirectSum.decompose_of_mem_ne 𝒜 (hmul rfl a.2 hg) hj)
        rw [h0, map_zero]
        exact P.zero_mem
    | add a a' ha ha' =>
      rw [add_mul, DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _)]
      exact P.add_mem ha ha'
  intro b hb
  have hall : ∀ y ∈ Q.ideal, ∀ a : A, algebraMap (𝒜 0) (mR Q) (DirectSum.decompose 𝒜 (a * y) 0) ∈ P := by
    intro y hy
    unfold Eqns.ideal at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · refine hgen (-1) _ (Q.hF i) ?_
        intro j hj c hc
        obtain rfl : j = 1 := by omega
        apply keysq
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1 (sq_mem_neg 𝒜 (Q.hF i))
          (m1 (hmul (i := 0) (j := 2) (by norm_num) (hmul (i := 2) (j := -2) (by norm_num)
            (hmul (i := 1) (j := 1) (by norm_num) hc hc) hg0) hf1)) (by change c * Q.F i * (c * Q.F i) * g0 * f1 = _; ring)]
        exact P.mul_mem_right _ (hsq i)
      · refine hgen (-2) _ (Q.hG i) ?_
        intro j hj c hc
        obtain rfl : j = 2 := by omega
        apply key
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1 (Q.hG i)
          (m1 (hmul (i := 0) (j := 2) (by norm_num) (hmul (i := 2) (j := -2) (by norm_num) hc hg0) hf1))
          (by change c * Q.G i * g0 * f1 = _; ring)]
        exact P.mul_mem_right _ (hmem (d := e 0) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 1 _ (Q.hE i) ?_
        intro j hj c hc
        obtain rfl : j = -1 := by omega
        apply keysq
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1
          (m0 (hmul (i := -4) (j := 2) (by norm_num) (hmul (i := -2) (j := -2) (by norm_num)
            (hmul (i := -1) (j := -1) (by norm_num) hc hc) hg0) hf1)) (sq_mem_pos 𝒜 (Q.hE i))
          (by change c * Q.E i * (c * Q.E i) * g0 * f1 = _; ring)]
        exact P.mul_mem_left _ (hmem (d := e 1) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 2 _ (Q.hE' i) ?_
        intro j hj c hc
        obtain rfl : j = -2 := by omega
        apply key
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1
          (m0 (hmul (i := -4) (j := 2) (by norm_num) (hmul (i := -2) (j := -2) (by norm_num) hc hg0) hf1))
          (Q.hE' i) (by change c * Q.E' i * g0 * f1 = _; ring)]
        exact P.mul_mem_left _ (hmem (d := e 1) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 0 _ (Q.hZ i).1 ?_
        intro j hj c hc
        obtain rfl : j = 0 := by omega
        have : (⟨c * Q.Z i, hmul hj hc (Q.hZ i).1⟩ : 𝒜 0) = ⟨c, hc⟩ * ⟨Q.Z i, (Q.hZ i).1⟩ := rfl
        rw [this, map_mul]
        exact P.mul_mem_left _ (hZ i)
    | zero => intro a; simp
    | add y z _ _ hy hz =>
      intro a
      rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _)]
      exact P.add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (a * c)
  have h1 := hall _ hb 1
  rw [one_mul] at h1
  convert h1 using 2
  apply Subtype.ext
  exact (DirectSum.decompose_of_mem_same 𝒜 b.2).symm
end

section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.fg_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ j, (oz 𝒜 j).FG := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx j
  obtain ⟨s, -, hadj⟩ := hx.gen
  have hadj' : Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ ↑s) := by rw [hadj]; trivial
    have hle : Algebra.adjoin O ((𝒜 0 : Set A) ∪ ↑s) ≤
        (Algebra.adjoin (𝒜 0) (s : Set A)).restrictScalars O := by
      rw [Algebra.adjoin_le_iff]
      rintro z (hz | hz)
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact (Algebra.adjoin (𝒜 0) (s : Set A)).algebraMap_mem ⟨z, hz⟩
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact Algebra.subset_adjoin hz
    exact (Subalgebra.mem_restrictScalars O).1 (hle hy)
  haveI : Algebra.FiniteType (𝒜 0) A := ⟨⟨s, hadj'⟩⟩
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing (𝒜 0) A
  have hI : (Ideal.span (𝒜 j : Set A)).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hI
  refine ⟨t, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    exact ht
  · intro y hy
    have hyA : y ∈ 𝒜 j := hy
    have hy' : y ∈ Submodule.span A (t : Set A) := by
      rw [← hspan]
      exact Submodule.subset_span hyA
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hy'
    have hyj : y = (DirectSum.decompose 𝒜 y j : A) := (DirectSum.decompose_of_mem_same 𝒜 hyA).symm
    rw [hyj, ← hf, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have e : (DirectSum.decompose 𝒜 (f i • i) j : A) = (DirectSum.decompose 𝒜 (f i) 0 : A) * i := by
      have := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := f i) (i := 0) (ht hi)
      rw [zero_add] at this
      exact this
    rw [e]
    exact Submodule.smul_mem _ (DirectSum.decompose 𝒜 (f i) 0) (Submodule.subset_span hi)
end
