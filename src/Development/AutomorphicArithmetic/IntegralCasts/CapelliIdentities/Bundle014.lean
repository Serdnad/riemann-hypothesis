module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

universe u

namespace UpperTheory.NoetherNormalizationChart

open MvPolynomial

variable {A : Type u} [CommRing A] {n : ℕ}

private noncomputable def shear (b : ℕ) (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval (Fin.cases (X 0) (fun i : Fin n => X i.succ + C c * X 0 ^ (b ^ (i.succ : ℕ))))

private lemma shear_zero (b : ℕ) (c : A) : shear (n := n) b c (X 0) = X 0 := by
  simp [shear]

private lemma shear_succ (b : ℕ) (c : A) (i : Fin n) :
    shear (n := n) b c (X i.succ) = X i.succ + C c * X 0 ^ (b ^ (i.succ : ℕ)) := by
  simp [shear]

private lemma shear_comp (b : ℕ) (c d : A) (h : c + d = 0) :
    (shear (n := n) b c).comp (shear b d) = AlgHom.id _ _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  cases i using Fin.cases with
  | zero => simp [shear_zero]
  | succ i =>
    rw [AlgHom.comp_apply, shear_succ, map_add (f := _), map_mul, map_pow, shear_zero, shear_succ,
      algHom_C, algebraMap_eq, add_assoc, ← add_mul, ← C_add, h]
    simp

private noncomputable def chart (A : Type u) [CommRing A] (n b : ℕ) :
    MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A) :=
  (AlgEquiv.ofAlgHom (shear b 1) (shear b (-1)) (shear_comp b 1 (-1) (by simp))
    (shear_comp b (-1) 1 (by simp))).trans (finSuccEquiv A n)

private lemma chart_X [Nontrivial A] {b : ℕ} (hb : b ≠ 0) (i : Fin (n + 1)) :
    (chart A n b (X i)).IsMonicOfDegree (b ^ (i : ℕ)) := by
  cases i using Fin.cases with
  | zero =>
    have : chart A n b (X 0) = Polynomial.X := by
      simp [chart, shear_zero, finSuccEquiv_X_zero]
    rw [this]
    exact ⟨by simp, Polynomial.monic_X⟩
  | succ i =>
    have : chart A n b (X i.succ)
        = Polynomial.X ^ (b ^ (i.succ : ℕ)) + Polynomial.C (X i) := by
      simp [chart, shear_succ, finSuccEquiv_X_zero, finSuccEquiv_X_succ, add_comm]
    rw [this]
    exact ⟨Polynomial.natDegree_X_pow_add_C, Polynomial.monic_X_pow_add_C _ (pow_ne_zero _ hb)⟩

private lemma chart_C (b : ℕ) (a : A) : chart A n b (C a) = Polynomial.C (C a) :=
  (chart A n b).commutes a

private lemma chart_monomial [Nontrivial A] {b : ℕ} (hb : b ≠ 0) (v : Fin (n + 1) →₀ ℕ) :
    (chart A n b (monomial v 1)).IsMonicOfDegree (∑ i, v i * b ^ (i : ℕ)) := by
  have h : chart A n b (monomial v 1) = ∏ i, chart A n b (X i) ^ v i := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  have hm : ∀ i ∈ Finset.univ, (chart A n b (X i) ^ v i).Monic :=
    fun i _ => (chart_X hb i).monic.pow _
  rw [h]
  refine ⟨?_, Polynomial.monic_prod_of_monic _ _ hm⟩
  rw [Polynomial.natDegree_prod_of_monic _ _ hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(chart_X hb i).monic.natDegree_pow, (chart_X hb i).natDegree_eq]

private lemma weight_inj {m b : ℕ} (v w : Fin m → ℕ) (hv : ∀ i, v i < b) (hw : ∀ i, w i < b)
    (h : ∑ i, v i * b ^ (i : ℕ) = ∑ i, w i * b ^ (i : ℕ)) : v = w := by
  have key : (fun i => (⟨v i, hv i⟩ : Fin b)) = fun i => ⟨w i, hw i⟩ := by
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    exact h
  funext i
  exact congrArg Fin.val (congrFun key i)

end UpperTheory.NoetherNormalizationChart

open UpperTheory.NoetherNormalizationChart in
theorem UpperTheory.exists_monic_change_of_variables :
    ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (f : MvPolynomial (Fin (n + 1)) A), f ≠ 0 → ∃ (e : MvPolynomial (Fin (n + 1)) A ≃ₐ[A] Polynomial (MvPolynomial (Fin n) A)) (a : A), a ≠ 0 ∧ (e f).leadingCoeff = MvPolynomial.C a := by
  intro A _ _ n f hf
  classical
  set b := f.totalDegree + 1 with hbdef
  have hb : b ≠ 0 := Nat.succ_ne_zero _
  let wt : (Fin (n + 1) →₀ ℕ) → ℕ := fun v => ∑ i, v i * b ^ (i : ℕ)
  have hlt : ∀ v ∈ f.support, ∀ i, v i < b := fun v hv i =>
    Nat.lt_succ_of_le ((MvPolynomial.monomial_le_degreeOf i hv).trans
      (MvPolynomial.degreeOf_le_totalDegree f i))
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image f.support wt (MvPolynomial.support_nonempty.mpr hf)
  have ha : f.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hsum : chart A n b f = ∑ w ∈ f.support,
      Polynomial.C (MvPolynomial.C (f.coeff w)) * chart A n b (MvPolynomial.monomial w 1) := by

    conv_lhs => rw [← f.support_sum_monomial_coeff, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← chart_C b, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hdeg : (chart A n b f).natDegree ≤ wt v := by
    rw [hsum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun w hw => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [(chart_monomial hb w).natDegree_eq]
    exact hmax w hw
  have hcoeff : (chart A n b f).coeff (wt v) = MvPolynomial.C (f.coeff v) := by
    rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single_of_mem v hv]
    · have h1 := (chart_monomial (A := A) hb v).monic.coeff_natDegree
      rw [(chart_monomial hb v).natDegree_eq] at h1
      rw [Polynomial.coeff_C_mul, h1, mul_one]
    · intro w hw hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [(chart_monomial hb w).natDegree_eq]
      refine lt_of_le_of_ne (hmax w hw) fun h => hne ?_
      exact DFunLike.coe_injective (weight_inj w v (hlt w hw) (hlt v hv) h)
  refine ⟨chart A n b, f.coeff v, ha, ?_⟩
  have hne : (chart A n b f).coeff (wt v) ≠ 0 := by
    rw [hcoeff]
    simpa using ha
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hne, hcoeff]
end

section

namespace AevalSpecializationAlgHom

open MvPolynomial

private theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω) (F : MvPolynomial σ ℚ)
    {E : Type} [CommRing E] [Algebra ℚ E] (u : σ → E) (hF : aeval τ F ≠ (0 : Ω))
    (v : E) (hv : v * aeval u F = 1) (P : MvPolynomial (Option σ) ℚ) :
    ∃ (N : ℕ) (G : MvPolynomial σ ℚ),
      aeval (fun o => Option.elim o (aeval τ F)⁻¹ τ) P * (aeval τ F) ^ N = aeval τ G ∧
      aeval (fun o => Option.elim o v u) P * (aeval u F) ^ N = aeval u G := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨N1, G1, h1, h1'⟩ := hp
    obtain ⟨N2, G2, h2, h2'⟩ := hq
    refine ⟨N1 + N2, G1 * F ^ N2 + G2 * F ^ N1, ?_, ?_⟩
    · simp only [map_add (f := _), map_mul, map_pow, ← h1, ← h2]; ring
    · simp only [map_add (f := _), map_mul, map_pow, ← h1', ← h2']; ring
  | mul_X p o hp =>
    obtain ⟨N, G, h1, h1'⟩ := hp
    cases o with
    | none =>
      refine ⟨N + 1, G, ?_, ?_⟩
      · simp only [map_mul, aeval_X, Option.elim_none]
        rw [← h1, pow_succ]
        field_simp
      · simp only [map_mul, aeval_X, Option.elim_none]
        rw [← h1', pow_succ]
        linear_combination (aeval (fun o => Option.elim o v u) p * aeval u F ^ N) * hv
    | some i =>
      refine ⟨N, G * X i, ?_, ?_⟩
      · simp only [map_mul, aeval_X, Option.elim_some, ← h1]; ring
      · simp only [map_mul, aeval_X, Option.elim_some, ← h1']; ring

end AevalSpecializationAlgHom

theorem UpperTheory.Reformulated.B.Yde9.main :
    ∀ (Ω : Type) [inst : Field Ω] [inst_1 : Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω)
      (E : Type) [inst_2 : CommRing E] [inst_3 : Algebra ℚ E] (u : σ → E),
      (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) F ≠ (0 : Ω) →
        S = Algebra.adjoin ℚ (Insert.insert ((MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) F)⁻¹ (Set.range τ)) →
          (∀ (G : MvPolynomial σ ℚ),
              (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) G = (0 : Ω) →
                (MvPolynomial.aeval u : MvPolynomial σ ℚ → E) G = (0 : E)) →
            IsUnit ((MvPolynomial.aeval u : MvPolynomial σ ℚ → E) F) →
              ∃ (φ : ↥S →ₐ[ℚ] E),
                ∀ (G : MvPolynomial σ ℚ) (s : ↥S),
                  (↑s : Ω) = (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) G →
                    (φ : ↥S → E) s = (MvPolynomial.aeval u : MvPolynomial σ ℚ → E) G := by
  intro Ω _ _ σ τ F S E _ _ u hF hS hker hU
  obtain ⟨w, hw⟩ := hU
  set v : E := ((w⁻¹ : Eˣ) : E) with hvdef
  have hv : v * MvPolynomial.aeval u F = 1 := by rw [← hw]; simp [v]
  set τ' : Option σ → Ω := fun o => Option.elim o (MvPolynomial.aeval τ F)⁻¹ τ with hτ'
  set u' : Option σ → E := fun o => Option.elim o v u with hu'
  have hS' : S = (MvPolynomial.aeval τ').range := by
    rw [hS, ← Algebra.adjoin_range_eq_range_aeval, Option.range_eq]
    rfl
  subst hS'
  have hsurj := AlgHom.rangeRestrict_surjective (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω)
  have hK : ∀ P ∈ RingHom.ker (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).rangeRestrict,
      (MvPolynomial.aeval u') P = 0 := by
    intro P hP
    rw [RingHom.mem_ker] at hP
    have hP' : MvPolynomial.aeval τ' P = 0 := congrArg Subtype.val hP
    obtain ⟨N, G, h1, h1'⟩ := AevalSpecializationAlgHom.key τ F u hF v hv P
    have h0 : MvPolynomial.aeval τ G = 0 := by
      rw [← h1]; simp only [τ'] at hP'; simp [hP']
    have h2 := hker G h0
    rw [h2] at h1'
    have hunit : IsUnit (MvPolynomial.aeval u F ^ N) := by
      rw [← hw]; exact (w.isUnit).pow N
    exact (hunit.mul_left_eq_zero).mp h1'
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let L := Ideal.Quotient.liftₐ (RingHom.ker (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).rangeRestrict) (MvPolynomial.aeval u') hK
  refine ⟨L.comp e.symm.toAlgHom, ?_⟩
  intro G s hs
  have hs' : s = (MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G) := by
    apply Subtype.ext
    rw [hs]
    simp [MvPolynomial.aeval_rename]
    rfl
  rw [hs']
  have he : e.symm ((MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G)) =
      Ideal.Quotient.mk _ (MvPolynomial.rename some G) :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hsurj _
  change L (e.symm ((MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G))) = _
  rw [he]
  change MvPolynomial.aeval u' (MvPolynomial.rename some G) = _
  rw [MvPolynomial.aeval_rename]
  rfl
end

section

private lemma UpperTheory.Reformulated.B.Qn12.step {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (y c : ι → R) (p e x a : R) (j : ι) (hy : y j = x - a) (hc : p = e + ∑ i, c i * y i) :
    p * x = e * a + ∑ i, (c i * a + if i = j then p else 0) * y i := by
  have h1 : ∑ i, (c i * a + if i = j then p else 0) * y i = (∑ i, c i * y i) * a + p * y j := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_mul, mul_right_comm]
  rw [h1, hy]
  linear_combination a * hc

private lemma UpperTheory.Reformulated.B.Qn12.step_add {R ι : Type*} [CommRing R] [Fintype ι]
    (y c d : ι → R) (p r e f : R) (hc : p = e + ∑ i, c i * y i) (hd : r = f + ∑ i, d i * y i) :
    p + r = (e + f) + ∑ i, (c i + d i) * y i := by
  simp only [add_mul, Finset.sum_add_distrib]
  linear_combination hc + hd

theorem UpperTheory.Reformulated.B.Qn12.exists_expansion :
    ∀ {n : ℕ} (q : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ),
    ∃ (c : Fin n → MvPolynomial (Fin n) ℂ),
      p =
        (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) ((MvPolynomial.eval q : MvPolynomial (Fin n) ℂ → ℂ) p) +
          ∑ i : Fin n, c i * (MvPolynomial.X i - (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) (q i)) := by
  intro n q p
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add p r hp hr =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hr
    refine ⟨fun i => c i + d i, ?_⟩
    rw [map_add (f := _), map_add (f := _)]
    exact UpperTheory.Reformulated.B.Qn12.step_add _ c d p r _ _ hc hd
  | mul_X p j hp =>
    obtain ⟨c, hc⟩ := hp
    refine ⟨fun i => c i * MvPolynomial.C (q j) + if i = j then p else 0, ?_⟩
    rw [map_mul, MvPolynomial.eval_X, map_mul]
    exact UpperTheory.Reformulated.B.Qn12.step (fun i => MvPolynomial.X i - MvPolynomial.C (q i)) c p _ _ _ j rfl hc
end

section

theorem UpperTheory.Reformulated.B.Qn15.eval_fg :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : Algebra R ℂ] {σ : Type} {M₀ : Submodule R ℂ},
    M₀.FG →
      ∀ (P : MvPolynomial σ ℂ),
        ∃ (M : Submodule R ℂ),
          M.FG ∧ ∀ (v : σ → ℂ), (∀ (i : σ), v i ∈ M₀) → (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P ∈ M := by
  intro R _ _ σ M₀ h₀ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span R {a}, Submodule.fg_span_singleton a, fun v _ => ?_⟩
    rw [MvPolynomial.eval_C]
    exact Submodule.mem_span_singleton_self a
  | add p q hp hq =>
    obtain ⟨M, hM, hp⟩ := hp
    obtain ⟨N, hN, hq⟩ := hq
    refine ⟨M ⊔ N, hM.sup hN, fun v hv => ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hp v hv) (hq v hv)
  | mul_X p i hp =>
    obtain ⟨M, hM, hp⟩ := hp
    refine ⟨M * M₀, hM.mul h₀, fun v hv => ?_⟩
    rw [map_mul, MvPolynomial.eval_X]
    exact Submodule.mul_mem_mul (hp v hv) (hv i)
end

section

theorem UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (Q : Set (Fin n → k) → Prop),
    Q ∅ →
      (∀ (s t : Set (Fin n → k)), s ⊆ t → Q t → Q s) →
        (∀ (s t : Set (Fin n → k)), Q s → Q t → Q (s ∪ t)) →
          (∀ (I : Ideal (MvPolynomial (Fin n) k)),
              I.IsPrime →
                ∃ g ∉ I,
                  Q
                    {c : Fin n → k |
                      (∀ p ∈ I, (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) p = (0 : k)) ∧
                        (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) g ≠ (0 : k)}) →
            Q Set.univ := by
  intro k inst n Q h0 hmono hunion hprime
  have key : ∀ I : Ideal (MvPolynomial (Fin n) k),
      Q {c : Fin n → k | ∀ p ∈ I, MvPolynomial.eval c p = 0} := by
    intro I
    induction I using IsNoetherian.induction with
    | _ I ih =>
      have step : ∀ g : MvPolynomial (Fin n) k, g ∉ I →
          Q {c : Fin n → k | (∀ p ∈ I, MvPolynomial.eval c p = 0) ∧
            MvPolynomial.eval c g = 0} := by
        intro g hg
        have hlt : I < I ⊔ Ideal.span {g} := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro h
          apply hg
          rw [h]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
        refine hmono _ _ ?_ (ih _ hlt)
        rintro c ⟨hc, hcg⟩
        have hle : I ⊔ Ideal.span {g} ≤ RingHom.ker (MvPolynomial.eval c) := by
          refine sup_le (fun p hp => (RingHom.mem_ker).2 (hc p hp)) ?_
          rw [Ideal.span_singleton_le_iff_mem]
          exact (RingHom.mem_ker).2 hcg
        exact fun p hp => (RingHom.mem_ker).1 (hle hp)
      by_cases hP : Ideal.IsPrime I
      · obtain ⟨g, hg, hQ⟩ := hprime I hP
        refine hmono _ _ ?_ (hunion _ _ hQ (step g hg))
        intro c hc
        by_cases hcg : MvPolynomial.eval c g = 0
        · exact Or.inr ⟨hc, hcg⟩
        · exact Or.inl ⟨hc, hcg⟩
      · rcases Ideal.not_isPrime_iff.1 hP with htop | ⟨x, hx, y, hy, hxy⟩
        · refine hmono _ _ ?_ h0
          intro c hc
          have h1 := hc 1 (htop ▸ Submodule.mem_top)
          simp at h1
        · refine hmono _ _ ?_ (hunion _ _ (step x hx) (step y hy))
          intro c hc
          have h1 := hc _ hxy
          rw [map_mul] at h1
          rcases mul_eq_zero.1 h1 with h | h
          · exact Or.inl ⟨hc, h⟩
          · exact Or.inr ⟨hc, h⟩
  refine hmono _ _ ?_ (key ⊥)
  intro c _ p hp
  rw [(Ideal.mem_bot).1 hp, map_zero]
end

section

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.FrechetDerivEvaluation.aux {σ : Type*} [Fintype σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    HasFDerivAt (fun x : σ → ℂ => eval x g)
      (∑ i : σ, eval z (pderiv i g) • (ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ)) z := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a z
  | add p q hp hq =>
    have h := hp.add hq
    simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
    exact h
  | mul_X p n hp =>
    have h := hp.mul (hasFDerivAt_apply (𝕜 := ℂ) n z)
    simp only [map_mul, eval_X]
    refine HasFDerivAt.congr_fderiv h ?_
    ext v
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib, apply_ite (eval z), mul_assoc, mul_comm, mul_left_comm]

open MvPolynomial in
theorem UpperTheory.Reformulated.B.FrechetDerivEvaluation.hasFDerivAt_eval.{u_1}
    {σ : Type u_1} [inst : Fintype σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    HasFDerivAt (fun x : σ → ℂ => eval x g)
      (∑ i : σ, eval z (pderiv i g) • (ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ)) z :=
  UpperTheory.Reformulated.B.FrechetDerivEvaluation.aux g z
end

section

theorem UpperTheory.Reformulated.B.Qk66.aeval_comm :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (φ : M →ₗ[L] N) (A : Module.End L M) (A' : Module.End L N),
    (∀ (y : M), (φ : M → N) ((A : M → M) y) = (A' : N → N) ((φ : M → N) y)) →
      ∀ (Q : Polynomial L) (y : M),
        (φ : M → N) (((Polynomial.aeval A : Polynomial L → Module.End L M) Q : M → M) y) =
          ((Polynomial.aeval A' : Polynomial L → Module.End L N) Q : N → N) ((φ : M → N) y) := by
  intro L M N _ _ _ _ _ φ A A' h Q
  induction Q using Polynomial.induction_on with
  | C a =>
    intro y
    simp [Module.algebraMap_end_apply]
  | add p q hp hq =>
    intro y
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a ih =>
    intro y
    rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval A), map_mul (Polynomial.aeval A'),
      Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]
end

section

theorem UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule.{u_1} :
    ∀ {Y : Type u_1} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y]
    (A : Module.End ℂ Y) (p : Submodule ℂ Y),
    (∀ y ∈ p, (A : Y → Y) y ∈ p) →
      ∀ (q : Polynomial ℂ), ∀ y ∈ p, ((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) q : Y → Y) y ∈ p := by
  intro Y _ _ A p hA q y hy
  have hpow : ∀ n : ℕ, (A ^ n) y ∈ p := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hA _ ih
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine p.sum_mem fun i _ => ?_
  rw [LinearMap.smul_apply]
  exact p.smul_mem _ (hpow i)
end
