module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace PI.OpWords

theorem wtLe_span (K : Type) [Field K] (k : ℕ) (c : ℤ) (s : Set (Pol K k))
    (hs : ∀ f ∈ s, WtLe K k c f) : ∀ f ∈ Submodule.span K s, WtLe K k c f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm a
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hx m h a
    · exact hy m h a
  | smul r x _ hx =>
    intro m hm a
    exact hx m (support_smul hm) a

theorem kappa_ad (hL : KappaLeft) (hR : KappaRight) (K : Type) [Field K] [CharZero K] (k d : ℕ)
    (a b : Fin k) (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d (Formalism.MainNotions.TestSideCounting.Ed K k d a b * A - A * Formalism.MainNotions.TestSideCounting.Ed K k d a b) =
      Rop K k a b (kappa K k d A) := by
  rw [map_sub, hL K k d a b A, hR K k d a b A]
  rfl

theorem divide_all (hV : Vanish) (hD : DivT) (hRB : RBihom) (hRT : RTT) (hTW : TTWt)
    (K : Type) [Field K] [CharZero K] (k c : ℕ) : ∀ n : ℕ, ∀ (W : Submodule K (Pol K k)),
    W ≤ Bihom K k (c + n) → (∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) → (∀ f ∈ W, WtLe K k c f) →
    ∀ f ∈ W, ∃ g ∈ Bihom K k c, f = tt K k ^ n * g := by
  intro n
  induction n with
  | zero =>
    intro W hW _ _ f hf
    exact ⟨f, by simpa using hW hf, by simp⟩
  | succ n ih =>
    intro W hW hst hwt f hf
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hf' : f ∈ weightedHomogeneousSubmodule K (wx 0) (c + (n + 1)) ⊓
          weightedHomogeneousSubmodule K (wxi 0) (c + (n + 1)) := hW hf
      have h1 := (Submodule.mem_inf.1 hf').1
      rw [mem_weightedHomogeneousSubmodule] at h1
      rw [mul_zero]
      ext m
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      by_contra h
      have h2 := h1 h
      have h3 : m = 0 := by
        ext v
        rcases v with i | i <;> exact i.elim0
      rw [h3, map_zero] at h2
      omega
    · have htt : tt K k ≠ 0 := by
        intro h
        have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
        simp [tt] at h1
        omega
      have hdiv : ∀ f ∈ W, ∃ g ∈ Bihom K k (c + n), f = tt K k * g := by
        intro f hf
        have hv := hV K k (c + (n + 1)) c W hW hst hwt (by omega) f hf
        obtain ⟨g, hg, rfl⟩ := hD K k (c + (n + 1)) (by omega) f (hW hf) hv
        exact ⟨g, by simpa using hg, rfl⟩
      let W' : Submodule K (Pol K k) := W.comap (LinearMap.mulLeft K (tt K k))
      have hmem : ∀ g, g ∈ W' ↔ tt K k * g ∈ W := fun g => Iff.rfl
      have hW' : W' ≤ Bihom K k (c + n) := by
        intro g hg
        obtain ⟨g', hg', he⟩ := hdiv _ ((hmem g).1 hg)
        rw [mul_left_cancel₀ htt he]
        exact hg'
      have hst' : ∀ f ∈ W', ∀ a b, Rop K k a b f ∈ W' := by
        intro g hg a b
        rw [hmem, ← hRT K k a b g]
        exact hst _ ((hmem g).1 hg) a b
      have hwt' : ∀ f ∈ W', WtLe K k c f := by
        intro g hg
        exact hTW K k c g (hwt _ ((hmem g).1 hg))
      obtain ⟨g, hg, rfl⟩ := hdiv f hf
      obtain ⟨g'', hg'', rfl⟩ := ih W' hW' hst' hwt' g ((hmem g).2 hf)
      exact ⟨g'', hg'', by ring⟩

theorem opWords_of (hI : KappaInj) (hL : KappaLeft) (hR : KappaRight) (hB : KappaBihom)
    (hE : WtOfEig) (hRB : RBihom) (hRT : RTT) (hTW : TTWt) (hD : DivT) (hV : Vanish)
    (hS : Surj) : Formalism.MainNotions.TestSideCounting.OpBound := by
  intro K _ _ k d c WW Sg hst hspan heig A hA
  have key : ∃ c' : ℕ, c' ≤ c ∧ c' ≤ d ∧ ∃ g ∈ Bihom K k c', kappa K k d A = tt K k ^ (d - c') * g := by
    rcases Nat.lt_or_ge c d with hcd | hdc
    · let W : Submodule K (Pol K k) := WW.map (kappa K k d)
      have hW : W ≤ Bihom K k (c + (d - c)) := by
        have e : c + (d - c) = d := by omega
        rw [e]
        rintro f ⟨A', _, rfl⟩
        exact hB K k d A'
      have hWst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W := by
        rintro f ⟨A', hA', rfl⟩ a b
        rw [← kappa_ad hL hR K k d a b A']
        exact Submodule.mem_map_of_mem (hst A' hA' a b)
      have hWwt : ∀ f ∈ W, WtLe K k c f := by
        have hWeq : W = Submodule.span K (kappa K k d '' Sg) := by
          show WW.map (kappa K k d) = _
          rw [hspan, Submodule.map_span]
        rw [hWeq]
        apply wtLe_span
        rintro f ⟨A', hA', rfl⟩ m hm a
        obtain ⟨ω, hω, hωc⟩ := heig A' hA'
        have h1 : Rop K k a a (kappa K k d A') = (ω a : K) • kappa K k d A' := by
          rw [← kappa_ad hL hR K k d a a A', hω a, map_smul]
        have h2 := hE K k a (ω a) (kappa K k d A') h1 m hm
        rw [h2]
        exact_mod_cast hωc a
      obtain ⟨g, hg, he⟩ := divide_all hV hD hRB hRT hTW K k c (d - c) W hW hWst hWwt _
        (Submodule.mem_map_of_mem hA)
      exact ⟨c, le_rfl, hcd.le, g, hg, he⟩
    · exact ⟨d, hdc, le_rfl, kappa K k d A, hB K k d A, by simp⟩
  obtain ⟨c', hc'c, hc'd, g, hg, he⟩ := key
  have hsurj := hS K k d c' hc'd g hg
  rw [← he] at hsurj
  obtain ⟨B, hB', hBe⟩ := Submodule.mem_map.1 hsurj
  have hAB : B = A := hI K k d hBe
  subst hAB
  have hmono : Wc K k d c' ≤ Wc K k d c := by
    unfold Wc
    apply Submodule.span_mono
    rintro Bx ⟨l, hl, rfl⟩
    exact ⟨l, le_trans hl hc'c, rfl⟩
  exact hmono hB'

end PI.OpWords
end
end

section

open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] {k d : ℕ}

lemma mapDomain_inl_add_inr (u g : Fin k →₀ ℕ) :
    u.mapDomain Sum.inl + g.mapDomain Sum.inr = Finsupp.sumElim u g := by
  ext v
  rcases v with i | i
  · simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective, Finsupp.mapDomain_notin_range]
  · simp [Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_notin_range]

lemma sumElim_inj {u g u' g' : Fin k →₀ ℕ} :
    Finsupp.sumElim u g = Finsupp.sumElim u' g' ↔ u = u' ∧ g = g' := by
  constructor
  · intro h
    constructor
    · ext i
      have h1 := congrArg (fun f => f (Sum.inl i)) h
      simpa using h1
    · ext i
      have h1 := congrArg (fun f => f (Sum.inr i)) h
      simpa using h1
  · rintro ⟨rfl, rfl⟩
    rfl

lemma exists_sumElim (n : Fin k ⊕ Fin k →₀ ℕ) : ∃ m g : Fin k →₀ ℕ, n = Finsupp.sumElim m g := by
  refine ⟨Finsupp.comapDomain Sum.inl n Sum.inl_injective.injOn,
    Finsupp.comapDomain Sum.inr n Sum.inr_injective.injOn, ?_⟩
  ext v
  rcases v with i | i <;> simp [Finsupp.comapDomain_apply]

lemma pol_ext {P Q : Pol K k}
    (h : ∀ m g : Fin k →₀ ℕ, AddMonoidAlgebra.coeff P (Finsupp.sumElim m g) = AddMonoidAlgebra.coeff Q (Finsupp.sumElim m g)) : P = Q := by
  ext n
  obtain ⟨m, g, rfl⟩ := exists_sumElim n
  exact h m g

lemma sumElim_sub_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g - single (Sum.inr b) 1 = Finsupp.sumElim m (g - single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]

lemma sumElim_add_single_inr (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g + single (Sum.inr b) 1 = Finsupp.sumElim m (g + single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]

lemma coeff_term (P : MvPolynomial (Fin k) K) (m g g' : Fin k →₀ ℕ) :
    AddMonoidAlgebra.coeff (rename Sum.inl P * monomial (g'.mapDomain Sum.inr) (1 : K)) (Finsupp.sumElim m g) =
      if g' = g then AddMonoidAlgebra.coeff P m else 0 := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [rename_monomial, monomial_mul, mapDomain_inl_add_inr]
    simp only [coeff_monomial, sumElim_inj, mul_one]
    by_cases h1 : u = m <;> by_cases h2 : g' = g <;> simp [h1, h2]
  next p q hp hq =>
    rw [map_add (f := _), add_mul, MvPolynomial.coeff_add, hp, hq]
    split_ifs <;> simp [MvPolynomial.coeff_add]

lemma mono_val (g : Fin k →₀ ℕ) :
    (mono K k d g : MvPolynomial (Fin k) K) = if g.degree = d then monomial g 1 else 0 := by
  unfold mono
  split_ifs <;> rfl

lemma mem_antidiag_iff (g : Fin k →₀ ℕ) :
    g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d ↔ g.degree = d := by
  rw [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  simp

lemma kappa_apply (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d A = ∑ g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d,
      invFact K g • (rename Sum.inl ((A (mono K k d g) : MvPolynomial (Fin k) K)) *
        monomial (g.mapDomain Sum.inr) (1 : K)) := by
  simp [kappa]

lemma coeff_kappa (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) (m g : Fin k →₀ ℕ) :
    AddMonoidAlgebra.coeff (kappa K k d A) (Finsupp.sumElim m g) =
      invFact K g * AddMonoidAlgebra.coeff (A (mono K k d g) : MvPolynomial (Fin k) K) m := by
  classical
  rw [kappa_apply, coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeff_term, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_antidiag_iff] at h
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dite_eq_right h]
    rw [h0, map_zero]
    simp

lemma degree_of_coeff_ne (F : ↥(homogeneousSubmodule (Fin k) K d)) {m : Fin k →₀ ℕ}
    (h : AddMonoidAlgebra.coeff (F : MvPolynomial (Fin k) K) m ≠ 0) : m.degree = d := by
  have hF := (mem_homogeneousSubmodule d _).1 F.2
  rw [Finsupp.degree_eq_weight_one]
  exact hF h

lemma eq_sum_mono (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    F = ∑ g ∈ (F : MvPolynomial (Fin k) K).support,
      AddMonoidAlgebra.coeff (F : MvPolynomial (Fin k) K) g • mono K k d g := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  conv_lhs => rw [(F : MvPolynomial (Fin k) K).as_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Submodule.coe_smul, mono_val, if_pos (degree_of_coeff_ne F (MvPolynomial.mem_support_iff.1 hg)),
    smul_monomial, smul_eq_mul, mul_one]

lemma prodFact_fintype (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) = ∏ i, ((g i).factorial : K) := by
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

lemma prodFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) :
    g.prod (fun _ n => (n.factorial : K)) ≠ 0 := by
  rw [prodFact_fintype]
  exact Finset.prod_ne_zero_iff.2 (fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

lemma invFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) : invFact K g ≠ 0 := by
  unfold invFact
  exact inv_ne_zero (prodFact_ne_zero g)

lemma prodFact_add_single (g : Fin k →₀ ℕ) (i : Fin k) :
    (g + single i 1).prod (fun _ n => (n.factorial : K)) =
      ((g i : K) + 1) * g.prod (fun _ n => (n.factorial : K)) := by
  rw [prodFact_fintype, prodFact_fintype, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i, (((g + single i 1 : Fin k →₀ ℕ) j).factorial : K) =
      ∏ j ∈ Finset.univ.erase i, ((g j).factorial : K) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    simp [Finsupp.single_apply, Finset.ne_of_mem_erase hj, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [h1, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

lemma invFact_add_single [CharZero K] (g : Fin k →₀ ℕ) (i : Fin k) :
    invFact K (g + single i 1) * ((g i : K) + 1) = invFact K g := by
  unfold invFact
  rw [prodFact_add_single, mul_inv]
  have h1 : ((g i : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (g i)
  rw [mul_comm ((g i : K) + 1)⁻¹ _, mul_assoc, inv_mul_cancel₀ h1, mul_one]

lemma degree_sub_add (g : Fin k →₀ ℕ) (a b : Fin k) (hb : g b ≠ 0) :
    (g - single b 1 + single a 1).degree = g.degree := by
  have hle : single b 1 ≤ g := by
    rw [Finsupp.single_le_iff]
    omega
  have hs : ∀ c : Fin k, (single c 1 : Fin k →₀ ℕ).degree = 1 := fun c => by
    rw [Finsupp.degree_eq_sum]
    simp [Finsupp.single_apply]
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add (f := _), map_add (f := _), hs, hs]

lemma Ed_val (a b : Fin k) (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    (Formalism.MainNotions.TestSideCounting.Ed K k d a b F : MvPolynomial (Fin k) K) = X a * pderiv b (F : MvPolynomial (Fin k) K) :=
  rfl

lemma Ed_mono (a b : Fin k) (g : Fin k →₀ ℕ) :
    Formalism.MainNotions.TestSideCounting.Ed K k d a b (mono K k d g) =
      ((g b : ℕ) : K) • mono K k d (g - single b 1 + single a 1) := by
  apply Subtype.ext
  rw [Ed_val, Submodule.coe_smul, mono_val, mono_val]
  by_cases hb : g b = 0
  · split_ifs <;> simp [pderiv_monomial, hb]
  · rw [degree_sub_add g a b hb]
    split_ifs with h
    · rw [pderiv_monomial, X, monomial_mul, smul_monomial, add_comm (Finsupp.single a 1)]
      simp
    · simp

lemma pderiv_inl_xi (b : Fin k) (g : Fin k →₀ ℕ) :
    pderiv (Sum.inl b) (monomial (g.mapDomain Sum.inr) (1 : K) : Pol K k) = 0 := by
  simp [pderiv_monomial, Finsupp.mapDomain_notin_range]

lemma weight_wx (m g : Fin k →₀ ℕ) : Finsupp.weight (wx k) (Finsupp.sumElim m g) = m.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type, Finsupp.degree_eq_sum]

lemma weight_wxi (m g : Fin k →₀ ℕ) : Finsupp.weight (wxi k) (Finsupp.sumElim m g) = g.degree := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wxi, Fintype.sum_sum_type, Finsupp.degree_eq_sum]

end PI.OpWords
end
end
