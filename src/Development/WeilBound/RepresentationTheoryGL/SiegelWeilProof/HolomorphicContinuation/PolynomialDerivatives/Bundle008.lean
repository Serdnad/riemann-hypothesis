module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle007
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
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem kAlg_of_adjoin_restrict (ε : Fin m → Bool) (V : Submodule ℂ (PX m n))
    (hK : ∀ ij : Fin n × Fin n, ∀ f ∈ V, KopL ε ij.1 ij.2 f ∈ V) (y : Module.End ℂ V)
    (hy : y ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (KopL ε ij.1 ij.2).restrict (hK ij))) :
    ∃ w ∈ kAlg ε, ∀ v : V, w v = (y v : PX m n) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ij, rfl⟩ := hx
    exact ⟨KopL ε ij.1 ij.2, Algebra.subset_adjoin ⟨ij, rfl⟩, fun v => rfl⟩
  | algebraMap r =>
    exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun v => by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨w₁, h₁, e₁⟩ := hx
    obtain ⟨w₂, h₂, e₂⟩ := hy
    exact ⟨w₁ + w₂, Subalgebra.add_mem _ h₁ h₂, fun v => by simp [e₁, e₂]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w₁, h₁, e₁⟩ := hx
    obtain ⟨w₂, h₂, e₂⟩ := hy
    refine ⟨w₁ * w₂, Subalgebra.mul_mem _ h₁ h₂, fun v => ?_⟩
    simp only [Module.End.mul_apply]
    rw [e₂, ← e₁ (y v)]

theorem coreLC_of' (hBi : Bicomm) (hEL : EquivLift) (hRep : RepB) (hFF : FormFacts) : CoreLC := by
  intro m n ε c hc Λ hΛ p
  classical
  obtain ⟨B, hBbox, hBrep, hBcomm⟩ := hRep m n ε c hc Λ hΛ
  obtain ⟨hherm, hpos, hadj, hKbox, -⟩ := hFF m n ε c hc
  set R : Finset (Fin m → ℕ) := p.support.image (rdeg ε) with hR
  set V := box (n := n) ε (R : Set (Fin m → ℕ)) with hV
  haveI : FiniteDimensional ℂ V := box_finiteDimensional ε R
  have hKV : ∀ ij : Fin n × Fin n, ∀ f ∈ V, KopL ε ij.1 ij.2 f ∈ V := fun ij f hf => hKbox ij.1 ij.2 _ f hf
  have hBV : ∀ f ∈ V, B f ∈ V := fun f hf => hBbox _ f hf
  have hBF : ∀ f ∈ F1 ε, B f ∈ F1 ε := fun f hf => by
    have := hBbox Set.univ f (first_family_le_box ε hf)
    exact box_le_first_family ε _ this
  let T : Fin n × Fin n → Module.End ℂ V := fun ij => (KopL ε ij.1 ij.2).restrict (hKV ij)
  let x : Module.End ℂ V := B.restrict hBV
  have key : x ∈ Algebra.adjoin ℂ (Set.range T) := by
    refine hBi V (fun v w => fform c (v : PX m n) w) (fun v w₁ w₂ => by simp [fform_add_right])
      (fun v w r => by simp [fform_smul_right]) (fun v w => hherm _ _)
      (fun v hv => hpos _ (by simpa using hv)) (Fin n × Fin n) T
      (fun ij => ⟨(ij.2, ij.1), fun v w => hadj ij.1 ij.2 v w⟩) x ?_
    intro t ht
    obtain ⟨q, hq⟩ := V.exists_isCompl
    let t' : Module.End ℂ (PX m n) := V.subtype ∘ₗ t ∘ₗ V.linearProjOfIsCompl q hq
    have ht' : ∀ f (hf : f ∈ V), t' f = (t ⟨f, hf⟩ : PX m n) := fun f hf => by
      have e0 := Submodule.linearProjOfIsCompl_apply_left hq ⟨f, hf⟩
      simp only [t', LinearMap.comp_apply, Submodule.coe_subtype]
      exact congrArg (fun v => ((t v : V) : PX m n)) e0
    have h1 : ∀ f ∈ box ε (R : Set (Fin m → ℕ)), t' f ∈ box ε (R : Set (Fin m → ℕ)) := fun f hf => by
      rw [ht' f hf]; exact (t ⟨f, hf⟩).2
    have h2 : ∀ i j, ∀ f ∈ box ε (R : Set (Fin m → ℕ)), t' (KopL ε i j f) = KopL ε i j (t' f) := by
      intro i j f hf
      have e := congrArg Subtype.val (LinearMap.congr_fun (ht (i, j)) ⟨f, hf⟩)
      simp only [Module.End.mul_apply, LinearMap.restrict_apply, LinearMap.restrict_coe_apply, T] at e
      rw [ht' _ (hKV (i, j) f hf), ht' f hf]
      exact e
    obtain ⟨w, hw, hwt⟩ := hEL m n ε c hc R t' h1 h2
    obtain ⟨-, hBw⟩ := adjoin_first_operators_preserves_family ε c B hBF hBcomm w hw
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [Module.End.mul_apply, x, LinearMap.restrict_coe_apply]
    have hv1 : (t v : PX m n) = w v := by rw [← hwt v v.2, ht' v v.2]
    have hv2 : (t (B.restrict hBV v) : PX m n) = w (B v) := by
      rw [← hwt (B v) (hBV v v.2), ht' (B v) (hBV v v.2)]; rfl
    rw [hv1, hv2, hBw v (box_le_first_family ε _ v.2)]
  obtain ⟨w, hw, hwB⟩ := kAlg_of_adjoin_restrict ε V hKV x key
  refine ⟨w, hw, ?_⟩
  have hterm : ∀ s ∈ p.support, Λ (monomial s (p.coeff s)) = contr c (w (monomial s (p.coeff s))) := by
    intro s hs
    obtain ⟨e, h1, h2⟩ := monomial_split ε s (p.coeff s)
    have hsub : ({rdeg ε s} : Set (Fin m → ℕ)) ⊆ (R : Set (Fin m → ℕ)) := by
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      rw [hr, hR, Finset.coe_image]
      exact Set.mem_image_of_mem _ hs
    have h1V : (monomial (s.filter (inF1 ε)) 1 : PX m n) ∈ V := box_mono ε hsub h1
    rw [e, hBrep _ (box_le_first_family ε _ h1) _ h2, compact_algebra_mul_second_family ε w hw _ _ h2]
    congr 2
    exact (hwB ⟨_, h1V⟩).symm
  have eL : Λ p = ∑ s ∈ p.support, Λ (monomial s (p.coeff s)) := by

    rw [← map_sum]; congr 1; exact p.as_sum
  have eR : contr c (w p) = ∑ s ∈ p.support, contr c (w (monomial s (p.coeff s))) := by
    show contrL c (w p) = ∑ s ∈ p.support, contrL c (w (monomial s (p.coeff s)))

    rw [← map_sum (contrL c), ← map_sum w]; congr 2; exact p.as_sum
  rw [eL, eR]
  exact Finset.sum_congr rfl hterm

end PositivityTheory.Rg.Sw.LC.Core
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ} {ε : Fin m → Bool}

def Good (ε : Fin m → Bool) (d : ℕ) (r : Sym m n) : Prop := SymbolInFirstFamily ε r ∧ EtaLt r d

theorem good_zero (d : ℕ) : Good ε d (0 : Sym m n) := by
  constructor <;> intro t ht <;> simp at ht

theorem good_add {d : ℕ} {r₁ r₂ : Sym m n} (h₁ : Good ε d r₁) (h₂ : Good ε d r₂) : Good ε d (r₁ + r₂) := by
  classical
  constructor
  · intro t ht k hk
    rcases Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h
    · exact h₁.1 t h k hk
    · exact h₂.1 t h k hk
  · intro t ht
    rcases Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h
    · exact h₁.2 t h
    · exact h₂.2 t h

theorem good_smul {d : ℕ} {r : Sym m n} (a : ℂ) (h : Good ε d r) : Good ε d (a • r) :=
  ⟨fun t ht => h.1 t (MvPolynomial.support_smul ht), fun t ht => h.2 t (MvPolynomial.support_smul ht)⟩

theorem good_sum {ι : Type*} (S : Finset ι) {d : ℕ} (r : ι → Sym m n) (h : ∀ i ∈ S, Good ε d (r i)) :
    Good ε d (∑ i ∈ S, r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using good_zero d
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact good_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mem_support_mul_monomial {p : Sym m n} {s t' : Ix m n ⊕ Ix m n →₀ ℕ} {a : ℂ}
    (h : t' ∈ (p * monomial s a).support) : ∃ t ∈ p.support, t' = t + s := by
  rw [MvPolynomial.mem_support_iff, coeff_mul_monomial'] at h
  split_ifs at h with hs
  · refine ⟨t' - s, ?_, (tsub_add_cancel_of_le hs).symm⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0; rw [h0, zero_mul] at h; exact h rfl
  · exact absurd rfl h

theorem good_mul_monomial {d e : ℕ} {r : Sym m n} (h : Good ε d r) (s : Ix m n ⊕ Ix m n →₀ ℕ)
    (hs : ∀ k, (s (Sum.inl k) ≠ 0 ∨ s (Sum.inr k) ≠ 0) → inF1 ε k) (he : (∑ k, s (Sum.inr k)) ≤ e) :
    Good ε (d + e) (r * monomial s 1) := by
  constructor
  · intro t' ht' k hk
    obtain ⟨t, ht, rfl⟩ := mem_support_mul_monomial ht'
    simp only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk
    by_cases h1 : t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0
    · exact h.1 t ht k h1
    · push_neg at h1
      apply hs k
      rcases hk with hk | hk
      · rcases hk with hk | hk
        · exact absurd h1.1 hk
        · exact Or.inl hk
      · rcases hk with hk | hk
        · exact absurd h1.2 hk
        · exact Or.inr hk
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := mem_support_mul_monomial ht'
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    exact add_lt_add_of_lt_of_le (h.2 t ht) he

theorem mem_support_pderiv {u : Sym m n} {i : Ix m n ⊕ Ix m n} {t' : Ix m n ⊕ Ix m n →₀ ℕ}
    (h : t' ∈ (pderiv i u).support) : ∃ t ∈ u.support, t i ≠ 0 ∧ t = t' + Finsupp.single i 1 := by
  classical
  have hu : pderiv i u = ∑ t ∈ u.support, monomial (t - Finsupp.single i 1) (AddMonoidAlgebra.coeff u t * (t i : ℂ)) := by
    conv_lhs => rw [u.as_sum]

    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  rw [MvPolynomial.mem_support_iff, hu, coeff_sum] at h
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_monomial] at hne
  split_ifs at hne with heq
  · have hti : t i ≠ 0 := by
      intro h0; rw [h0] at hne; simp at hne
    refine ⟨t, ht, hti, ?_⟩
    rw [← heq, tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]; omega
  · exact absurd rfl hne

theorem good_pderiv {d : ℕ} {u : Sym m n} (hu : SymbolInFirstFamily ε u) (hue : EtaLe u d) (k : Ix m n) :
    Good ε d (pderiv (Sum.inr k) u) := by
  constructor
  · intro t' ht' j hj
    obtain ⟨t, ht, -, rfl⟩ := mem_support_pderiv ht'
    apply hu _ ht j
    simp only [Finsupp.add_apply, ne_eq] at hj ⊢
    omega
  · intro t' ht'
    obtain ⟨t, ht, hti, rfl⟩ := mem_support_pderiv ht'
    have h1 := hue _ ht
    have h3 : ∑ j, t' (Sum.inr j) + 1 ≤ d := by
      simpa [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply] using h1
    omega

theorem good_le {d : ℕ} {r : Sym m n} (h : Good ε d r) : EtaLe r d := fun t ht => (h.2 t ht).le

theorem first_family_symbol_mul_variable_pow {u : Sym m n} (hu : SymbolInFirstFamily ε u) {a : Ix m n} (ha : inF1 ε a) (b : ℕ) :
    SymbolInFirstFamily ε (u * X (Sum.inl a) ^ b) ∧ ∀ d, EtaLe u d → EtaLe (u * X (Sum.inl a) ^ b) d := by
  have hs : ∀ k, ((Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
      (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
    intro k hk
    simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
    split_ifs at hk with h
    · subst h; exact ha
    · exact absurd rfl hk
  have h0 : (∑ k, (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ 0 := by
    simp [Finsupp.single_apply]
  rw [X_pow_eq_monomial]
  refine ⟨?_, fun d hd => ?_⟩
  · intro t ht k hk
    obtain ⟨t0, ht0, rfl⟩ := mem_support_mul_monomial ht
    simp only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk
    by_cases h1 : t0 (Sum.inl k) ≠ 0 ∨ t0 (Sum.inr k) ≠ 0
    · exact hu t0 ht0 k h1
    · push_neg at h1
      apply hs k
      rcases hk with hk | hk
      · rcases hk with hk | hk
        · exact absurd h1.1 hk
        · exact Or.inl hk
      · rcases hk with hk | hk
        · exact absurd h1.2 hk
        · exact Or.inr hk
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := mem_support_mul_monomial ht
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    calc _ ≤ d + 0 := add_le_add (hd t0 ht0) h0
      _ = d := add_zero d

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

namespace CoreD

variable {m n : ℕ} {ε : Fin m → Bool}

def psi (p q : Sym m n) : ℂ :=
  ∑ u ∈ p.support ∪ q.support, star (p.coeff u) * q.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ)

theorem psi_eq (p q : Sym m n) (T : Finset _) (h : p.support ∪ q.support ⊆ T) :
    psi p q = ∑ u ∈ T, star (p.coeff u) * q.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ) := by
  unfold psi
  refine Finset.sum_subset h fun u _ hu => ?_
  rw [Finset.mem_union, not_or, mem_support_iff, mem_support_iff, not_not, not_not] at hu
  simp [hu.1, hu.2]

theorem psi_add_right (p q₁ q₂ : Sym m n) : psi p (q₁ + q₂) = psi p q₁ + psi p q₂ := by
  classical
  have h0 : (q₁ + q₂).support ⊆ q₁.support ∪ q₂.support := support_add
  rw [psi_eq p (q₁ + q₂) (p.support ∪ q₁.support ∪ q₂.support) (by
      intro u hu; rcases Finset.mem_union.1 hu with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · rcases Finset.mem_union.1 (h0 h) with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ h'),
    psi_eq p q₁ (p.support ∪ q₁.support ∪ q₂.support) (Finset.union_subset_left le_rfl),
    psi_eq p q₂ (p.support ∪ q₁.support ∪ q₂.support)
      (Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem psi_herm (p q : Sym m n) : psi q p = star (psi p q) := by
  unfold psi
  rw [Finset.union_comm, star_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [star_mul', star_star, star_prod, star_natCast]
  ring

theorem psi_pos (p : Sym m n) (hp : p ≠ 0) : 0 < (psi p p).re := by
  unfold psi
  rw [Finset.union_self, Complex.re_sum]
  have hterm : ∀ u, (star (p.coeff u) * p.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ)).re =
      Complex.normSq (p.coeff u) * ∏ k ∈ u.support, ((u k).factorial : ℝ) := by
    intro u
    have : star (p.coeff u) * p.coeff u = (Complex.normSq (p.coeff u) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this, show (∏ k ∈ u.support, ((u k).factorial : ℂ)) = ((∏ k ∈ u.support, ((u k).factorial : ℝ) : ℝ) : ℂ) by
      push_cast; rfl, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hterm]
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hp)
  refine Finset.sum_pos' (fun v _ => mul_nonneg (Complex.normSq_nonneg _)
    (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)) ⟨u, hu, mul_pos ?_ (Finset.prod_pos fun _ _ => by
      exact_mod_cast Nat.factorial_pos _)⟩
  exact Complex.normSq_pos.2 (mem_support_iff.1 hu)

theorem psi_sum_right {ι : Type*} (p : Sym m n) (F : Finset ι) (f : ι → Sym m n) :
    psi p (∑ x ∈ F, f x) = ∑ x ∈ F, psi p (f x) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [psi]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, psi_add_right, ih]

theorem psi_sum_left {ι : Type*} (p : Sym m n) (F : Finset ι) (f : ι → Sym m n) :
    psi (∑ x ∈ F, f x) p = ∑ x ∈ F, psi (f x) p := by
  rw [psi_herm, psi_sum_right, star_sum]
  exact Finset.sum_congr rfl fun x _ => (psi_herm _ _).symm


variable (ε) in
def Om : Module.End ℂ (Sym m n) :=
  ∑ ij : Fin n × Fin n, (symK ε ij.1 ij.2).toLinearMap * (symK ε ij.2 ij.1).toLinearMap

theorem Om_apply (s : Sym m n) : Om ε s = ∑ ij : Fin n × Fin n, symK ε ij.1 ij.2 (symK ε ij.2 ij.1 s) := by
  simp [Om, LinearMap.sum_apply]

theorem Om_mem {N : ℕ} {s : Sym m n} (hs : s ∈ S ε N) : Om ε s ∈ S ε N := by
  rw [Om_apply]
  exact Submodule.sum_mem _ fun ij _ => symK_mem _ _ (symK_mem _ _ hs)


variable (ε) in
def OmS (N : ℕ) : Module.End ℂ (S (n := n) ε N) := (Om ε).restrict fun _ hs => Om_mem hs

section adj

variable (hadj : ∀ (i j : Fin n) (s t : Sym m n), psi (symK ε i j s) t = psi s (symK ε j i t))
include hadj

theorem psi_Om (a b : Sym m n) : psi (Om ε a) b = psi a (Om ε b) := by
  rw [Om_apply, Om_apply, psi_sum_left, psi_sum_right]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [hadj, ← hadj ij.2 ij.1]

theorem psi_Om_diag (a : Sym m n) : psi a (Om ε a) = ∑ ij : Fin n × Fin n, psi (symK ε ij.2 ij.1 a) (symK ε ij.2 ij.1 a) := by
  rw [Om_apply, psi_sum_right]
  exact Finset.sum_congr rfl fun ij _ => (hadj ij.2 ij.1 a _).symm

theorem symK_eq_zero_of_Om (a : Sym m n) (h : Om ε a = 0) (i j : Fin n) : symK ε i j a = 0 := by
  have h0 := psi_Om_diag hadj a
  rw [h, show psi a 0 = 0 by simp [psi]] at h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hnn : ∀ ij ∈ (Finset.univ : Finset (Fin n × Fin n)),
      0 ≤ (psi (symK ε ij.2 ij.1 a) (symK ε ij.2 ij.1 a)).re := fun ij _ => by
    by_cases hz : symK ε ij.2 ij.1 a = 0
    · rw [hz]; simp [psi]
    · exact (psi_pos _ hz).le
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hre.symm (j, i) (Finset.mem_univ _)
  by_contra hz
  exact (psi_pos _ hz).ne' this

theorem ker_inf_range {N : ℕ} (v : S (n := n) ε N) (h0 : OmS ε N v = 0) (h1 : ∃ u, OmS ε N u = v) : v = 0 := by
  obtain ⟨u, rfl⟩ := h1
  have h0' : Om ε (OmS ε N u).1 = 0 := congrArg Subtype.val h0
  have : psi (OmS ε N u).1 (OmS ε N u).1 = 0 := by
    change psi (Om ε u.1) (Om ε u.1) = 0
    rw [psi_Om hadj]
    change psi u.1 (Om ε (OmS ε N u).1) = 0
    rw [h0']; simp [psi]
  by_contra hne
  have hne' : (OmS ε N u).1 ≠ 0 := fun h => hne (Subtype.ext h)
  exact (psi_pos _ hne').ne' (by rw [this]; simp)

theorem pow_kill {N : ℕ} (k : ℕ) (v : S (n := n) ε N) (h : (OmS ε N ^ (k + 1)) v = 0) : OmS ε N v = 0 := by
  induction k generalizing v with
  | zero => simpa using h
  | succ k ih =>
    have h' : (OmS ε N ^ (k + 1)) (OmS ε N v) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ]; exact h
    exact ker_inf_range hadj _ (ih _ h') ⟨v, rfl⟩

theorem exists_q (N : ℕ) : ∃ q : Polynomial ℂ, q.eval 0 = 1 ∧ ∀ v, OmS ε N (Polynomial.aeval (OmS (n := n) ε N) q v) = 0 := by
  set T := OmS (n := n) ε N
  have hp : T.charpoly ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  obtain ⟨g, hpg, hg⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd _ hp 0
  rw [map_zero, sub_zero] at hpg hg
  have hg0 : g.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]; exact fun h => hg (Polynomial.X_dvd_iff.2 h)
  refine ⟨Polynomial.C (g.eval 0)⁻¹ * g, by simp [hg0], fun v => ?_⟩
  have hz : (Polynomial.aeval T T.charpoly) v = 0 := by rw [LinearMap.aeval_self_charpoly]; rfl
  rw [hpg, map_mul, map_pow, Polynomial.aeval_X, Module.End.mul_apply] at hz
  rw [map_mul, Module.End.mul_apply, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  rcases Nat.eq_zero_or_pos (Polynomial.rootMultiplicity 0 T.charpoly) with hk | hk
  · rw [hk, pow_zero, Module.End.one_apply] at hz
    rw [hz, map_zero, smul_zero]
  · obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_lt hk
    rw [hk', zero_add] at hz
    rw [pow_kill hadj k _ hz, smul_zero]

end adj

end CoreD

end PositivityTheory.Rg.Sw.LC
end
end
