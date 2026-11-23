module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitObj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem GeneratedAmple.proof (hCover : AmpleCover.Statement.{u, w})
    (hLocal : AmpleTwistLocal.Statement.{u, w}) : GeneratedAmple.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q
  choose n₀ hn₀ using fun (b : Fin A.m) (j : Fin (A.r + 1)) => hLocal S Ω N x H A Q b j
  let M : ℕ := Finset.univ.sup fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2
  refine ⟨A.m * M, fun c hc => hCover S Ω N x H A _ fun j I y hy => ?_⟩
  have hm := A.m_pos
  have hc' : c % A.m + A.m * (c / A.m) = c := Nat.mod_add_div c A.m
  have hM : M ≤ c / A.m := (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hc)
  have hn : n₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j ≤ c / A.m :=
    le_trans (Finset.le_sup (f := fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2)
      (Finset.mem_univ (⟨c % A.m, Nat.mod_lt c hm⟩, j))) hM
  have key := hn₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j (c / A.m) hn I y
  simp only [hc'] at key
  exact key hy

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem TwistVanish.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun b c hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c 1
  have := hc₀ 1 le_rfl c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise

noncomputable section

universe u w

section Chart

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)

def twLocPart (M₀ : FinGradedSub (S := S) (x := x) Ω) (b c : ℤ) (I : Finset (Fin (N + 1))) :
    Submodule S Ω :=
  Submodule.span S {y | ∃ (z : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I ∧ s.IsHomogeneous e ∧
    z ∈ twPart η M₀ a b ∧ a - e = c ∧ y = (aeval x s)⁻¹ * z}

theorem twLocPart_eta_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {b c : ℤ} {I : Finset (Fin (N + 1))}
    (j : Fin (r + 1)) {y : Ω} (hy : y ∈ twLocPart η M₀ b c I) : η j * y ∈ twLocPart η M₀ (b + 1) c I := by
  refine Submodule.span_induction (p := fun y _ => η j * y ∈ twLocPart η M₀ (b + 1) c I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s, a, e, hs, hse, hz, hae, rfl⟩
    refine Submodule.subset_span ⟨η j * z, s, a, e, hs, hse, twPart_eta_mul η M₀ j hz, hae, ?_⟩
    ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
  · intro c' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' hu

theorem twLocPart_chart_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {b c : ℤ} (K : Chart x)
    (a : chartRing S x K) {y : Ω} (hy : y ∈ twLocPart η M₀ b c K.1) : (a : Ω) * y ∈ twLocPart η M₀ b c K.1 := by
  obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
  rw [ha]
  refine Submodule.span_induction (p := fun y _ => aeval x f / aeval x s * y ∈ twLocPart η M₀ b c K.1)
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s₁, a₁, e₁, hs₁, hse₁, hz, hae, rfl⟩
    refine Submodule.subset_span ⟨aeval x f * z, s * s₁, a₁ + e, e + e₁, mul_mem hs hs₁, hse.mul hse₁,
      twPart_form_mul η M₀ hf hz, by push_cast; omega, ?_⟩
    rw [map_mul, mul_inv, div_eq_mul_inv]
    ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
  · intro c' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' hu

def twLocPartA (M₀ : FinGradedSub (S := S) (x := x) Ω) (b c : ℤ) (K : Chart x) :
    Submodule (chartRing S x K) Ω where
  carrier := twLocPart η M₀ b c K.1
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  smul_mem' a y hy := by rw [chartRing_smul_def]; exact twLocPart_chart_mul η M₀ K a hy

theorem mul_mem_of_mem_span {K : Chart x} (T : Submodule (chartRing S x K) Ω) {s t : Set Ω} (w : Ω)
    (h : ∀ u ∈ s, ∀ v ∈ t, w * (u * v) ∈ T) {u v : Ω} (hu : u ∈ Submodule.span (chartRing S x K) s)
    (hv : v ∈ Submodule.span (chartRing S x K) t) : w * (u * v) ∈ T := by
  induction hu using Submodule.span_induction generalizing v with
  | mem u hu =>
    induction hv using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => rw [mul_zero, mul_zero]; exact T.zero_mem
    | add v v' _ _ h₁ h₂ => rw [mul_add, mul_add]; exact T.add_mem h₁ h₂
    | smul a v _ h₁ =>
      have : w * (u * (a • v)) = a • (w * (u * v)) := by rw [chartRing_smul_def, chartRing_smul_def]; ring
      rw [this]; exact T.smul_mem a h₁
  | zero => rw [zero_mul, mul_zero]; exact T.zero_mem
  | add u u' _ _ h₁ h₂ => rw [add_mul, mul_add]; exact T.add_mem (h₁ hv) (h₂ hv)
  | smul a u _ h₁ =>
    have : w * ((a • u) * v) = a • (w * (u * v)) := by rw [chartRing_smul_def, chartRing_smul_def]; ring
    rw [this]; exact T.smul_mem a (h₁ hv)

variable {G B : SubSystem S x Ω}

theorem pow_sub_le_span (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x)
    (n : ℕ) : (B.pow n).sub K ≤ Submodule.span (chartRing S x K) (Set.range η ^ n) := by
  induction n with
  | zero =>
    change twistMod S x 0 K ≤ _
    rw [twistMod, Submodule.span_le]
    rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    have he : e' = e := by omega
    subst he
    have hmem : aeval x f / aeval x s ∈ chartRing S x K := ⟨f, s, e', hs, hf, hse, rfl⟩
    have h1 : (1 : Ω) ∈ Submodule.span (chartRing S x K) (Set.range η ^ 0) :=
      Submodule.subset_span (by rw [pow_zero]; exact Set.mem_one.mpr rfl)
    have := Submodule.smul_mem _ (⟨_, hmem⟩ : chartRing S x K) h1
    rwa [chartRing_smul_def, mul_one] at this
  | succ n ih =>
    change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hB K] at hq
    have := mul_mem_of_mem_span (Submodule.span (chartRing S x K) (Set.range η ^ (n + 1))) 1
      (s := Set.range η) (t := Set.range η ^ n)
      (fun u hu v hv => by
        rw [one_mul, pow_succ']
        exact Submodule.subset_span (Set.mul_mem_mul hu hv)) hq (ih hy)
    rwa [one_mul, ← smul_eq_mul] at this

theorem range_pow_subset (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x)
    (n : ℕ) {q : Ω} (hq : q ∈ Set.range η ^ n) : q ∈ (B.pow n).sub K := by
  induction n generalizing q with
  | zero =>
    rw [pow_zero, Set.mem_one] at hq
    subst hq
    exact one_mem_twistMod_zero (S := S) K
  | succ n ih =>
    rw [pow_succ', Set.mem_mul] at hq
    obtain ⟨u, hu, v, hv, rfl⟩ := hq
    have hu' : u ∈ B.sub K := by rw [← hB K]; exact Submodule.subset_span hu
    exact Submodule.subset_span ⟨u, hu', v, ih hv, smul_eq_mul _ _⟩

variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

theorem twistSub_le_twLocPart (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    y ∈ twLocPart η M₀ n c K.1 := by
  change y ∈ twLocPartA η M₀ n c K
  revert y
  change Submodule.span _ _ ≤ twLocPartA η M₀ n c K
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, y', hy', rfl⟩
  rw [smul_eq_mul, ← one_mul (t * y')]
  refine mul_mem_of_mem_span _ 1 ?_ ht hy'
  rintro u ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩ v ⟨q, hq, g, hg, rfl⟩
  rw [one_mul, smul_eq_mul]
  rw [← hG K] at hg
  refine mul_mem_of_mem_span _ (aeval x f / aeval x s) ?_ (pow_sub_le_span η hB K n hq) hg
  rintro q' hq' _ ⟨m, s₁, a, e₁, hs₁, hse₁, hm, hae, rfl⟩
  refine Submodule.subset_span ⟨(aeval x f * m) * q', s * s₁, a + e', e + e₁, mul_mem hs hs₁,
    hse.mul hse₁, ?_, by push_cast; omega, ?_⟩
  · rw [twPart_of_nonneg]
    exact Submodule.subset_span (Set.mul_mem_mul (M₀.smul_mem e' a f m hf hm) hq')
  · rw [smul_eq_mul, map_mul, mul_inv, div_eq_mul_inv]
    ring

theorem twLocPart_le_twistSub (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ twLocPart η M₀ n c K.1) :
    y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K := by
  obtain ⟨i, hi⟩ := K.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (K.2.2 hi)
  set T := ((G.twist (B.pow n)).twist (twistSys S x c)).sub K with hT
  refine Submodule.span_induction (p := fun y _ => y ∈ T) ?_ (T.zero_mem) (fun _ _ _ _ h₁ h₂ => T.add_mem h₁ h₂)
    (fun r' y _ h => Submodule.smul_of_tower_mem T r' h) hy
  rintro _ ⟨z, s, a, e, hs, hse, hz, hae, rfl⟩
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos K hs
  rw [twPart_of_nonneg] at hz
  refine Submodule.span_induction (p := fun z _ => (aeval x s)⁻¹ * z ∈ T) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, hm, q, hq, rfl⟩
    have hq' := range_pow_subset η hB K n hq
    have hxc : x i ^ c ∈ twistMod S x c K := by
      rw [twistMod_eq_span c K hi]; exact Submodule.mem_span_singleton_self _
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have hg : (aeval x (s * X i ^ k))⁻¹ • m ∈ G.sub K := by
        rw [← hG K]
        exact Submodule.subset_span ⟨m, s * X i ^ k, a, e + k, mul_mem hs (pow_mem (X_mem_monos hi) k),
          hse.mul (isHomogeneous_X_pow i k), hm, by push_cast; omega, rfl⟩
      have hmem : x i ^ (k : ℤ) • (q • ((aeval x (s * X i ^ k))⁻¹ • m)) ∈ T :=
        Submodule.subset_span ⟨_, hxc, _, Submodule.subset_span ⟨q, hq', _, hg, rfl⟩, rfl⟩
      convert hmem using 1
      simp only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_natCast]
      field_simp
    · have hg : (aeval x s)⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ G.sub K := by
        rw [← hG K]
        exact Submodule.subset_span ⟨aeval x (X i ^ k : Poly S N) • m, s, a + k, e, hs, hse,
          M₀.smul_mem k a (X i ^ k : Poly S N) m (isHomogeneous_X_pow i k) hm, by omega, rfl⟩
      have hmem : x i ^ (-(k : ℤ)) • (q • ((aeval x s)⁻¹ • (aeval x (X i ^ k : Poly S N) • m))) ∈ T :=
        Submodule.subset_span ⟨_, hxc, _, Submodule.subset_span ⟨q, hq', _, hg, rfl⟩, rfl⟩
      convert hmem using 1
      simp only [smul_eq_mul, map_pow, aeval_X, zpow_neg, zpow_natCast]
      field_simp
  · rw [mul_zero]; exact T.zero_mem
  · intro u v _ _ hu hv; rw [mul_add]; exact T.add_mem hu hv
  · intro r' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_of_tower_mem T r' hu

end Chart

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KHFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def negSet (a : (Σ k, ι k) → ℤ) : ∀ k, Finset (ι k) :=
  fun k => Finset.univ.filter fun i => a ⟨k, i⟩ < 0

def blockSum (a : (Σ k, ι k) → ℤ) : K → ℤ :=
  fun k => ∑ i, a ⟨k, i⟩

def posExp (a : (Σ k, ι k) → ℤ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (a p).toNat

def negExp (a : (Σ k, ι k) → ℤ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (-a p).toNat

theorem monomial_negExp_mem (S : Type) [CommRing S] (I : ∀ k, Finset (ι k)) (a : (Σ k, ι k) → ℤ)
    (h : ∀ k, negSet a k ⊆ I k) : (monomial (negExp a) (1 : S) : MRingOver S ι) ∈ KH.cellMon S I := by
  classical
  rw [monomial_eq, C_1, one_mul, Finsupp.prod]
  refine Submonoid.prod_mem _ fun p hp => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  refine ⟨p.1, p.2, h p.1 ?_, rfl⟩
  have hp' : (negExp a) p ≠ 0 := Finsupp.mem_support_iff.mp hp
  simp only [negExp, Finsupp.coe_equivFunOnFinite_symm] at hp'
  simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and]
  show a p < 0
  omega


open Classical in
def monoFrac (S : Type) [CommRing S] (I : ∀ k, Finset (ι k)) (a : (Σ k, ι k) → ℤ) :
    LocalizedModule (KH.cellMon S I) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) :=
  if h : ∀ k, negSet a k ⊆ I k then
    LocalizedModule.mk (Ideal.Quotient.mk ⊥ (monomial (posExp a) 1))
      ⟨monomial (negExp a) 1, monomial_negExp_mem S I a h⟩
  else 0

def CombCell (ι : K → Type) (J : ∀ k, Finset (ι k)) (n : ℕ) : Type :=
  {I : KH.Cell K ι n // ∀ k, J k ⊆ I.1 k}

abbrev CombC (S : Type) (J : ∀ k, Finset (ι k)) (n : ℕ) : Type :=
  CombCell ι J n → S

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


open Classical in
def combD (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) (n : ℕ) :
    CombC S J n →ₗ[S] CombC S J (n + 1) :=
  LinearMap.pi fun I => ∑ k, ∑ i ∈ I.1.1 k,
    if h : ((∀ l, (Function.update I.1.1 k ((I.1.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1.1 k ((I.1.1 k).erase i) l).card - 1) = n) ∧
        ∀ l, J l ⊆ Function.update I.1.1 k ((I.1.1 k).erase i) l then
      KH.faceSign I.1.1 k i • LinearMap.proj (R := S) (φ := fun _ : CombCell ι J n => S)
        ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
    else 0

def combB (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) : (n : ℕ) → Submodule S (CombC S J n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (combD S J n)

end KHFree

namespace KHFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def singOne (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) (n : ℕ) : CombC S J n :=
  fun I => if ∀ k, J k = ∅ → (I.1.1 k).card = 1 then 1 else 0


open Classical in
def embed (S : Type) [CommRing S] (a : (Σ k, ι k) → ℤ) (n : ℕ) :
    CombC S (negSet a) n →ₗ[S] KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n :=
  LinearMap.pi fun I => if h : ∀ k, negSet a k ⊆ I.1 k then
    (LinearMap.toSpanSingleton S _ (monoFrac S I.1 a)).comp
      (LinearMap.proj (R := S) (φ := fun _ : CombCell ι (negSet a) n => S) ⟨I, h⟩)
  else 0

end KHFree

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell faceSign)


open Classical in
def constD (K : Type*) [Fintype K] [LinearOrder K] (ι : K → Type*) [∀ k, LinearOrder (ι k)] (V : Type*)
    [AddCommGroup V] (n : ℕ) (f : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → V) : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1) → V :=
  fun I => ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      faceSign I.1 k i • f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0

def CechConstVanish.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, LinearOrder (ι k)] (V : Type) [AddCommGroup V]
    (G : ∀ k, Finset (ι k)) (z : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 1 → V),
    (∀ I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0) →
    ∃ f : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → V, ∀ J : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 1, (∀ k, J.1 k ⊆ G k) → constD K ι V 0 f J = z J

theorem constVanish_hyp_segment :
    ∀ I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell Unit (fun _ => Fin 2) 2, (∀ k, I.1 k ⊆ Finset.univ) →
      constD Unit (fun _ => Fin 2) ℤ 1 (fun _ => 1) I = 0 := by
  intro I _
  exfalso
  have h : (I.1 ()).card - 1 = 2 := by simpa using I.2.2
  have hc : (I.1 ()).card ≤ 2 := by simpa using Finset.card_le_univ (I.1 ())
  omega

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]

def CellMeets (y : (Σ k, ι k) → Ω) (I : ∀ k, Finset (ι k)) : Prop :=
  ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0

open scoped Classical

open Classical in
def cellSec (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (I : ∀ k, Finset (ι k)) : Submodule S Ω :=
  if CellMeets y I then
    Submodule.span S {z | ∃ (g t : MRingOver S ι) (a : K → ℕ),
      t ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S I ∧ IsMultiHomog t a ∧ (∀ k, 0 ≤ γ k + a k) ∧
        IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ z = aeval y g / aeval y t}
  else ⊥

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


open Classical in
def cellD (y : (Σ k, ι k) → Ω) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) →ₗ[S] (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1) → Ω) :=
  LinearMap.pi fun I => if CellMeets y I.1 then ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I.1 k i •
        LinearMap.proj (R := S) (φ := fun _ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n => Ω)
          ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0
  else 0

def cellC (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => cellSec S y γ I.1

def cellZ (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellC S y γ n ⊓ LinearMap.ker (cellD S y n)

def cellB (y : (Σ k, ι k) → Ω) (γ : K → ℤ) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellC S y γ n).map (cellD S y n)

abbrev cellH (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) : Type :=
  ↥(cellZ S y γ n) ⧸ (cellB S y γ n).comap (cellZ S y γ n).subtype

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
