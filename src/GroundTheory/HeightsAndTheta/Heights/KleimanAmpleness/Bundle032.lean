module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace VeryAmpleZChartSpan

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem chart_smul {I : Chart x} (a : chartRing S x I) (e : E) : a • e = (a : Ω) • e := rfl

theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    exact Submodule.subset_span
      ⟨h l, (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp (hh l) I), _, ih, rfl⟩


omit [Module S E] [IsScalarTower S Ω E] in
theorem exists_coeff_of_mem_twist (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x) (g : Finset E)
    (hg : F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E)) {z : E} (hz : z ∈ (F.twist Q).sub I) :
    ∃ γ : E → Ω, (∀ y ∈ g, γ y ∈ Q.sub I) ∧ z = ∑ y ∈ g, γ y • y := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, y', hy', rfl⟩ := hz
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.mp (hg hy')
    refine ⟨fun y => (a y : Ω) * q, fun y _ => ?_, ?_⟩
    · have := Submodule.smul_mem (Q.sub I) (a y) hq
      rwa [chartRing_smul_def] at this
    · rw [← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [chart_smul, smul_smul, mul_comm]
  | zero => exact ⟨0, fun _ _ => Submodule.zero_mem _, by simp⟩
  | add z z' _ _ ih ih' =>
    obtain ⟨γ, hγ, rfl⟩ := ih
    obtain ⟨γ', hγ', rfl⟩ := ih'
    refine ⟨γ + γ', fun y hy => Submodule.add_mem _ (hγ y hy) (hγ' y hy), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]
  | smul a z _ ih =>
    obtain ⟨γ, hγ, rfl⟩ := ih
    refine ⟨fun y => (a : Ω) * γ y, fun y hy => ?_, ?_⟩
    · have := Submodule.smul_mem (Q.sub I) a (hγ y hy)
      rwa [chartRing_smul_def] at this
    · rw [chart_smul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [smul_smul]

theorem proof : VeryAmpleZChartSpan.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh I J g hg e he
  have hJ : xProd J ∈ (H.pow J.1.card).sub I := prod_mem_pow H I hh J.1
  have h0 : xProd J ≠ 0 := AmpleAffineGen.xProd_ne_zero J
  have memB : ∀ {a : Ω}, a ∈ ampleChart H J.1.card (xProd J) I →
      a ∈ AmpleAffineGen.ampleSubalg H J.1.card (xProd J) I hJ := fun ha => ha
  change e ∈ Submodule.span S _ at he
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨n, hn⟩ := he
    obtain ⟨γ, hγ, hz⟩ := exists_coeff_of_mem_twist F _ I g hg hn
    have hp : xProd J ^ n ≠ 0 := pow_ne_zero n h0
    refine ⟨fun y => γ y / xProd J ^ n, fun y hy => ⟨n, ?_⟩, ?_⟩
    · rw [div_mul_cancel₀ _ hp]; exact hγ y hy
    · have he' : e = (xProd J ^ n)⁻¹ • (xProd J ^ n • e) := by
        rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
      rw [he', hz, Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => by
        show _ = (γ y / xProd J ^ n) • y
        rw [smul_smul, div_eq_inv_mul]
  | zero =>
    refine ⟨0, fun _ _ => ⟨0, ?_⟩, by simp⟩
    rw [Pi.zero_apply, zero_mul]; exact Submodule.zero_mem _
  | add e e' _ _ ih ih' =>
    obtain ⟨β, hβ, rfl⟩ := ih
    obtain ⟨β', hβ', rfl⟩ := ih'
    refine ⟨β + β', fun y hy => Subalgebra.add_mem _ (memB (hβ y hy)) (memB (hβ' y hy)), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]
  | smul s e _ ih =>
    obtain ⟨β, hβ, rfl⟩ := ih
    refine ⟨fun y => algebraMap S Ω s * β y,
      fun y hy => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ s) (memB (hβ y hy)), ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [← smul_assoc, Algebra.smul_def]

end VeryAmpleZChartSpan

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

theorem KHFreeBadFinite.full : KHFreeBadFinite.Statement := by
  intro K _ ι _ e
  refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Icc (-|e p.1|) |e p.1|)
    (fun p => Set.finite_Icc _ _)).subset ?_
  rintro a ⟨hsum, hneg⟩ ⟨k, i⟩ -
  show a ⟨k, i⟩ ∈ Set.Icc (-|e k|) |e k|
  rw [Set.mem_Icc, ← abs_le]
  have hs : ∑ j, a ⟨k, j⟩ = e k := congrFun hsum k
  rcases hneg k with h | h
  · have hnn : ∀ j, 0 ≤ a ⟨k, j⟩ := by
      intro j
      by_contra hj
      have hj2 : a ⟨k, j⟩ < 0 := lt_of_not_ge hj
      have hj' : j ∈ negSet a k := by simp [negSet, hj2]
      rw [h] at hj'
      simp at hj'
    have h1 : a ⟨k, i⟩ ≤ ∑ j, a ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => a ⟨k, j⟩) (fun j _ => hnn j) (Finset.mem_univ i)
    rw [abs_of_nonneg (hnn i)]
    linarith [le_abs_self (e k)]
  · have hng : ∀ j, a ⟨k, j⟩ < 0 := by
      intro j
      have hj : j ∈ negSet a k := by rw [h]; exact Finset.mem_univ j
      simpa [negSet] using hj
    have h1 : -a ⟨k, i⟩ ≤ ∑ j, -a ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => -a ⟨k, j⟩) (fun j _ => by linarith [hng j])
        (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib] at h1
    rw [abs_of_neg (hng i)]
    linarith [neg_abs_le (e k)]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeIndep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ e, t = monomial e 1 := by
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, -, rfl⟩ := hx
    exact ⟨Finsupp.single ⟨k, i⟩ 1, rfl⟩
  | one => exact ⟨0, by rw [monomial_zero', C_1]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hy
    exact ⟨e + e', by rw [monomial_mul, mul_one]⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eq_zero_of_monomial_mul (e : (Σ k, ι k) →₀ ℕ) {p : MRingOver S ι}
    (h : monomial e (1 : S) * p = 0) : p = 0 := by
  ext d
  have := congrArg (AddMonoidAlgebra.coeff · (e + d)) h
  rw [coeff_monomial_mul, one_mul] at this
  simpa using this


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eq_zero_of_mk_eq_zero {I : ∀ k, Finset (ι k)} {p : MRingOver S ι}
    (h : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) p) (1 : KH.cellMon S I) = 0) :
    p = 0 := by
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I), LocalizedModule.mk_eq] at h
  obtain ⟨t, ht⟩ := h
  rw [one_smul, one_smul, smul_zero, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at ht
  obtain ⟨e, he⟩ := cellMon_monomial t.2
  rw [he] at ht
  exact eq_zero_of_monomial_mul e ht

theorem shift_injective (u : (Σ k, ι k) →₀ ℕ) {b b' : (Σ k, ι k) → ℤ} (hb : negExp b ≤ u)
    (hb' : negExp b' ≤ u) (h : posExp b + u - negExp b = posExp b' + u - negExp b') : b = b' := by
  funext p
  have h1 := DFunLike.congr_fun h p
  have h2 := Finsupp.le_def.1 hb p
  have h3 := Finsupp.le_def.1 hb' p
  simp only [posExp, negExp, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
    Finsupp.coe_equivFunOnFinite_symm] at h1 h2 h3
  omega

theorem smul_smul_monoFrac (I : ∀ k, Finset (ι k)) (u : (Σ k, ι k) →₀ ℕ) (r : S) (b : (Σ k, ι k) → ℤ)
    (hI : ∀ k, negSet b k ⊆ I k) (hb : negExp b ≤ u) :
    (monomial u (1 : S) : MRingOver S ι) • (r • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (monomial (posExp b + u - negExp b) r)) (1 : KH.cellMon S I) := by
  rw [monoFrac, dif_pos hI, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  rw [one_smul, one_smul, one_smul, Submonoid.smul_def]
  rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  congr 1
  simp only [smul_eq_mul, smul_monomial, monomial_mul, mul_one, one_mul]
  congr 1
  rw [add_tsub_cancel_of_le (le_add_left hb), add_comm]

theorem eq_zero_of_sum_smul_monoFrac (I : ∀ k, Finset (ι k)) (A : Finset ((Σ k, ι k) → ℤ))
    (g : ((Σ k, ι k) → ℤ) → S) (hg : ∀ b ∈ A, ¬ (∀ k, negSet b k ⊆ I k) → g b = 0)
    (h : ∑ b ∈ A, g b • monoFrac S I b = 0) : ∀ a ∈ A, g a = 0 := by
  classical
  set u : (Σ k, ι k) →₀ ℕ := ∑ b ∈ A.filter (fun b => ∀ k, negSet b k ⊆ I k), negExp b with hu
  set c : ((Σ k, ι k) → ℤ) → ((Σ k, ι k) →₀ ℕ) := fun b => posExp b + u - negExp b with hc
  have hle : ∀ b ∈ A, (∀ k, negSet b k ⊆ I k) → negExp b ≤ u := fun b hb hI =>
    Finset.single_le_sum (f := negExp) (fun _ _ => zero_le) (Finset.mem_filter.2 ⟨hb, hI⟩)
  have hterm : ∀ b ∈ A, (monomial u (1 : S) : MRingOver S ι) • (g b • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (c b) (g b)))
        (1 : KH.cellMon S I) := by
    intro b hb
    by_cases hI : ∀ k, negSet b k ⊆ I k
    · exact smul_smul_monoFrac I u (g b) b hI (hle b hb hI)
    · rw [hg b hb hI, zero_smul, smul_zero, monomial_zero, map_zero, LocalizedModule.zero_mk]
  have key : ∑ b ∈ A, monomial (c b) (g b) = 0 := by
    apply eq_zero_of_mk_eq_zero (I := I)
    have e1 : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (∑ b ∈ A, monomial (c b) (g b))) (1 : KH.cellMon S I) =
        ∑ b ∈ A, LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
          (monomial (c b) (g b))) (1 : KH.cellMon S I) := by

      rw [map_sum]
      exact map_sum (LocalizedModule.mkLinearMap (KH.cellMon S I) _) _ _
    rw [e1, ← Finset.sum_congr rfl hterm, ← Finset.smul_sum, h, smul_zero]
  intro a ha
  by_cases hI : ∀ k, negSet a k ⊆ I k
  · have hk := congrArg (AddMonoidAlgebra.coeff · (c a)) key
    rw [coeff_sum, Finset.sum_eq_single a, coeff_monomial, if_pos rfl,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hk
    · exact hk
    · intro b hb hba
      by_cases hbI : ∀ k, negSet b k ⊆ I k
      · rw [coeff_monomial, if_neg]
        exact fun hcb => hba (shift_injective u (hle b hb hbI) (hle a ha hI) hcb)
      · simp [hg b hb hbI]
    · exact fun hna => absurd ha hna
  · exact hg a ha hI

end KHFreeIndep

theorem KHFreeIndep.full : KHFreeIndep.Statement := by
  intro S _ K _ _ ι _ _ n A f h a ha
  classical
  funext J
  let g : ((Σ k, ι k) → ℤ) → S := fun b =>
    if hb : ∀ k, negSet b k ⊆ J.1.1 k then f b ⟨J.1, hb⟩ else 0
  have hsum : ∑ b ∈ A, g b • monoFrac S J.1.1 b = 0 := by
    have h0 := congrFun h J.1
    rw [Finset.sum_apply, Pi.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [embed, LinearMap.pi_apply, g]
    split_ifs with hb1
    · rfl
    · simp [monoFrac, hb1]
  have hJ := KHFreeIndep.eq_zero_of_sum_smul_monoFrac J.1.1 A g (fun b _ hb => dif_neg hb) hsum a ha
  rw [show g a = f a J from dif_pos J.2] at hJ
  simpa using hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CechContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (Ω : Type) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G : Kleiman.Chart x → Submodule S Ω) (J₀ : Kleiman.Chart x),
    J₀.1.card = 1 →
    (∀ J J' : Kleiman.Chart x, J.1 ⊆ J'.1 → G J ≤ G J') →
    (∀ J J' : Kleiman.Chart x, J'.1 = J₀.1 ∪ J.1 → G J' = G J) →
    CechAugExact S G (G J₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace VeryAmpleZRows

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {n : ℕ} {U : Finset (Fin n)}

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (A : Finset (Fin n)) : V :=
  if h : A.card = i + 1 ∧ A ⊆ U then s ⟨⟨A, Finset.card_pos.mp (by omega), h.2⟩, h.1⟩ else 0

theorem onSet_idx {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (I : Cech.Idx U i) :
    onSet s I.1.1 = s I := by
  unfold onSet
  rw [dite_eq_left ⟨I.2, I.1.2.2⟩]

theorem d_eq {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl

theorem onSet_pair {s : Cech.Cochain (fun _ : Cell U => V) 0}
    (hs : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 s = 0) {a b : Fin n} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a < b) : onSet s {a} = onSet s {b} := by
  have hcard : ({a, b} : Finset (Fin n)).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hs ⟨⟨{a, b}, Finset.insert_nonempty _ _,
    Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin n)), Cech.sgn {a, b} j • onSet s (({a, b} : Finset _).erase j) = 0 at h
  rw [Finset.sum_pair hab.ne, Finset.erase_insert (Finset.notMem_singleton.mpr hab.ne),
    Finset.erase_insert_of_ne hab.ne, Finset.erase_singleton, insert_empty_eq] at h
  have e1 : Cech.sgn ({a, b} : Finset (Fin n)) a = 1 := by
    simp [Cech.sgn, Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hab.le]
  have e2 : Cech.sgn ({a, b} : Finset (Fin n)) b = -1 := by
    simp [Cech.sgn, Finset.filter_insert, Finset.filter_singleton, hab]
  rw [e1, e2, one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const_zero {s : Cech.Cochain (fun _ : Cell U => V) 0}
    (hs : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 s = 0) (I K : Cech.Idx U 0) : s I = s K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  have haU : a ∈ U := I.1.2.2 (ha ▸ Finset.mem_singleton_self a)
  have hbU : b ∈ U := K.1.2.2 (hb ▸ Finset.mem_singleton_self b)
  rw [← onSet_idx s I, ← onSet_idx s K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hs haU hbU h
  · rfl
  · exact (onSet_pair hs hbU haU h).symm

end VeryAmpleZRows


open VeryAmpleZRows in
theorem VeryAmpleZRows.proof (hPart : CechPartition.Statement.{u, v, w}) (hSmul : ZChartSmul.Statement.{u, v, w})
    (hLoc : ZChartLocal.Statement.{u, v, w}) : VeryAmpleZRows.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hH J
  have hmono : ∀ I I' : Chart x, I.1 ⊆ I'.1 →
      secsOnZChart G.toSubSystem H.toSubSystem h I J ≤ secsOnZChart G.toSubSystem H.toSubSystem h I' J := by
    intro I I' hII'
    refine Submodule.span_mono ?_
    rintro e ⟨m, hm⟩
    exact ⟨m, (G.toSubSystem.twist (H.toSubSystem.pow (J.1.card * m))).mono I I' hII' _ hm⟩

  obtain ⟨j, hjJ⟩ := J.2.1
  obtain ⟨n, a, b, K, ha, hb, hab, hK⟩ := hH.affine j ((mem_support h).mp (J.2.2 hjJ))
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hab
    · exact hn

  let pt : ∀ i, i ∈ support x → Cech.Idx (support x) 0 := fun i hi =>
    ⟨⟨{i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr hi⟩, Finset.card_singleton _⟩
  obtain ⟨i₀, hi₀⟩ := (K ⟨0, hn⟩).2.1
  have hi₀x : i₀ ∈ support x := (K ⟨0, hn⟩).2.2 hi₀
  refine ⟨hmono, fun I => iInf_le _ I, fun z _ hz => hz (pt i₀ hi₀x), ?_, ?_⟩
  ·
    intro s hs hds
    refine ⟨s (pt i₀ hi₀x), Submodule.mem_iInf _ |>.mpr fun I => ?_, fun I => const_zero hds I _⟩
    obtain ⟨i, hi⟩ := I.2.1
    rw [const_zero hds (pt i₀ hi₀x) (pt i (I.2.2 hi))]
    exact hmono (pt i (I.2.2 hi)).1 I (Finset.singleton_subset_iff.mpr hi)
      ((Submodule.mem_pi.mp hs) _ (Set.mem_univ _))
  ·
    intro p s hs hds
    have hjk : ∀ k, (K k).2.1.choose ∈ (K k).1 := fun k => (K k).2.1.choose_spec
    exact hPart S Ω E (support x) (fun I => secsOnZChart G.toSubSystem H.toSubSystem h I J) n a b
      (fun k => (K k).2.1.choose) (fun k => (K k).2.2 (hjk k)) hab
      (fun k I z hz => hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hH.mem_secs J j hjJ I (a k) (ha k) z hz)
      (fun k I z hz => hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hH.mem_secs J j hjJ I (b k) (hb k) z hz)
      (fun k I I' hI z hz => hLoc S Ω N x E G H r h hH.mem_secs J j hjJ (b k) (hb k) (K k) (hK k) _ (hjk k)
        I I' hI z hz)
      p s hs hds

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon IsMGraded quotPart)

def SectionMapInj.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 →
    ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → ∀ x ∈ 𝓜 c,
      (∀ I : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, LocalizedModule.mk x (1 : cellMon S I.1) = 0) → x = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
