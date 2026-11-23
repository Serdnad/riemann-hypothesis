module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_chartRing_of_mem_zero {I : Chart x} {q : Ω} (hq : q ∈ twistMod S x 0 I) :
    q ∈ chartRing S x I := by
  refine Submodule.span_induction (p := fun q _ => q ∈ chartRing S x I) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨f, s, e, e', hs, hf, hse, he, rfl⟩
    have hee : e' = e := by omega
    subst hee
    exact ⟨f, s, e', hs, hf, hse, rfl⟩
  · exact Subalgebra.zero_mem _
  · intro a b _ _ ha hb; exact Subalgebra.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def]
    exact Subalgebra.mul_mem _ a.2 hq

theorem mul_mem_pow (H : SubSystem S x Ω) (I : Chart x) {c : ℕ} {z : Ω}
    (hz : z ∈ (H.pow c).sub I) (d : ℕ) {w : Ω} (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (H.pow (c + d)).sub I := by
  induction d generalizing w with
  | zero =>
    change w ∈ twistMod S x 0 I at hw
    have h := Submodule.smul_mem ((H.pow c).sub I)
      (⟨w, mem_chartRing_of_mem_zero hw⟩ : chartRing S x I) hz
    rw [chartRing_smul_def] at h
    rwa [Nat.add_zero, mul_comm]
  | succ d ih =>
    change w ∈ Submodule.span _ _ at hw
    refine Submodule.span_induction
      (p := fun w _ => z * w ∈ ((H.pow (c + d)).twist H).sub I) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨q, hq, y, hy, rfl⟩
      refine Submodule.subset_span ⟨q, hq, z * y, ih hy, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
    · intro a w _ hw
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hw

theorem pow_mem_pow (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (H.pow m).sub I) (n : ℕ) : h ^ n ∈ (H.pow (m * n)).sub I := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_mem_twistMod_zero I
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_pow H I ih m hh

theorem mul_mem_twist_pow (Q H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z w : Ω}
    (hz : z ∈ (Q.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (Q.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => z * w ∈ (Q.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, y, hy, ?_⟩
    simp only [smul_eq_mul]; ring
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hz

theorem proof (hA : AmpleAffineGen.Statement.{u, w}) : AmpleTwistLocal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q b j
  classical
  by_cases h0 : A.h j = 0
  · refine ⟨0, fun n _ I y _ => ⟨1, ?_⟩⟩
    rw [h0, pow_one, mul_zero]
    exact Submodule.zero_mem _
  obtain ⟨p, s, hs, hgen⟩ := hA S Ω N x H A Q b j h0
  have hhI : ∀ I : Chart x, A.h j ∈ (H.pow A.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (A.mem_secs j) I
  choose k hk using hs
  refine ⟨Finset.univ.sup fun q : Fin p × Chart x => k q.1 q.2, fun n hn I y hy => ?_⟩
  have hglob : ∀ t, s t * A.h j ^ n ∈ (Q.twist (H.pow (b + A.m * n))).secs := by
    intro t
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    have hle : k t I' ≤ n := le_trans
      (Finset.le_sup (f := fun q : Fin p × Chart x => k q.1 q.2) (Finset.mem_univ (t, I'))) hn
    have h1 := mul_mem_twist_pow Q.toSubSystem H.toSubSystem I' (hk t I')
      (pow_mem_pow H.toSubSystem I' (hhI I') (n - k t I'))
    have e1 : s t * A.h j ^ k t I' * A.h j ^ (n - k t I') = s t * A.h j ^ n := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    have e2 : b + A.m * k t I' + A.m * (n - k t I') = b + A.m * n := by
      rw [add_assoc, ← mul_add, Nat.add_sub_cancel' hle]
    rw [e1, e2] at h1
    exact h1
  have hpn : A.h j ^ n ≠ 0 := pow_ne_zero n h0
  obtain ⟨e, g, hg, hz⟩ := hgen I (y / A.h j ^ n) n (by rwa [div_mul_cancel₀ y hpn])
  refine ⟨e, ?_⟩
  have hy' : y = A.h j ^ n * ∑ t, g t * s t := by
    rw [← hz]; field_simp
  rw [hy', Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun t _ => ?_
  have e3 : A.h j ^ n * (g t * s t) * A.h j ^ e = (s t * A.h j ^ n) * (g t * A.h j ^ e) := by ring
  rw [e3]
  exact Submodule.mul_mem_mul (Submodule.subset_span (hglob t)) (hg t)

end AmpleTwistLocal

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

namespace DegLocExact

theorem decompose_map {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i) (a : A) (k : ι) :
    φ (DirectSum.decompose 𝒜 a k) = DirectSum.decompose ℬ (φ a) k := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp [h0]
  | @homogeneous i m =>
    obtain ⟨m, hm⟩ := m
    by_cases hik : i = k
    · subst hik
      rw [DirectSum.decompose_of_mem_same (ℳ := 𝒜) hm,
        DirectSum.decompose_of_mem_same (ℳ := ℬ) (hφ _ _ hm)]
    · rw [DirectSum.decompose_of_mem_ne (ℳ := 𝒜) hm hik,
        DirectSum.decompose_of_mem_ne (ℳ := ℬ) (hφ _ _ hm) hik, h0]
  | add m m' hm hm' => simp [hadd, DirectSum.decompose_add, hm, hm']

theorem mem_of_map_mem {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i)
    (hinj : Function.Injective φ) {a : A} {k : ι} (ha : φ a ∈ ℬ k) : a ∈ 𝒜 k := by
  have h := decompose_map 𝒜 ℬ φ h0 hadd hφ a k
  rw [DirectSum.decompose_of_mem_same (ℳ := ℬ) ha] at h
  rw [← hinj h]
  exact SetLike.coe_mem _

variable {S : Type u} [CommRing S] {N : ℕ} {M : Type v} [AddCommGroup M] [Module (Poly S N) M]
  [Module S M] [IsScalarTower S (Poly S N) M]

theorem exists_frac (𝓜 : GradedPMod S N M) (c : ℤ) (I : StdCell N) (z : LocMod S N M I.1)
    (hz : z ∈ degLoc 𝓜 c I) :
    ∃ (m : M) (s : monos (S := S) I.1) (e : ℕ), (s : Poly S N).IsHomogeneous e ∧
      m ∈ 𝓜.piece (c + e) ∧ z = (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, s, a, e, hm, hs, hae, rfl⟩ := hz
    exact ⟨m, s, e, hs, by rwa [← hae, sub_add_cancel], rfl⟩
  | zero => exact ⟨0, 1, 0, isHomogeneous_one _ _, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, s1, e1, hs1, hm1, rfl⟩ := hx
    obtain ⟨m2, s2, e2, hs2, hm2, rfl⟩ := hy
    refine ⟨(s2 : Poly S N) • m1 + (s1 : Poly S N) • m2, s1 * s2, e1 + e2,
      by simpa using hs1.mul hs2, add_mem ?_ ?_, LocalizedModule.mk_add_mk⟩
    · have h : c + ((e1 + e2 : ℕ) : ℤ) = c + e1 + e2 := by push_cast; ring
      rw [h]; exact 𝓜.smul_mem e2 _ _ m1 hs2 hm1
    · have h : c + ((e1 + e2 : ℕ) : ℤ) = c + e2 + e1 := by push_cast; ring
      rw [h]; exact 𝓜.smul_mem e1 _ _ m2 hs1 hm2
  | smul r x _ hx =>
    obtain ⟨m, s, e, hs, hm, rfl⟩ := hx
    refine ⟨r • m, s, e, hs, Submodule.smul_mem _ r hm, ?_⟩
    change algebraMap S (Poly S N) r • (LocalizedModule.mk m s : LocalizedModule _ M) = _
    rw [LocalizedModule.smul'_mk, algebraMap_smul]

theorem proof : DegLocExact.Statement := by
  intro S _ N M' M M'' _ _ _ _ _ _ _ _ _ _ _ _ 𝓜' 𝓜 𝓜'' f g hf hg hfg c I
  let _ := 𝓜'.isInternal.chooseDecomposition
  let _ := 𝓜.isInternal.chooseDecomposition
  let _ := 𝓜''.isInternal.chooseDecomposition
  refine ⟨fun z hz hz0 => ?_, fun z hz => ?_⟩
  · obtain ⟨m, s, e, hs, hm, rfl⟩ := exists_frac 𝓜 c I z hz
    rw [locMap_mk] at hz0
    have h0 : (LocalizedModule.mk (g.toLin m) s : LocalizedModule (monos (S := S) I.1) M'') =
        LocalizedModule.mk 0 s := by rw [LocalizedModule.zero_mk]; exact hz0
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 h0
    set T : monos (S := S) I.1 := u * s with hT
    obtain ⟨e', he'⟩ := monos_isHomogeneous T.2
    have hgT : g.toLin ((T : Poly S N) • m) = 0 := by
      rw [map_smul, hT, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← Submonoid.smul_def,
        hu, smul_zero, smul_zero]
    obtain ⟨m', hm'⟩ := (hfg _).1 hgT
    have hTm : (T : Poly S N) • m ∈ 𝓜.piece (c + e + e') := 𝓜.smul_mem e' _ _ m he' hm
    have hm'd : m' ∈ 𝓜'.piece (c + e + e') :=
      mem_of_map_mem 𝓜'.piece 𝓜.piece f.toLin (map_zero _) (map_add _) f.map_piece hf (hm' ▸ hTm)
    refine ⟨LocalizedModule.mk m' (T * s), Submodule.subset_span
      ⟨m', T * s, c + e + e', e' + e, hm'd, by simpa using he'.mul hs, by push_cast; ring, rfl⟩, ?_⟩
    rw [locMap_mk, hm', ← Submonoid.smul_def, LocalizedModule.mk_cancel_common_left]
  · obtain ⟨m'', s, e, hs, hm'', rfl⟩ := exists_frac 𝓜'' c I z hz
    obtain ⟨m, rfl⟩ := hg m''
    refine ⟨LocalizedModule.mk (DirectSum.decompose 𝓜.piece m (c + e) : M) s, Submodule.subset_span
      ⟨_, s, c + e, e, SetLike.coe_mem _, hs, by ring, rfl⟩, ?_⟩
    rw [locMap_mk, decompose_map 𝓜.piece 𝓜''.piece g.toLin (map_zero _) (map_add _) g.map_piece,
      DirectSum.decompose_of_mem_same (ℳ := 𝓜''.piece) hm'']

end DegLocExact

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace Cech.Cone

section Signs

variable {n : ℕ}

theorem sgn_insert {a b : Fin n} {A : Finset (Fin n)} (ha : a ∉ A) :
    Cech.sgn (insert a A) b = Cech.sgn A b * (if a < b then -1 else 1) := by
  unfold Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1), pow_succ]
  · rw [mul_one]

theorem sgn_mul_self (A : Finset (Fin n)) (b : Fin n) : Cech.sgn A b * Cech.sgn A b = 1 := by
  unfold Cech.sgn
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sgn_key {K : Finset (Fin n)} {i₀ j : Fin n} (hi₀ : i₀ ∉ K) (hj : j ∈ K) :
    Cech.sgn K j * Cech.sgn (insert i₀ (K.erase j)) i₀ =
      -(Cech.sgn (insert i₀ K) i₀ * Cech.sgn (insert i₀ K) j) := by
  have hne : j ≠ i₀ := fun e => hi₀ (e ▸ hj)
  have h1 : Cech.sgn (insert i₀ (K.erase j)) i₀ = Cech.sgn (K.erase j) i₀ := by
    rw [sgn_insert (fun hm => hi₀ (Finset.mem_of_mem_erase hm)), if_neg (lt_irrefl _), mul_one]
  have h2 : Cech.sgn (insert i₀ K) i₀ = Cech.sgn K i₀ := by
    rw [sgn_insert hi₀, if_neg (lt_irrefl _), mul_one]
  have h3 := sgn_insert (b := j) hi₀
  have h4 := sgn_insert (b := i₀) (Finset.notMem_erase j K)
  rw [Finset.insert_erase hj] at h4
  rw [h1, h2, h3, h4]
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [if_pos h, if_neg (lt_asymm h)]; ring
  · simp only [if_neg (lt_asymm h), if_pos h]; ring

end Signs

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {N : ℕ}

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i) (A : Finset (Fin (N + 1))) : V :=
  if h : A.card = i + 1 then
    s ⟨⟨A, Finset.card_pos.mp (by omega), Finset.subset_univ A⟩, h⟩
  else 0

theorem onSet_idx {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) : onSet s I.1.1 = s I := by
  unfold onSet
  rw [dite_eq_left I.2]

theorem d_eq {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) :
    Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl

def coneY {i : ℕ} (i₀ : Fin (N + 1)) (z : Cech.Cochain (fun _ : StdCell N => V) (i + 1))
    (A : Finset (Fin (N + 1))) : V :=
  if i₀ ∈ A then 0 else Cech.sgn (insert i₀ A) i₀ • onSet z (insert i₀ A)

theorem onSet_pair {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    {a b : Fin (N + 1)} (hab : a < b) : onSet z {a} = onSet z {b} := by
  have hcard : ({a, b} : Finset (Fin (N + 1))).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hz ⟨⟨{a, b}, Finset.insert_nonempty _ _, Finset.subset_univ _⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin (N + 1))), Cech.sgn {a, b} j • onSet z (({a, b} : Finset _).erase j)
    = 0 at h
  have ha : a ∉ ({b} : Finset (Fin (N + 1))) := Finset.notMem_singleton.mpr hab.ne
  rw [Finset.sum_pair hab.ne, Finset.erase_insert ha, Finset.erase_insert_of_ne hab.ne,
    Finset.erase_singleton, sgn_insert ha, sgn_insert ha, if_neg (lt_irrefl _), if_pos hab] at h
  have e1 : Cech.sgn ({b} : Finset (Fin (N + 1))) a = 1 := by
    simp [Cech.sgn, Finset.filter_singleton, lt_asymm hab]
  have e2 : Cech.sgn ({b} : Finset (Fin (N + 1))) b = 1 := by
    simp [Cech.sgn, Finset.filter_singleton]
  rw [e1, e2, insert_empty_eq] at h
  rw [one_mul, one_smul, one_mul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    (I K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) : z I = z K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  rw [← onSet_idx z I, ← onSet_idx z K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hz h
  · rfl
  · exact (onSet_pair hz h).symm

end Cech.Cone


open Cech.Cone in
theorem Cech.Cone.proof : Cech.Cone.Statement.{u, v} := by
  intro R _ V _ _ N J
  refine ⟨?_, ?_, fun z hz I K => const hz I K⟩
  · intro W i₀ hi₀ i z hz hW hJ
    have hWs : ∀ A, onSet z A ∈ W := by
      intro A; unfold onSet; split_ifs
      · exact hW _
      · exact W.zero_mem
    have hJs : ∀ A, ¬ J ⊆ A → onSet z A = 0 := by
      intro A hA; unfold onSet; split_ifs
      · exact hJ _ hA
      · rfl
    have hcoc : ∀ L : Finset (Fin (N + 1)), L.card = i + 1 + 1 + 1 →
        ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
      intro L hL
      have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), Finset.subset_univ L⟩, hL⟩
      rw [d_eq] at h
      exact h
    refine ⟨fun I => coneY i₀ z I.1.1, fun I => ?_, fun I hI => ?_, ?_⟩
    · change coneY i₀ z I.1.1 ∈ W
      unfold coneY; split_ifs
      · exact W.zero_mem
      · exact zsmul_mem (hWs _) _
    · change coneY i₀ z I.1.1 = 0
      unfold coneY; split_ifs
      · rfl
      · rw [hJs _ fun hs => hI fun x hx =>
          (Finset.mem_insert.mp (hs hx)).resolve_left fun (e : x = i₀) => hi₀ (e ▸ hx), smul_zero]
    · funext K
      rw [d_eq, ← onSet_idx z K]
      have hK : K.1.1.card = i + 1 + 1 := K.2
      have hY : ∀ j ∈ K.1.1, onSet (fun I => coneY i₀ z I.1.1 :
          Cech.Cochain (fun _ : StdCell N => V) i) (K.1.1.erase j) = coneY i₀ z (K.1.1.erase j) := by
        intro j hj
        unfold onSet
        rw [dite_eq_left (by rw [Finset.card_erase_of_mem hj, hK]; rfl)]
      rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
      generalize K.1.1 = Kf at hK ⊢
      by_cases h : i₀ ∈ Kf
      · rw [Finset.sum_eq_single i₀]
        · rw [coneY, if_neg (Finset.notMem_erase i₀ Kf), Finset.insert_erase h, smul_smul,
            sgn_mul_self, one_smul]
        · intro j hj hne
          rw [coneY, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
        · exact fun h' => absurd h h'
      · have hc := hcoc (insert i₀ Kf) (by rw [Finset.card_insert_of_notMem h, hK])
        rw [Finset.sum_insert h, Finset.erase_insert h] at hc
        have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
        have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY i₀ z (Kf.erase j) =
            -(Cech.sgn (insert i₀ Kf) i₀ •
              ∑ j ∈ Kf, Cech.sgn (insert i₀ Kf) j • onSet z ((insert i₀ Kf).erase j)) := by
          rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : i₀ ≠ j := fun e => h (e ▸ hj)
          have hni : i₀ ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
          rw [Finset.erase_insert_of_ne hne, coneY, if_neg hni, smul_smul, smul_smul,
            sgn_key h hj, neg_smul]
        rw [hs, hb, smul_neg, neg_neg, smul_smul, sgn_mul_self, one_smul]
  · intro hJne i₀ hi₀ z hz hJ
    obtain ⟨j, hj⟩ := hJne
    funext I
    let I₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{i₀}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    rw [const hz I I₀]
    exact hJ I₀ fun hs => hi₀ (Finset.mem_singleton.mp (hs hj) ▸ hj)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Retract

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem locMap_retract (f : M →ₗ[Poly S N] M') (g : M' →ₗ[Poly S N] M)
    (hgf : Function.LeftInverse g f) (I : Finset (Fin (N + 1))) :
    Function.LeftInverse (locMap g I) (locMap f I) := by
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s => rw [locMap_mk, locMap_mk, hgf m]

theorem cohomMap_retract {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'}
    (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜) (hgf : Function.LeftInverse g.toLin f.toLin)
    (i : ℕ) (c : ℤ) : Function.LeftInverse (cohomMap g i c) (cohomMap f i c) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (funext fun I => locMap_retract f.toLin g.toLin hgf I.1.1 (z.1 I)))

theorem CohomRetract.proof : CohomRetract.Statement.{u, v, w} := by
  intro S _ N M M' _ _ _ _ _ _ _ _ 𝓜 𝓜' f g hgf i c
  exact (cohomMap_retract f g hgf i c).injective

end Retract

end

end GroundTheory.Heights₂.Heights.Kleiman
end
