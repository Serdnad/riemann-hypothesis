module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle004
public import Mathlib.Algebra.Lie.OfAssociative
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace CechZerothCohomologySections

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

def pt {i : Fin (N + 1)} (hi : i ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{i}, Finset.singleton_nonempty i, Finset.singleton_subset_iff.mpr hi⟩, Finset.card_singleton i⟩

theorem idx_ext {U : Finset (Fin (N + 1))} {i : ℕ} {K K' : Cech.Idx U i} (h : K.1.1 = K'.1.1) :
    K = K' :=
  Subtype.ext (Subtype.ext h)

theorem mem_sub_of_mem_secs (F : SubSystem S x E) {z : E} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I :=
  (Submodule.mem_iInf _).mp hz I

theorem cocycle_coe_eq (F : SubSystem S x E) {s : Cech.Cochain (fun I => F.sub I) 0}
    (hs : Cech.d (fun I => F.sub I) F.res 0 s = 0) (K K' : Cech.Idx (support x) 0) :
    (s K : E) = (s K' : E) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · subst hab; rw [idx_ext (ha.trans hb.symm)]
  have hsub : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact K.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self _)
    · rw [Finset.mem_singleton.mp hz]
      exact K'.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self _)
  let J : Cech.Idx (support x) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsub⟩, Finset.card_pair hab⟩
  have ha' : a ∈ J.1.1 := Finset.mem_insert_self _ _
  have hb' : b ∈ J.1.1 := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have fa : Cech.face J ⟨a, ha'⟩ = K' := idx_ext (by
    change ({a, b} : Finset _).erase a = _
    rw [hb]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨Ne.symm hab, Or.inr rfl⟩)
  have fb : Cech.face J ⟨b, hb'⟩ = K := idx_ext (by
    change ({a, b} : Finset _).erase b = _
    rw [ha]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩)
  have hval : ∀ L L' : Cech.Idx (support x) 0, L = L' → (s L : E) = (s L' : E) := by
    rintro L L' rfl; rfl
  have h0 := congrArg (F.sub J.1).subtype (congrFun hs J)

  rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have huniv : (Finset.univ : Finset J.1.1) = {⟨a, ha'⟩, ⟨b, hb'⟩} := by
    ext ⟨z, hz⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    exact (Finset.mem_insert.mp hz).imp id Finset.mem_singleton.mp
  have hne : (⟨a, ha'⟩ : J.1.1) ≠ ⟨b, hb'⟩ := fun h => hab (congrArg Subtype.val h)
  rw [huniv, Finset.sum_pair hne, map_zsmul, map_zsmul] at h0
  have h1 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a • (s K' : E) +
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) b • (s K : E) = 0 := by
    rw [← hval _ _ fa, ← hval _ _ fb]; exact h0
  have hsum := Cech.sum_sgn_of_card_two (Finset.card_pair hab)
  rw [Finset.sum_pair hab] at hsum
  have hb2 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) b =
      - Cech.sgn ({a, b} : Finset (Fin (N + 1))) a := by linarith
  rw [hb2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h1
  have hsq : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a *
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) a = 1 := by
    unfold Cech.sgn; rw [← mul_pow]; norm_num
  have h2 : (s K' : E) - (s K : E) = 0 := by
    rw [← one_smul ℤ ((s K' : E) - (s K : E)), ← hsq, mul_smul, h1, smul_zero]
  exact (sub_eq_zero.mp h2).symm

def constC (F : SubSystem S x E) : F.secs →ₗ[S] Cech.Cochain (fun I => F.sub I) 0 where
  toFun z K := ⟨z, mem_sub_of_mem_secs F z.2 K.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem constC_cocycle (F : SubSystem S x E) (z : F.secs) :
    Cech.d (fun I => F.sub I) F.res 0 (constC F z) = 0 :=
  Cech.d_zero_of_compat (v := fun I => (⟨z, mem_sub_of_mem_secs F z.2 I⟩ : F.sub I))
    (fun _ _ _ => rfl)

def toKer (F : SubSystem S x E) :
    F.secs →ₗ[S] LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0) :=
  (constC F).codRestrict _ fun z => LinearMap.mem_ker.mpr (constC_cocycle F z)

theorem exists_mem_support (hx : x ≠ 0) : ∃ i, i ∈ support x := by
  by_contra h
  simp only [not_exists] at h
  exact hx (funext fun i => by_contra fun hi => h i ((mem_support x).mpr hi))

theorem toKer_bijective (F : SubSystem S x E) (hx : x ≠ 0) : Function.Bijective (toKer F) := by
  obtain ⟨i₀, hi₀⟩ := exists_mem_support hx
  refine ⟨fun z₁ z₂ h => ?_, fun s => ?_⟩
  · have := congrArg (fun t => ((t.1 (pt hi₀) : F.sub (pt hi₀).1) : E)) h
    exact Subtype.ext this
  · have hs := LinearMap.mem_ker.mp s.2
    have hz : (s.1 (pt hi₀) : E) ∈ F.secs := by
      refine Submodule.mem_iInf _ |>.mpr fun I => ?_
      obtain ⟨i, hi⟩ := I.2.1
      have hsup : i ∈ support x := I.2.2 hi
      rw [Submodule.restrictScalars_mem, cocycle_coe_eq F hs (pt hi₀) (pt hsup)]
      exact F.mono _ I (Finset.singleton_subset_iff.mpr hi) _ (s.1 (pt hsup)).2
    refine ⟨⟨_, hz⟩, Subtype.ext (funext fun K => Subtype.ext ?_)⟩
    exact cocycle_coe_eq F hs (pt hi₀) K

theorem proof : CechZerothCohomologySections.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F hx
  have hp : (Cech.bdry (fun I => F.sub I) F.res 0).comap
      (LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0)).subtype = ⊥ := by
    rw [show Cech.bdry (fun I => F.sub I) F.res 0 = ⊥ from rfl, Submodule.comap_bot,
      Submodule.ker_subtype]
  set_option synthInstance.maxHeartbeats 200000 in
    exact ⟨(Submodule.quotEquivOfEqBot _ hp).trans
    (LinearEquiv.ofBijective (toKer F) (toKer_bijective F hx)).symm⟩

end CechZerothCohomologySections

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace CechDSq

variable {n : ℕ}

theorem sgn_mul_sgn_of_lt {K : Finset (Fin n)} {j k : Fin n} (hj : j ∈ K) (hjk : j < k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  have h1 : (K.erase k).filter (· < j) = K.filter (· < j) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hz⟩, hzj⟩; exact ⟨hz, hzj⟩
    · rintro ⟨hz, hzj⟩; exact ⟨⟨(hzj.trans hjk).ne, hz⟩, hzj⟩
  have h3 : j ∈ K.filter (· < k) := Finset.mem_filter.2 ⟨hj, hjk⟩
  have h2 : ((K.erase j).filter (· < k)).card + 1 = (K.filter (· < k)).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one h3]
  unfold Cech.sgn
  rw [h1, ← h2, pow_succ]
  ring

theorem sgn_mul_sgn_swap {K : Finset (Fin n)} {j k : Fin n} (hk : k ∈ K) (hj : j ∈ K) (hne : j ≠ k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact sgn_mul_sgn_of_lt hj h
  · rw [sgn_mul_sgn_of_lt hk h, neg_neg]

variable {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}


open Classical in
def restrictTo {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (A : Finset (Fin n)) : G K :=
  if h : ∃ L : Cech.Idx U i, L.1.1 = A ∧ A ⊆ K.1 then
    ρ h.choose.1 K (by rw [h.choose_spec.1]; exact h.choose_spec.2) (s h.choose)
  else 0

theorem restrictTo_eq {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (L : Cech.Idx U i)
    (h : L.1.1 ⊆ K.1) : restrictTo (ρ := ρ) s K L.1.1 = ρ L.1 K h (s L) := by
  have hex : ∃ L' : Cech.Idx U i, L'.1.1 = L.1.1 ∧ L.1.1 ⊆ K.1 := ⟨L, rfl, h⟩
  have key : ∀ (L₁ L₂ : Cech.Idx U i) (_ : L₁ = L₂) (h₁ : L₁.1.1 ⊆ K.1) (h₂ : L₂.1.1 ⊆ K.1),
      ρ L₁.1 K h₁ (s L₁) = ρ L₂.1 K h₂ (s L₂) := by
    rintro _ _ rfl _ _; rfl
  rw [restrictTo, dite_eq_left hex]
  exact key _ _ (Subtype.ext (Subtype.ext hex.choose_spec.1)) _ _

end CechDSq


open CechDSq in
theorem CechDSq.proof : CechDSq.Statement := by
  intro n U R _ G _ _ ρ hρ i s
  classical
  funext K
  have hcomp : ∀ (I J L : Cell U) (h₁ : I.1 ⊆ J.1) (h₂ : J.1 ⊆ L.1) (x : G I),
      ρ J L h₂ (ρ I J h₁ x) = ρ I L (h₁.trans h₂) x := fun I J L h₁ h₂ x =>
    LinearMap.congr_fun (hρ I J L h₁ h₂) x

  let f : (Σ _ : Fin n, Fin n) → G K.1 := fun p =>
    (Cech.sgn K.1.1 p.1 * Cech.sgn (K.1.1.erase p.1) p.2) •
      restrictTo (ρ := ρ) s K.1 ((K.1.1.erase p.1).erase p.2)
  have step : ∀ k : K.1.1, Cech.sgn K.1.1 k • ρ (Cech.face K k).1 K.1 (Cech.face_subset K k)
      (Cech.d G ρ i s (Cech.face K k)) = ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩ := by
    intro k

    rw [Cech.d_apply, map_sum, Finset.smul_sum]
    refine Eq.trans ?_ (Finset.sum_coe_sort (K.1.1.erase k) (fun j => f ⟨k, j⟩))
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, hcomp, ← restrictTo_eq]
    rfl
  show Cech.d G ρ (i + 1) (Cech.d G ρ i s) K = 0
  rw [Cech.d_apply, Finset.sum_congr rfl fun k _ => step k,
    Finset.sum_coe_sort K.1.1 (fun k => ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩),
    Finset.sum_sigma' K.1.1 (fun k => K.1.1.erase k) (fun k j => f ⟨k, j⟩)]
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    simp only [f]
    rw [Finset.erase_right_comm, sgn_mul_sgn_swap hk hj hne, neg_smul, neg_add_cancel]
  · rintro ⟨k, j⟩ hp - h
    obtain ⟨hne, -⟩ := Finset.mem_erase.1 (Finset.mem_sigma.1 hp).2
    exact hne (congrArg Sigma.fst h)
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    exact Finset.mem_sigma.2 ⟨hj, Finset.mem_erase.2 ⟨hne.symm, hk⟩⟩
  · rintro ⟨k, j⟩ -
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechPartition.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    {n : ℕ} (U : Finset (Fin n)) (M : Cell U → Submodule S E) (m : ℕ) (a b : Fin m → Ω) (j : Fin m → Fin n),
    (∀ k, j k ∈ U) → ∑ k, a k * b k = 1 →
    (∀ k I, ∀ z ∈ M I, a k • z ∈ M I) → (∀ k I, ∀ z ∈ M I, b k • z ∈ M I) →
    (∀ k (I I' : Cell U), I'.1 = insert (j k) I.1 → ∀ z ∈ M I', ∃ e : ℕ, b k ^ e • z ∈ M I) →
    ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Cell U => E) M (p + 1),
      Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) (p + 1) s = 0 →
        ∃ t ∈ Cech.Cdeg (fun _ : Cell U => E) M p, Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) p t = s

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem AmpleCover.sub_twist (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨y, hy, q, hq, mul_comm _ _⟩
  · rintro ⟨y, hy, q, hq, rfl⟩; exact ⟨q, hq, y, hy, mul_comm _ _⟩

theorem AmpleCover.sub_pow (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    rw [pow_zero]
    change twistMod S x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [AmpleCover.sub_twist, ih, pow_succ]

theorem AmpleCover.proof : AmpleCover.Statement.{u, w} := by
  intro S _ Ω _ _ N x H A F hF I
  set R := chartRing S x I
  set G : Submodule R Ω := Submodule.span R (F.secs : Set Ω)
  set P : Submodule R Ω := H.sub I
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) fun y hy => ?_
  · exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨Q', hQ'⟩ := H.invertible I
  have hpow : ∀ n, (H.pow n).sub I = P ^ n := fun n => AmpleCover.sub_pow H.toSubSystem n I
  have hone : ∀ n, P ^ n * Q' ^ n = 1 := fun n => by rw [← mul_pow, hQ', one_pow]

  set c : Ideal R := G.comap (LinearMap.toSpanSingleton R Ω y)
  set V : Submodule R Ω := Submodule.map (Algebra.linearMap R Ω) c.radical
  have hkey : P ^ A.m * Q' ^ A.m ≤ V := by
    rw [← hpow, ← A.generates I, Submodule.mul_le]
    intro u hu w hw
    have hmem : ∀ j, A.h j * w ∈ V := by
      intro j
      have h1 : A.h j * w ∈ (1 : Submodule R Ω) := by
        rw [← hone A.m, ← hpow]
        exact Submodule.mul_mem_mul (by rw [← A.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hw
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      obtain ⟨e, he⟩ := hF j I y hy
      refine ⟨a, ⟨e, ?_⟩, ha⟩
      change a ^ e • y ∈ G
      have hw' : w ^ e ∈ Q' ^ (A.m * e) := by
        rw [pow_mul]; exact Submodule.pow_mem_pow _ hw e
      have h2 : (y * A.h j ^ e) * w ^ e ∈ G * P ^ (A.m * e) * Q' ^ (A.m * e) :=
        Submodule.mul_mem_mul (by rw [← hpow]; exact he) hw'
      rw [mul_assoc, hone, mul_one] at h2
      rw [Algebra.smul_def, map_pow]
      change ((a : Ω)) ^ e * y ∈ G
      have : (a : Ω) = A.h j * w := ha
      rw [this]
      convert h2 using 1
      ring
    refine Submodule.span_induction (p := fun u _ => u * w ∈ V) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, rfl⟩; exact hmem j
    · rw [zero_mul]; exact V.zero_mem
    · intro a b _ _ ha hb; rw [add_mul]; exact V.add_mem ha hb
    · intro r a _ ha; rw [smul_mul_assoc]; exact V.smul_mem r ha
  obtain ⟨b, ⟨n, hn⟩, hb⟩ := hkey (by rw [hone]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have hb1 : (b : Ω) = 1 := hb
  have hbn : b ^ n • y ∈ G := hn
  rwa [Algebra.smul_def, map_pow, show algebraMap R Ω b = 1 from hb1, one_pow, one_mul] at hbn

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section Aug

variable (S : Type u) [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {n : ℕ}

def Cech.AugExact {y : Fin (n + 1) → Ω} (G : Chart y → Submodule S E) (B : Submodule S E) : Prop :=
  (∀ J, B ≤ G J) ∧
  (∀ b ∈ B, (∀ _ : Cech.Idx (support y) 0, b = 0) → b = 0) ∧
  (∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G 0,
      Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) 0 s = 0 → ∃ b ∈ B, ∀ J, s J = b) ∧
  ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G (p + 1),
    Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) (p + 1) s = 0 →
      ∃ t ∈ Cech.Cdeg (fun _ : Chart y => E) G p,
        Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) p t = s

end Aug

section Z

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E] {r : ℕ}

def secsOnZChart (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (I : Chart x)
    (J : Chart h) : Submodule S E :=
  Submodule.span S {e | ∃ n : ℕ, xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I}

def secsOnZ (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (J : Chart h) : Submodule S E :=
  ⨅ I : Chart x, secsOnZChart G H h I J

end Z

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def GradedCech.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ),
    ∃ e : ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (i : ℕ) (c : ℤ),
        IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c ≃ₗ[S] Kleiman.cohom (gradedEquiv S N M G) i c,
      (∀ (M M' : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (G' : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M')
        (f : M →ₗ[Poly S N] M') (hf : IndefiniteRowSideFullHecke.Kleiman.IsGradedHom S N G G' f) (i : ℕ) (c : ℤ)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c),
        e M' G' i c (IndefiniteRowSideFullHecke.Kleiman.gradedHmap S N hf i c z) =
          Kleiman.cohomMap (⟨f, fun c m hm => hf c m hm⟩ :
            Kleiman.GradedHom (gradedEquiv S N M G) (gradedEquiv S N M' G')) i c (e M G i c z)) ∧
      ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (m : M) (hm : m ∈ G.piece c)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G 0 c),
        (z : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) = IndefiniteRowSideFullHecke.Kleiman.unitCochain S N M m →
        e M G 0 c (Submodule.Quotient.mk z) = Kleiman.toH0 (gradedEquiv S N M G) c ⟨m, hm⟩

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end
