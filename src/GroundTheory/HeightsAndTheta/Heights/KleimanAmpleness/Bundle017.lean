module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

theorem GlobalFunctionsIntegral.proof : GlobalFunctionsIntegral.Statement := by
  intro k _ K _ _ N y a hy ha
  classical

  have key : ∀ i : Fin (N + 1), ∃ (e : ℕ) (f : MvPolynomial (Fin (N + 1)) k),
      f.IsHomogeneous e ∧ a * y i ^ e = aeval y f := by
    intro i
    by_cases hi : y i = 0
    · exact ⟨1, 0, isHomogeneous_zero _ _ _, by simp [hi]⟩
    · obtain ⟨f, s, e, hs, hf, hse, hrep⟩ := ha i hi
      obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
      have hne : (X i ^ n : MvPolynomial (Fin (N + 1)) k) ≠ 0 := pow_ne_zero _ (X_ne_zero i)
      have hn : n = e := (isHomogeneous_X_pow i n).inj_right hse hne
      subst hn
      refine ⟨n, f, hf, ?_⟩
      have hyn : y i ^ n ≠ 0 := pow_ne_zero _ hi
      rw [hrep, map_pow, aeval_X, div_mul_cancel₀ _ hyn]
  choose e f hf hrel using key
  set E := ∑ i, e i with hE
  let M : Submodule k K :=
    (homogeneousSubmodule (Fin (N + 1)) k E).map (aeval y : MvPolynomial (Fin (N + 1)) k →ₐ[k] K).toLinearMap
  refine isIntegral_of_smul_mem_submodule M ?_ ((homogeneousSubmodule_fg (Fin (N + 1)) k E).map _) a ?_
  ·
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine (Submodule.ne_bot_iff M).mpr ⟨y i ^ E, ⟨X i ^ E, ?_, by simp⟩, pow_ne_zero _ hi⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow i E)
  ·
    rintro _ ⟨g, hg, rfl⟩
    have hgE : g.IsHomogeneous E := (mem_homogeneousSubmodule _ _).mp hg

    rw [smul_eq_mul, AlgHom.toLinearMap_apply, g.as_sum, map_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hmE : m.degree = E := by
      by_contra h
      exact mem_support_iff.mp hm (hgE.coeff_eq_zero h)
    have hsum : ∑ i, e i ≤ ∑ i, m i := by
      rw [← hE, ← hmE, Finsupp.degree_eq_sum]
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    set m' := m - Finsupp.single i (e i) with hm'
    have hsplit : m' + Finsupp.single i (e i) = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
    have hdeg : m'.degree + e i = E := by
      rw [← hmE, ← hsplit, map_add (f := _), Finsupp.degree_single]
    refine ⟨monomial m' (AddMonoidAlgebra.coeff g m) * f i, ?_, ?_⟩
    · refine (mem_homogeneousSubmodule _ _).mpr ?_
      rw [← hdeg]
      exact (isHomogeneous_monomial _ rfl).mul (hf i)
    · have hmono : (monomial m (AddMonoidAlgebra.coeff g m) : MvPolynomial (Fin (N + 1)) k) =
          monomial m' (AddMonoidAlgebra.coeff g m) * X i ^ e i := by
        rw [X_pow_eq_monomial, monomial_mul, mul_one, hsplit]
      rw [AlgHom.toLinearMap_apply, map_mul, ← hrel i, hmono, map_mul, map_pow, aeval_X]
      ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem Cech.H_subsingleton {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
    [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)
    (h : ∀ I, Subsingleton (G I)) (i : ℕ) : Subsingleton (Cech.H G ρ i) := by
  have h2 : Subsingleton (Cech.Cochain G i) := by
    unfold Cech.Cochain; infer_instance
  unfold Cech.H
  refine Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun z _ => ?_)
  have hz : z = 0 := Subtype.ext (h2.elim _ _)
  rw [hz]
  exact Submodule.zero_mem _

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]


omit [IsScalarTower S Ω E] in
theorem tildeSys_twist_mono {M M' : FinGradedSub (S := S) (x := x) E} (h : ∀ c, M.piece c ≤ M'.piece c)
    (Q : SubSystem S x Ω) (I : Chart x) :
    ((M.tildeSys 0).twist Q).sub I ≤ ((M'.tildeSys 0).twist Q).sub I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨q, hq, y, hy, rfl⟩
  refine ⟨q, hq, y, ?_, rfl⟩
  change y ∈ M'.tilde 0 I
  change y ∈ M.tilde 0 I at hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩

theorem quotH_self_subsingleton (F : SubSystem S x E) (i : ℕ) :
    Subsingleton (SubSystem.quotH F F i) := by
  have h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I) := fun I =>
    Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)
  unfold SubSystem.quotH
  exact Cech.H_subsingleton _ h1 i

end Helpers

theorem StepTwo.Reduce.proof (hF : StepTwo.Filt.Statement.{u, v, w}) (hT : QuotTrans.Statement.{u, v, w})
    (hP : StepTwo.Piece.Statement.{u, v, w}) : StepTwo.Reduce.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ h21 J hJ
  obtain ⟨n, Nf, g, deg, pr, h0, hlast, hk⟩ := hF S Ω N x E M₁ M₂ h21 J hJ
  refine ⟨n, pr, fun i => -deg i, fun i => ⟨(hk i).1, (hk i).2.1, (hk i).2.2.1, (hk i).2.2.2.1⟩, ?_⟩
  intro Q c hQ
  have key : ∀ (m : ℕ) (hm : m < n + 1), (∀ a, (Nf 0).piece a ≤ (Nf ⟨m, hm⟩).piece a) ∧
      Subsingleton (SubSystem.quotH (((Nf ⟨m, hm⟩).tildeSys 0).twist (Q.twist (twistSys S x c)))
        (((Nf 0).tildeSys 0).twist (Q.twist (twistSys S x c))) 1) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ => le_rfl, quotH_self_subsingleton _ 1⟩
    | succ m ih =>
      intro hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨hpr, hhom, hprx, -, hg, hsup, hann⟩ := hk ⟨m, by omega⟩
      have hstep := hP S Ω N x E _ _ (g ⟨m, by omega⟩) (deg ⟨m, by omega⟩) (pr ⟨m, by omega⟩) hpr hhom
        hprx hg hsup hann Q c (fun hrel => by rw [sub_eq_add_neg]; exact hQ ⟨m, by omega⟩ hrel)
      have hle : ∀ a, (Nf ⟨m, by omega⟩).piece a ≤ (Nf ⟨m + 1, hm⟩).piece a := fun a => by
        rw [show (⟨m + 1, hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, by omega⟩ from rfl, hsup a]
        exact le_sup_left
      exact ⟨fun a => (ih1 a).trans (hle a), hT S Ω N x E _ _ _ (tildeSys_twist_mono ih1 _)
        (tildeSys_twist_mono hle _) ih2 hstep⟩
  obtain ⟨-, h⟩ := key n (Nat.lt_succ_self n)
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, hlast, h0] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech.Partition

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V]
  [Module R V]

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (A : Finset (Fin n)) : V :=
  if h : A.card = i + 1 ∧ A ⊆ U then
    s ⟨⟨A, Finset.card_pos.mp (h.1 ▸ Nat.succ_pos i), h.2⟩, h.1⟩
  else 0

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

def coneY {i : ℕ} (k : Fin n) (z : Cech.Cochain (fun _ : Cell U => V) (i + 1)) (A : Finset (Fin n)) : V :=
  if k ∈ A then 0 else Cech.sgn (insert k A) k • onSet z (insert k A)

theorem cone_d {i : ℕ} {z : Cech.Cochain (fun _ : Cell U => V) (i + 1)}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0) {k : Fin n} (hk : k ∈ U)
    (K : Cech.Idx U (i + 1)) :
    ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) = z K := by
  have hcoc : ∀ L : Finset (Fin n), L ⊆ U → L.card = i + 1 + 1 + 1 →
      ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
    intro L hLU hL
    have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), hLU⟩, hL⟩
    rw [d_eq] at h
    exact h
  rw [← onSet_idx z K]
  have hK : K.1.1.card = i + 1 + 1 := K.2
  have hKU : K.1.1 ⊆ U := K.1.2.2
  generalize K.1.1 = Kf at hK hKU ⊢
  by_cases h : k ∈ Kf
  · rw [Finset.sum_eq_single k]
    · rw [coneY, if_neg (Finset.notMem_erase k Kf), Finset.insert_erase h, smul_smul,
        Cech.Cone.sgn_mul_self, one_smul]
    · intro j hj hne
      rw [coneY, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
    · exact fun h' => absurd h h'
  · have hc := hcoc (insert k Kf) (Finset.insert_subset hk hKU)
      (by rw [Finset.card_insert_of_notMem h, hK])
    rw [Finset.sum_insert h, Finset.erase_insert h] at hc
    have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
    have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY k z (Kf.erase j) =
        -(Cech.sgn (insert k Kf) k •
          ∑ j ∈ Kf, Cech.sgn (insert k Kf) j • onSet z ((insert k Kf).erase j)) := by
      rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : k ≠ j := fun e => h (e ▸ hj)
      have hni : k ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
      rw [Finset.erase_insert_of_ne hne, coneY, if_neg hni, smul_smul, smul_smul,
        Cech.Cone.sgn_key h hj, neg_smul]
    rw [hs, hb, smul_neg, neg_neg, smul_smul, Cech.Cone.sgn_mul_self, one_smul]

theorem exact_of_partition {A : Type w} [Semiring A] [Module A V] (M : Cell U → Submodule R V)
    {i : ℕ} (z : Cech.Cochain (fun _ : Cell U => V) (i + 1))
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0)
    (a : Fin n → A) (ha : ∑ k ∈ U, a k = 1)
    (hmem : ∀ (K : Cech.Idx U i) (k : Fin n), k ∈ U → k ∉ K.1.1 →
      a k • onSet z (insert k K.1.1) ∈ M K.1) :
    ∃ t ∈ Cech.Cdeg (fun _ : Cell U => V) M i,
      Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i t = z := by
  refine ⟨fun K => ∑ k ∈ U, a k • coneY k z K.1.1, fun K _ => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k hk => ?_
    unfold coneY
    split_ifs with h
    · rw [smul_zero]; exact zero_mem _
    · rw [smul_comm]; exact zsmul_mem (hmem K k hk h) _
  · funext K
    rw [d_eq]
    have hY : ∀ j ∈ K.1.1, onSet (fun I => ∑ k ∈ U, a k • coneY k z I.1.1 :
        Cech.Cochain (fun _ : Cell U => V) i) (K.1.1.erase j) =
          ∑ k ∈ U, a k • coneY k z (K.1.1.erase j) := by
      intro j hj
      unfold onSet
      rw [dite_eq_left ⟨by rw [Finset.card_erase_of_mem hj, K.2]; rfl,
        (Finset.erase_subset _ _).trans K.1.2.2⟩]
    rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
    calc ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • ∑ k ∈ U, a k • coneY k z (K.1.1.erase j)
        = ∑ k ∈ U, a k • ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) := by
          simp_rw [Finset.smul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      _ = ∑ k ∈ U, a k • z K := Finset.sum_congr rfl fun k hk => by rw [cone_d hz hk K]
      _ = z K := by rw [← Finset.sum_smul, ha, one_smul]

theorem onSet_pair {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    {a b : Fin n} (haU : a ∈ U) (hbU : b ∈ U) (hab : a < b) : onSet z {a} = onSet z {b} := by
  have hcard : ({a, b} : Finset (Fin n)).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hz ⟨⟨{a, b}, Finset.insert_nonempty _ _,
    Finset.insert_subset haU (Finset.singleton_subset_iff.mpr hbU)⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin n)), Cech.sgn {a, b} j • onSet z (({a, b} : Finset _).erase j)
    = 0 at h
  have ha : a ∉ ({b} : Finset (Fin n)) := Finset.notMem_singleton.mpr hab.ne
  rw [Finset.sum_pair hab.ne, Finset.erase_insert ha, Finset.erase_insert_of_ne hab.ne,
    Finset.erase_singleton, Cech.Cone.sgn_insert ha, Cech.Cone.sgn_insert ha, if_neg (lt_irrefl _),
    if_pos hab] at h
  have e1 : Cech.sgn ({b} : Finset (Fin n)) a = 1 := by
    simp [Cech.sgn, Finset.filter_singleton, lt_asymm hab]
  have e2 : Cech.sgn ({b} : Finset (Fin n)) b = 1 := by
    simp [Cech.sgn, Finset.filter_singleton]
  rw [e1, e2, insert_empty_eq] at h
  rw [one_mul, one_smul, one_mul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    (I K : Cech.Idx U 0) : z I = z K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  have haU : a ∈ U := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  have hbU : b ∈ U := K.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self b)
  rw [← onSet_idx z I, ← onSet_idx z K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hz haU hbU h
  · rfl
  · exact (onSet_pair hz hbU haU h).symm

end Cech.Partition

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

open IsLocalRing

def locQuotEquiv {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] (J : Ideal R) :
    (Localization.AtPrime q ⧸ J.localized' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q))) ≃ₗ[Localization.AtPrime q]
      LocalizedModule q.primeCompl (R ⧸ J) :=
  have := IsLocalization.linearMap_compatibleSMul q.primeCompl
  (IsLocalizedModule.linearEquiv q.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)))
    (LocalizedModule.mkLinearMap _ _)).restrictScalars _

theorem CutMultPos.proof : CutMultPos.Statement := by
  intro S _ _ N J qq h
  have : qq.IsPrime := h.1.1
  let J' : Ideal (Localization.AtPrime qq) :=
    J.localized' (Localization.AtPrime qq) qq.primeCompl
      (Algebra.linearMap (Poly S N) (Localization.AtPrime qq))
  have hJ' : J' = J.map (algebraMap (Poly S N) (Localization.AtPrime qq)) := by
    simp only [J', Submodule.localized'_eq_span, Ideal.map]
    rfl
  have hmin : maximalIdeal (Localization.AtPrime qq) ∈ J'.minimalPrimes := by
    rw [hJ', IsLocalization.minimalPrimes_map qq.primeCompl, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact h
  have hne : J' ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hmin.1.2
  have : Nontrivial (Localization.AtPrime qq ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsArtinianRing (Localization.AtPrime qq ⧸ J') :=
    quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J' hmin
  have : IsArtinian (Localization.AtPrime qq) (Localization.AtPrime qq ⧸ J') :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J'))
  have : IsNoetherianRing (Localization.AtPrime qq) :=
    IsLocalization.isNoetherianRing qq.primeCompl _ inferInstance
  unfold cutMult
  rw [← (locQuotEquiv qq J).length_eq]
  exact ⟨Module.length_pos, Module.length_ne_top.lt_top⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u w

theorem CutComponent.proof (hZ : CutZeroNotLe.Statement.{u, w}) (hE : CutNonempty.Statement.{u, w})
    (hD : CutDimLower.Statement.{u, w}) : CutComponent.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs hI
  obtain ⟨qq, hq, j, hj⟩ := hE k Ω N x n pp L s hW hL hs hI
  obtain ⟨f, hfZ, hfp⟩ := hZ k Ω N x (n + 1) pp L s hW hs hI
  have hlo := hD k Ω N x n pp L s qq hW hs hq ⟨j, hj⟩
  have hJq : pp ⊔ zeroIdeal L.toSubSystem s ≤ qq := hq.1.2
  have hqp : qq.IsPrime := hq.1.1
  have hppq : pp ≤ qq := le_sup_left.trans hJq
  have := hW.isPrime

  have hpH : pp.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) := by
    intro i r hr
    have := hW.homog r hr i
    rwa [← decomposition.decompose'_apply] at this
  have hZH : (zeroIdeal L.toSubSystem s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
    Ideal.homogeneous_span _ _ (by rintro f ⟨c, hc, -⟩; exact ⟨c, hc⟩)
  have hJH : (pp ⊔ zeroIdeal L.toSubSystem s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) := by
    have h := (HomogeneousIdeal.toIdeal_sup ⟨pp, hpH⟩ ⟨_, hZH⟩).symm ▸
      (⟨pp, hpH⟩ ⊔ ⟨_, hZH⟩ : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) k)).isHomogeneous
    exact h

  have hcore : qq ≤ (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).toIdeal := by
    refine hq.2 ⟨hqp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    rw [← hJH.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJq
  have hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq := by
    intro p hp d
    have := (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).isHomogeneous d (hcore hp)
    have h2 : homogeneousComponent d p ∈
        (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).toIdeal := by
      rw [← decomposition.decompose'_apply]
      exact this
    exact Ideal.toIdeal_homogeneousCore_le _ _ h2

  have hup : ringKrullDim (Poly k N ⧸ qq) + 1 ≤ ((n + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hW.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hppq)
      (Ideal.Quotient.factor_surjective hppq) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hJq (Ideal.mem_sup_right hfZ)
  refine ⟨qq, hq, hqp, hhom, hW.le.trans hppq, ⟨j, hj⟩, ?_⟩

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize ringKrullDim (Poly k N ⧸ qq) = D at hup hlo ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hlo (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe m =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have h1 : n + 1 ≤ m := by exact_mod_cast hlo
      have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have h3 := Nat.cast_le.mp h2
      have : m = n + 1 := by omega
      subst this
      rfl

end GroundTheory.Heights₂.Heights.Kleiman
end
