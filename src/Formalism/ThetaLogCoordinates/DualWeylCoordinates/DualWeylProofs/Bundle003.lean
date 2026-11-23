module

public import Formalism.GradedWeylDivisibility.Bundle001
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle001
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementH
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaNuAntitone
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhCountAll
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qa_P (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    MvPolynomial (Fin n × Fin n) R :=
  ∏ c : ↥(TCols mu), initMinor R (qa_row I c) (colH_le mu c)

def qa_e {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin (Fintype.card ↥(TCols mu)) ≃ ↥(TCols mu) :=
  (Fintype.equivFin ↥(TCols mu)).symm

lemma tableauBideterminant_eq_bideterminant (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I = bideterminant R (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_P bideterminant
  exact (Fintype.prod_equiv (qa_e mu) _ _ (fun _ => rfl)).symm

lemma qa_exp_eq_bidetExp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_exp I = bidetExp (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_exp bidetExp
  exact (Fintype.sum_equiv (qa_e mu) _ _ (fun _ => rfl)).symm

private theorem lt_colH_iff_le {n : ℕ} {mu : Fin n → ℤ} (hmu : Antitone mu) (c : ℤ) (t : Fin n) :
    (t : ℕ) < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (Finset.univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      have := hmu hmt
      omega
    exact absurd (lt_of_lt_of_le h ((Finset.card_le_card hsub).trans (Fin.card_Iio t).le)) (lt_irrefl _)
  · intro h
    have hsub : Finset.Iic t ⊆ (Finset.univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hmu hm)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ((Fin.card_Iic t).symm.le.trans (Finset.card_le_card hsub))

lemma qa_shape {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    shapeDeg (n := n) (fun k => colH mu (qa_e mu k)) = qa_nu mu := by
  have hmu' : Antitone mu := hmu
  funext t
  unfold shapeDeg qa_nu
  have h1 : (Finset.univ.filter fun k => (t : ℕ) < colH mu ↑(qa_e mu k)).card =
      (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card :=
    Finset.card_equiv (qa_e mu) (by simp)
  have h2 : (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card =
      ((TCols mu).filter fun c => (t : ℕ) < colH mu c).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort (TCols mu) (fun c => if (t : ℕ) < colH mu c then 1 else 0)
  have h3 : ((TCols mu).filter fun c => (t : ℕ) < colH mu c) = Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    have h0 : mu t ≤ mu 0 := hmu' (by simp [Fin.le_iff_val_le_val])
    simp only [TCols, Finset.mem_filter, Finset.mem_Ioc, lt_colH_iff_le hmu']
    constructor <;> intro h <;> omega
  exact h1.trans (h2.trans (by rw [h3, Int.card_Ioc]))

lemma tableauBideterminant_degree_leadingCoeff (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    (colLex n n).degree (qa_P R I) = qa_exp I ∧ (colLex n n).leadingCoeff (qa_P R I) = 1 := by
  rw [tableauBideterminant_eq_bideterminant, qa_exp_eq_bidetExp]
  exact column_lex_bideterminant R n n _ _ _ _ fun k => qa_row_strictMono I _

lemma tableauBideterminant_mem_dualWeyl (R : Type) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_P R I ∈ dualWeyl R n n (qa_nu mu) := by
  rw [tableauBideterminant_eq_bideterminant, ← qa_shape hmu]
  exact bidetMem R n n _ _ _ _

theorem dualWeyl_eq_span_standard_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) =
      Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) := by
  apply le_antisymm
  · suffices key : ∀ d : (colLex n n).syn, ∀ f ∈ dualWeyl B n n (qa_nu mu),
        (colLex n n).toSyn ((colLex n n).degree f) = d →
          f ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) by
      intro f hf
      exact key _ f hf rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      have hint : Interlaced ((colLex n n).degree f) := leadInterlaced B n n _ f hf hf0
      have hcol := colSums B n n _ f hf _ (((colLex n n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨I, hI, he⟩ := qa_exp_surj hmu _ ⟨hint, hcol⟩
      have hbS : qa_P B I ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) :=
        Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩
      have hdecomp : f = (f - (colLex n n).leadingCoeff f • qa_P B I) + (colLex n n).leadingCoeff f • qa_P B I := by
        abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)
      by_cases h0 : f - (colLex n n).leadingCoeff f • qa_P B I = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex n n) (f := f) (g := qa_P B I) ((tableauBideterminant_degree_leadingCoeff B I).1.trans he)
        (tableauBideterminant_degree_leadingCoeff B I).2 h0
      exact ih _ (hd ▸ hlt) _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl B hmu I))) rfl
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I.1

theorem dualWeyl_eq_span_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) = Submodule.span B (Set.range fun I : TIdx mu => qa_P B I) := by
  apply le_antisymm
  · rw [dualWeyl_eq_span_standard_tableauBideterminant B hmu]
    apply Submodule.span_mono
    rintro _ ⟨I, rfl⟩
    exact ⟨I.1, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_reduce [IsDomain R] (mu : Fin n → ℤ) (f : GLCoord R n) (hf : f ∈ inducedSections R mu) :
    ∃ (k : ℕ) (Q : MvPolynomial (Fin n × Fin n) R), (∀ a, 0 ≤ mu a + k) ∧
      f = ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
        algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∧
      Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n (fun a => (mu a + k).toNat) := by
  obtain ⟨N, P, hNP⟩ := IsLocalization.Away.surj (genMat R n).det f
  have hk : ∀ a, 0 ≤ mu a + ((N + (Finset.univ.sup fun b => (-mu b).toNat) : ℕ) : ℤ) := by
    intro a
    have h1 := Int.self_le_toNat (-mu a)
    have h2 : (-mu a).toNat ≤ Finset.univ.sup fun b => (-mu b).toNat :=
      Finset.le_sup (f := fun b => (-mu b).toNat) (Finset.mem_univ a)
    push_cast
    omega
  set M : ℕ := Finset.univ.sup fun b => (-mu b).toNat with hM
  have hswap : rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M)) = P * (genMat R n).det ^ M := by
    rw [rename_rename, Prod.swap_swap_eq, rename_id_apply]
  have hmain : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) =
      f * algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [hswap, map_mul, map_pow, pow_add, ← mul_assoc, hNP]
  have hunit : ((qhDet R n ^ ((N + M : ℕ) : ℤ) : (GLCoord R n)ˣ) : GLCoord R n) =
      algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, qhDet_val]
  refine ⟨N + M, rename Prod.swap (P * (genMat R n).det ^ M), hk, ?_, ?_⟩
  · rw [hmain, ← hunit, mul_comm f, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_mul]
  · have hmem : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) ∈
        inducedSections R (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) := by
      rw [hmain, mul_comm, ← hunit]
      have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) ((N + M : ℕ) : ℤ)) hf
      have e : (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) = (fun _ : Fin n => ((N + M : ℕ) : ℤ)) + mu := by
        funext a
        rw [Pi.add_apply, Int.toNat_of_nonneg (hk a), add_comm]
      rw [e]
      exact h
    exact qh_mem_dualWeyl _ _ hmem

lemma qh_span_transfer (T : Submodule R (GLCoord R n)) (u : GLCoord R n)
    (S : Set (MvPolynomial (Fin n × Fin n) R))
    (h : ∀ x ∈ S, u * algebraMap _ (GLCoord R n) (rename Prod.swap x) ∈ T)
    (Q : MvPolynomial (Fin n × Fin n) R) (hQ : Q ∈ Submodule.span R S) :
    u * algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ T := by
  let L : MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
    (LinearMap.mulLeft R u).comp ((IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap.comp
      (rename Prod.swap).toLinearMap)
  have hle : Submodule.span R S ≤ T.comap L := Submodule.span_le.mpr (fun x hx => h x hx)
  exact hle hQ

private theorem antitone_of_step_lemma {n : ℕ} (g : Fin n → ℤ) (h : ∀ l j : Fin n, (j : ℕ) = l + 1 → g j ≤ g l) :
    Antitone g := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro hb; exact le_rfl
  | succ b hab ih =>
    intro hb
    exact (h ⟨b, by omega⟩ ⟨b + 1, hb⟩ rfl).trans (ih (by omega))

theorem highest_weight_corollary_one : InducedSectionsSpanStatement := by
  intro n _ mu R _ _ _
  constructor
  · intro hmu
    apply Set.Subset.antisymm
    · intro f hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n] at hQ
      rw [SetLike.mem_coe, hfQ]
      refine qh_span_transfer (Submodule.span R (Set.range fun I : TIdx mu => mapCoord R (brk mu I))) _ _ ?_ Q hQ
      rintro x ⟨K, sz, hsz, I, hsh, rfl⟩
      exact qh_bidet_mem hmu k (hk _) sz hsz I (fun t => by rw [hsh]; exact Int.toNat_of_nonneg (hk t))
    · exact qh_span_le (by rintro _ ⟨I, rfl⟩; exact qh_brk_mem hmu I)
  · intro hmu
    ext f
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      by_contra hf0
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        apply hf0
        rw [hfQ]
        simp
      apply hmu
      have hInt := Formalism.GradedWeylDivisibility.leadInterlaced R n n _ Q hQ hQ0
      have hcol := Formalism.GradedWeylDivisibility.colSums R n n _ Q hQ _ (MonomialOrder.degree_mem_support (m := Formalism.GradedWeylDivisibility.colLex n n) hQ0)
      set m := (Formalism.GradedWeylDivisibility.colLex n n).degree Q
      apply antitone_of_step_lemma mu
      intro l j hlj
      have hI : Formalism.GradedWeylDivisibility.InterlacedAt 0 l j m := hInt l j hlj
      have hI2 := hI (lastIdx n)
      have e1 : (∑ b : Fin n with b ≤ lastIdx n, m (b, j)) = ∑ b, m (b, j) := by
        rw [Finset.filter_true_of_mem (fun b _ => qh_le_last b)]
      have e2 : (∑ b : Fin n with b < lastIdx n, m (b, l)) ≤ ∑ b, m (b, l) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have cj := hcol j
      have cl := hcol l
      have tj := Int.toNat_of_nonneg (hk j)
      have tl := Int.toNat_of_nonneg (hk l)
      omega
    · rintro rfl
      exact qh_zero_mem mu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
