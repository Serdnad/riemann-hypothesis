module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
import Formalism.RealPlaceAnalysis.FinalF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle009
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv

@[expose] public section

section

section

noncomputable section

open MvPolynomial Matrix
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF.BlockEvaluationOffDiagonal

variable {n : ℕ}

lemma ev_inl (k : Mat n) (a b : Fin n) : ev k (X (Sum.inl (a, b))) = k a b := by
  simp [GlobalTheory.PsCo.Pc1.ev]

lemma ev_inr (k : Mat n) (a b : Fin n) : ev k (X (Sum.inr (a, b))) = star (k a b) := by
  simp [GlobalTheory.PsCo.Pc1.ev]

lemma offdiag {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) {a b : Fin n} (hab : ε a ≠ ε b) :
    k a b = 0 := by
  have h := congrFun (congrFun hk.2 a) b
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, Bool.false_eq_true, if_false, if_true] at h hab
  · exact absurd rfl hab
  · linear_combination (1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * h
  · exact absurd rfl hab

def bM (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) (blockAlg ε) := fun a b =>
  if h : ε a = ε b then ⟨X (Sum.inl (a, b)), Algebra.subset_adjoin ⟨a, b, h, rfl⟩⟩ else 0

def evB (ε : Fin n → Bool) (k : Mat n) : blockAlg ε →+* ℂ := (ev k).comp (blockAlg ε).val.toRingHom

lemma evB_apply (ε : Fin n → Bool) (k : Mat n) (x : blockAlg ε) : evB ε k x = ev k (x : Poly n) := rfl

lemma map_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : (bM ε).map (evB ε k) = k := by
  ext a b
  simp only [Matrix.map_apply, bM]
  split_ifs with h
  · rw [evB_apply, ev_inl]
  · rw [map_zero, offdiag hk h]

lemma det_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : evB ε k (bM ε).det = k.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_bM hk]

lemma adj_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (a b : Fin n) :
    evB ε k ((bM ε).adjugate a b) = k.adjugate a b := by
  have := congrFun (congrFun (RingHom.map_adjugate (evB ε k) (bM ε)) a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, map_bM hk] at this
  exact this

lemma ev_detbP (k : Mat n) : ev k (detbP n) = conj k.det := by
  rw [GlobalTheory.PsCo.Pc1.detbP, RingHom.map_det, (starRingEnd ℂ).map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, ev_inr]

lemma conj_det_mul {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : conj k.det * k.det = 1 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.mp hk.1)
  rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h
  simpa using h

lemma star_entry {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (a b : Fin n) :
    star (k a b) = conj k.det * k.adjugate b a := by
  have hu : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  have h1 : k.adjugate * k = k.det • (1 : Mat n) := Matrix.adjugate_mul k
  have h2 : kᴴ = conj k.det • k.adjugate := by
    calc kᴴ = (conj k.det * k.det) • kᴴ := by rw [conj_det_mul hk, one_smul]
      _ = conj k.det • ((k.det • (1 : Mat n)) * kᴴ) := by rw [smul_mul_assoc, one_mul, smul_smul]
      _ = conj k.det • k.adjugate := by
        rw [← h1, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu, Matrix.mul_one]
  have := congrFun (congrFun h2 b) a
  simpa [Matrix.conjTranspose_apply] using this

def dB (ε : Fin n → Bool) : Poly n := ((bM ε).det : Poly n)

lemma dB_mem (ε : Fin n → Bool) : dB ε ∈ blockAlg ε := (bM ε).det.2

lemma ev_dB {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : ev k (dB ε) = k.det := det_bM hk

def Good (ε : Fin n → Bool) (P : Poly n) : Prop :=
  ∃ (M : ℕ) (Q : Poly n), Q ∈ blockAlg ε ∧ ∀ k ∈ Formalism.REAL.Kset ε, ev k P = ev k (detbP n ^ M * Q)

lemma good (ε : Fin n → Bool) (P : Poly n) : Good ε P := by
  refine MvPolynomial.induction_on P ?_ ?_ ?_
  · intro a
    refine ⟨0, C a, ?_, fun k _ => by simp⟩
    simpa [MvPolynomial.algebraMap_eq] using (blockAlg ε).algebraMap_mem a
  · rintro p q ⟨M1, Q1, h1, e1⟩ ⟨M2, Q2, h2, e2⟩
    refine ⟨M1 + M2, Q1 * dB ε ^ M2 + Q2 * dB ε ^ M1, ?_, fun k hk => ?_⟩
    · exact add_mem (mul_mem h1 (pow_mem (dB_mem ε) _)) (mul_mem h2 (pow_mem (dB_mem ε) _))
    · have hc : ∀ m : ℕ, conj k.det ^ m * k.det ^ m = 1 := fun m => by
        rw [← mul_pow, conj_det_mul hk, one_pow]
      rw [map_add (f := _), e1 k hk, e2 k hk]
      simp only [map_mul, map_pow, map_add (f := _), ev_detbP, ev_dB hk]
      rw [pow_add]
      linear_combination (-(conj k.det ^ M1 * ev k Q1)) * hc M2 + (-(conj k.det ^ M2 * ev k Q2)) * hc M1
  · rintro p i ⟨M, Q, hQ, e⟩
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · refine ⟨M, Q * ((bM ε a b : blockAlg ε) : Poly n), mul_mem hQ (bM ε a b).2, fun k hk => ?_⟩
      have h : ev k ((bM ε a b : blockAlg ε) : Poly n) = k a b := by
        have := congrFun (congrFun (map_bM hk) a) b
        rw [Matrix.map_apply] at this
        exact this
      rw [map_mul, e k hk, ev_inl]
      simp only [map_mul, h]
      ring
    · refine ⟨M + 1, Q * (((bM ε).adjugate b a : blockAlg ε) : Poly n),
        mul_mem hQ ((bM ε).adjugate b a).2, fun k hk => ?_⟩
      have h : ev k (((bM ε).adjugate b a : blockAlg ε) : Poly n) = k.adjugate b a := adj_bM hk b a
      rw [map_mul, e k hk, ev_inr, star_entry hk]
      simp only [map_mul, map_pow, h, ev_detbP]
      ring

end GlobalTheory.PsCo.PcEF.BlockEvaluationOffDiagonal

namespace GlobalTheory.PsCo.PcEF

theorem maxCompactPolynomial_blockTimesConjDetPower : BlockForm := by
  intro n ε P
  exact BlockEvaluationOffDiagonal.good ε P

end GlobalTheory.PsCo.PcEF

end
end
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

theorem eq_discreteSeries_of_lowestKType_casimir : DatumEquiv := by
  intro n ε lam hgap H _ _ _ σ hσ hirr V hV hV0 hc X _ _ D hD
  haveI : CompleteSpace X := hD.1
  have hσD : IsURepOn (UJset ε) D := hD.2.2.1
  have hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v :=
    kStable_of_isKStableSub hσ (isDerivedOn_smE hσ) V hV.1 hV.2.1
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := arb_datum hD (casOnSmooth_of_isDS hD hgap)
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0
  have htop' := data_closGen_eq_top hgap hσD (isDerivedOn_smE hσD) hV' hc' hVK' hD.2.2.2.1 hV0'
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ (isDerivedOn_smE hσ) hV hc hVK hV0
    hσD (isDerivedOn_smE hσD) hV' hc' hVK' hV0'
  refine ⟨((LinearIsometryEquiv.ofTop _ _ htop).symm.trans U).trans (LinearIsometryEquiv.ofTop _ _ htop'),
    fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.ofTop_apply]
  apply hU g hg
  simp only [LinearIsometryEquiv.ofTop_symm_apply_coe]

end GlobalTheory.PsCo.PcEF
end
end

section

open GlobalTheory.LKCount

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

end GlobalTheory.ConjugateFold

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

noncomputable def foldMap (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (y : G)
    (p : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) :
    {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) //
      DoubleCoset.mk T K (Quotient.out q) = DoubleCoset.mk T K y} :=
  ⟨DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y), by
    obtain ⟨g, hg, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out p : T) : G) * y)
    rw [he, DoubleCoset.eq]
    refine ⟨(g * ((Quotient.out p : T) : G))⁻¹, T.inv_mem (T.mul_mem (hΓT hg) (Quotient.out p).2),
      k⁻¹, K.inv_mem hk, by group⟩⟩

end GlobalTheory.ConjugateFold

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

end GlobalTheory.ConjugateFold

namespace GlobalTheory

variable {G : Type} [Group G] in
private lemma mem_map_conj_iff_inv_mul_mul_mem' (K : Subgroup G) (a x : G) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

variable {G : Type} [Group G] in
private lemma foldMap_bijective' (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (y : G) :
    Function.Bijective (_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y) := by
  constructor
  · intro p p' h
    have h' : DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y) =
        DoubleCoset.mk Γ' K (((Quotient.out p' : T) : G) * y) := congrArg Subtype.val h
    obtain ⟨γ, hγ, k, hk, he⟩ := DoubleCoset.eq.mp h'
    have hmem : y * k * y⁻¹ = ((Quotient.out p : T) : G)⁻¹ * γ⁻¹ * ((Quotient.out p' : T) : G) := by
      rw [eq_mul_inv_of_mul_eq he]; group
    have hT : y * k * y⁻¹ ∈ T := by
      rw [hmem]
      exact T.mul_mem (T.mul_mem (T.inv_mem (Quotient.out p).2) (T.inv_mem (hΓT hγ))) (Quotient.out p').2
    rw [← DoubleCoset.out_eq' p, ← DoubleCoset.out_eq' p', DoubleCoset.eq]
    refine ⟨⟨γ, hΓT hγ⟩, by rw [Subgroup.mem_subgroupOf]; exact hγ, ⟨y * k * y⁻¹, hT⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem']
      refine ⟨hT, ?_⟩
      rw [show y⁻¹ * (y * k * y⁻¹) * y = k by group]
      exact hk
    · apply Subtype.ext
      push_cast
      rw [eq_mul_inv_of_mul_eq he]
      group
  · rintro ⟨q, hq⟩
    obtain ⟨t, ht, k, hk, hqe⟩ := DoubleCoset.eq.mp hq.symm
    refine ⟨DoubleCoset.mk (Γ'.subgroupOf T) ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T)
      ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change DoubleCoset.mk Γ' K (((Quotient.out (DoubleCoset.mk (Γ'.subgroupOf T)
      ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T) ⟨t, ht⟩) : T) : G) * y) = q
    obtain ⟨γ, hγ, h, hh, hout⟩ := DoubleCoset.mk_out_eq_mul (Γ'.subgroupOf T)
      ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T) ⟨t, ht⟩
    rw [hout, ← DoubleCoset.out_eq' q, DoubleCoset.eq]
    rw [Subgroup.mem_subgroupOf] at hγ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem'] at hh
    refine ⟨(γ : G)⁻¹, Γ'.inv_mem hγ, (y⁻¹ * h * y)⁻¹ * k, K.mul_mem (K.inv_mem hh.2) hk, ?_⟩
    rw [hqe]
    push_cast
    group

variable {G : Type} [Group G] in
private lemma card_subgroupOf_inf_map_conj_eq (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (t : T) (y : G) :
    Nat.card (Γ'.subgroupOf T ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj t).toMonoidHom : Subgroup T) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom : Subgroup G) := by
  set S : Subgroup T := Γ'.subgroupOf T ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj t).toMonoidHom
  have e : S.map T.subtype = Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
    ext x
    rw [Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', Subgroup.mem_map]
    have hconj : ∀ s : T, (((MulAut.conj t).symm s : T) : G) = (t : G)⁻¹ * s * t := by
      intro s
      rw [MulAut.conj_symm_apply]
      push_cast
      rfl
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', hconj] at hs
      refine ⟨hs.1, ?_⟩
      rw [show ((t : G) * y)⁻¹ * (T.subtype s) * ((t : G) * y) = y⁻¹ * ((t : G)⁻¹ * s * t) * y by
        simp only [Subgroup.coe_subtype]; group]
      exact hs.2.2
    · rintro ⟨hx, hxK⟩
      refine ⟨⟨x, hΓT hx⟩, ?_, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', hconj]
      refine ⟨hx, T.mul_mem (T.mul_mem (T.inv_mem t.2) (hΓT hx)) t.2, ?_⟩
      rw [show y⁻¹ * ((t : G)⁻¹ * x * t) * y = ((t : G) * y)⁻¹ * x * ((t : G) * y) by group]
      exact hxK
  rw [← e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ T.subtype_injective).toEquiv

variable {G : Type} [Group G] in
private lemma card_inf_map_conj_mul_mul_eq (Γ' K : Subgroup G) {γ k : G} (hγ : γ ∈ Γ') (hk : k ∈ K) (a : G) :
    Nat.card (Γ' ⊓ K.map (MulAut.conj (γ * a * k)).toMonoidHom : Subgroup G) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj a).toMonoidHom : Subgroup G) := by
  have e : (Γ' ⊓ K.map (MulAut.conj (γ * a * k)).toMonoidHom : Subgroup G) =
      (Γ' ⊓ K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h1 : (γ * a * k)⁻¹ * x * (γ * a * k) = k⁻¹ * (a⁻¹ * (γ⁻¹ * x * γ) * a) * k := by group
    rw [h1, Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk),
      Subgroup.mul_mem_cancel_right Γ' hγ, Subgroup.mul_mem_cancel_left Γ' (Γ'.inv_mem hγ)]
  rw [e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj γ).injective).toEquiv.symm

theorem _root_.GlobalTheory.finsum_fold_intermediate : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out q) = ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G), ((_root_.GlobalTheory.LKCount.massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) := by
  intro G _ Γ' T K F hΓT hF _ hfin
  have hsupp : (Function.support fun q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) =>
      ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
        F (Quotient.out q)).Finite :=
    hfin.subset fun q hq => right_ne_zero_of_mul hq
  refine (_root_.GlobalTheory.finsum_fiberwise_of_finite_support (A := DoubleCoset.Quotient (Γ' : Set G) (K : Set G))
    (B := DoubleCoset.Quotient (T : Set G) (K : Set G))
    (fun q => DoubleCoset.mk T K (Quotient.out q)) _ hsupp).trans (finsum_congr fun y' => ?_)
  set y := Quotient.out y'
  have hy' : DoubleCoset.mk T K y = y' := DoubleCoset.out_eq' y'
  have hfib : ∀ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
      DoubleCoset.mk T K (Quotient.out q) = DoubleCoset.mk T K y → F (Quotient.out q) = F y := by
    intro q hq
    obtain ⟨t, ht, k, hk, hqe⟩ := DoubleCoset.eq.mp hq.symm
    rw [hqe, hF t ht y k hk]
  let e : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T) →
      {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) // DoubleCoset.mk T K (Quotient.out q) = y'} :=
    fun p => ⟨(_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y p).1,
      (_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y p).2.trans hy'⟩
  have hb := foldMap_bijective' Γ' T K hΓT y
  have he : Function.Bijective e := by
    constructor
    · intro p p' h
      have h' := congrArg Subtype.val h
      exact hb.1 (Subtype.ext h')
    · rintro ⟨q, hq⟩
      obtain ⟨p, hp⟩ := hb.2 ⟨q, hq.trans hy'.symm⟩
      have hp' := congrArg Subtype.val hp
      exact ⟨p, Subtype.ext hp'⟩
  rw [← finsum_eq_of_bijective e he (fun _ => rfl)]
  have hterm : ∀ p, ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out (e p).1)).toMonoidHom :
      Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out (e p).1) =
      ((Nat.card ((Γ'.subgroupOf T) ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj (Quotient.out p)).toMonoidHom : Subgroup T) : ℕ) : ℂ)⁻¹ * F y := by
    intro p
    obtain ⟨γ, hγ, k, hk, hg⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out p : T) : G) * y)
    have hval : (e p).1 = DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y) := rfl
    rw [card_subgroupOf_inf_map_conj_eq Γ' T K hΓT, hval, hg, card_inf_map_conj_mul_mul_eq Γ' K hγ hk,
      show γ * (((Quotient.out p : T) : G) * y) * k = (γ * ((Quotient.out p : T) : G)) * y * k by group,
      hF _ (T.mul_mem (hΓT hγ) (Quotient.out p).2) y k hk]
  rw [finsum_congr hterm]
  by_cases hFy : F y = 0
  · simp [hFy]
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} :=
    hfin.to_subtype
  haveI : Finite (DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) :=
    Finite.of_injective
      (β := {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0})
      (fun p => ⟨(e p).1, by
        show F (Quotient.out (e p).1) ≠ 0
        rw [hfib _ ((e p).2.trans hy'.symm)]
        exact hFy⟩)
      (fun p p' h => by
        have h' := congrArg Subtype.val h
        exact he.1 (Subtype.ext h'))
  letI := Fintype.ofFinite (DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T))
  unfold _root_.GlobalTheory.LKCount.massC
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_mul, Rat.cast_sum]
  simp

end GlobalTheory
end

section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS
open scoped InnerProductSpace Matrix

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sumTypes_conjT_mem {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : gᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hg
  refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hu), ?_⟩
  have h := congrArg Matrix.conjTranspose hc
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at h
  exact h.symm

theorem sumTypes_mul_conjT {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g * gᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hg.1

theorem sumTypes_inner {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) (r v : H) :
    ⟪r, σ g v⟫_ℂ = ⟪σ gᴴ r, v⟫_ℂ := by
  have hK := Formalism.REAL.kFacts n ε
  have hgU : g ∈ UJset ε := hK.1 g hg
  have hgU' : gᴴ ∈ UJset ε := hK.1 _ (sumTypes_conjT_mem hg)
  let f : H →ₗᵢ[ℂ] H := { (σ g : H →ₗ[ℂ] H) with norm_map' := hσ.2.1 g hgU }
  have e : σ g (σ gᴴ r) = r := by
    have h1 := hσ.1.2 g hgU gᴴ hgU'
    rw [sumTypes_mul_conjT hg, hσ.1.1] at h1
    have := congrArg (fun T : H →L[ℂ] H => T r) h1
    simpa using this.symm
  calc ⟪r, σ g v⟫_ℂ = ⟪f (σ gᴴ r), f v⟫_ℂ := by
        show ⟪r, σ g v⟫_ℂ = ⟪σ g (σ gᴴ r), σ g v⟫_ℂ
        rw [e]
    _ = ⟪σ gᴴ r, v⟫_ℂ := f.inner_map_map _ _

theorem finDimStable_isSumOfKTypes : SumTypes := by
  intro n ε H _ _ σ hσ S hSfd hSK
  set R : Submodule ℂ H := sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} with hR
  have hRS : R ≤ S := sSup_le fun S' hS' => hS'.1
  have : FiniteDimensional ℂ R := Submodule.finiteDimensional_of_le hRS
  have hRK : Formalism.MainNotions.S.IsKStableOn ε σ R := by
    intro g hg v hv
    have hle : R ≤ Submodule.comap (σ g : H →ₗ[ℂ] H) R := sSup_le fun S' hS' x hx => by
      obtain ⟨μ, hμ⟩ := hS'.2
      exact Submodule.mem_sSup_of_mem hS' (hμ.2.1 g hg x hx)
    exact hle hv
  have hRoK : Formalism.MainNotions.S.IsKStableOn ε σ Rᗮ := by
    intro g hg v hv r hr
    rw [sumTypes_inner hσ hg]
    exact hv _ (hRK _ (sumTypes_conjT_mem hg) r hr)
  set T : Submodule ℂ H := S ⊓ Rᗮ
  have hT : T = ⊥ := by
    by_contra h0
    have : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨μ, S', hS'T, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ T inferInstance
      (fun g hg v hv => Submodule.mem_inf.2 ⟨hSK g hg v (Submodule.mem_inf.1 hv).1, hRoK g hg v (Submodule.mem_inf.1 hv).2⟩) h0
    obtain ⟨v, hv, hv0, -⟩ := hS'.2.2.2.1
    have hvR : v ∈ R := Submodule.mem_sSup_of_mem (show S' ∈ {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} from ⟨hS'T.trans inf_le_left, μ, hS'⟩) hv
    have hvRo : v ∈ Rᗮ := (hS'T hv).2
    exact hv0 (inner_self_eq_zero.1 (hvRo v hvR))
  intro v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := R.exists_add_mem_mem_orthogonal v
  have hzS : z ∈ S := by
    have := sub_mem hv (hRS hy)
    simpa using this
  have hz0 : z ∈ T := ⟨hzS, hz⟩
  rw [hT, Submodule.mem_bot] at hz0
  rw [hz0, add_zero]
  exact hy

end GlobalTheory.PsCo.PcEF
end
end
