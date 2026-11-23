module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.FieldTheory.Finite.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Fubini

variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

lemma relIndex_prod (H K : AddSubgroup W) (H' K' : AddSubgroup W') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1

lemma exists_fine_prod {A : AddSubgroup W} {A' : AddSubgroup W'} {φ : W × W' → ℂ}
    (h : Nice (A.prod A') φ) :
    ∃ (B : AddSubgroup W) (B' : AddSubgroup W'), B ≤ A ∧ B' ≤ A' ∧ B.relIndex A ≠ 0 ∧
      B'.relIndex A' ≠ 0 ∧ Fine (A.prod A') φ (B.prod B') := by
  obtain ⟨C, hC⟩ := h
  have i1 : (C.comap (AddMonoidHom.inl W W')).relIndex A ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨ha, A'.zero_mem⟩
  have i2 : (C.comap (AddMonoidHom.inr W W')).relIndex A' ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨A.zero_mem, ha⟩
  refine ⟨C.comap (AddMonoidHom.inl W W'), C.comap (AddMonoidHom.inr W W'),
    fun a ha => (hC.1 ha).1, fun a ha => (hC.1 ha).2, i1, i2, Model.fine_refine hC ?_ ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have := C.add_mem ha hb
    simpa using this
  · rw [relIndex_prod]
    exact mul_ne_zero i1 i2

theorem cint_prod (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ)
    (h : Nice (A.prod A') φ) :
    (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧
      cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  obtain ⟨B, B', hB, hB', i1, i2, hF⟩ := exists_fine_prod h
  let e := QuotientAddGroup.prodEquiv B B'
  have he : ∀ p : W × W', e (QuotientAddGroup.mk p) =
      ((QuotientAddGroup.mk p.1 : W ⧸ B), (QuotientAddGroup.mk p.2 : W' ⧸ B')) := fun _ => rfl
  have hS := hF.2.2.2.image e
  have f1 : ∀ w, Fine A' (fun w' => φ (w, w')) B' := by
    intro w
    refine ⟨hB', i2, fun w' b hb => ?_, (hS.image Prod.snd).subset ?_⟩
    · have := hF.2.2.1 (w, w') (0, b) ⟨B.zero_mem, hb⟩
      simpa using this
    · rintro _ ⟨w', hw', rfl⟩
      exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  have hinv : ∀ w, ∀ b ∈ B, (fun w' => φ (w + b, w')) = fun w' => φ (w, w') := by
    intro w b hb
    funext w'
    have := hF.2.2.1 (w, w') (b, 0) ⟨hb, B'.zero_mem⟩
    simpa using this
  have f2 : Fine A (fun w => cint A' (fun w' => φ (w, w'))) B := by
    refine ⟨hB, i1, fun w b hb => by simp only [hinv w b hb], (hS.image Prod.fst).subset ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have : ∃ w', φ (w, w') ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hw
      show cint A' (fun w' => φ (w, w')) = 0
      rw [Model.cint_eq (f1 w)]
      simp [hn]
    obtain ⟨w', hw'⟩ := this
    exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  refine ⟨fun w => ⟨B', f1 w⟩, ⟨B, f2⟩, ?_⟩
  rw [Model.cint_eq hF, Model.cint_eq f2, relIndex_prod]
  simp only [fun w => Model.cint_eq (f1 w)]
  have h1 : ∀ p : (W ⧸ B) × (W' ⧸ B'), φ (e.symm p).out = φ (p.1.out, p.2.out) := by
    intro p
    have : e.symm p = QuotientAddGroup.mk (p.1.out, p.2.out) := by
      rw [Equiv.symm_apply_eq, he]
      simp
    rw [this, Model.out_mk hF.2.2.1]
  have hfin : (Function.support fun p : (W ⧸ B) × (W' ⧸ B') => φ (p.1.out, p.2.out)).Finite := by
    refine hS.subset ?_
    intro p hp
    refine ⟨_, ⟨(p.1.out, p.2.out), hp, rfl⟩, ?_⟩
    rw [he]; simp
  have h2 : (∑ᶠ c : (W × W') ⧸ B.prod B', φ c.out) =
      ∑ᶠ (a : W ⧸ B) (b : W' ⧸ B'), φ (a.out, b.out) := by
    rw [← finsum_comp_equiv e.symm, finsum_congr h1, finsum_curry _ hfin]
  rw [h2]
  simp only [div_eq_mul_inv]
  rw [← finsum_mul]
  push_cast
  rw [mul_inv]
  ring

end GlobalTheory.IdxInt.Fubini
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.AmpCS

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma norm_tsum_sq_le_card_mul_sum_sq {α ι : Type*} (s : Finset ι) (f : ι → α → ℂ)
    (g : α → ℂ) (hg : ∀ a, g a = ∑ i ∈ s, f i a) (hdom : ∀ i ∈ s, ∀ a, ‖f i a‖ ≤ ‖g a‖) :
    ‖∑' a, g a‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := by
  by_cases hs : Summable g
  · have hfi : ∀ i ∈ s, Summable (f i) := fun i hi =>
      Summable.of_norm_bounded (summable_norm_iff.mpr hs) (hdom i hi)
    have hsum : ∑' a, g a = ∑ i ∈ s, ∑' a, f i a := by
      simp_rw [hg]
      exact Summable.tsum_finsetSum hfi
    rw [hsum]
    calc ‖∑ i ∈ s, ∑' a, f i a‖ ^ 2 ≤ (∑ i ∈ s, ‖∑' a, f i a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  · rw [tsum_eq_zero_of_not_summable hs, norm_zero]
    have : (0 : ℝ) ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := by positivity
    simpa using this


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.AmpCS.ampSq_le_card_mul_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 1 ≤ k → ∀ {ι : Type} (s : Finset ι) (P : ι → S.Datum → Submodule L.O S.V → Prop) (Q : S.Datum → Submodule L.O S.V → Prop), (∀ d Λ, S.IsTerm d Λ → (Q d Λ ↔ ∃ i ∈ s, P i d Λ)) → (∀ d Λ, S.IsTerm d Λ → ∀ i ∈ s, ∀ i' ∈ s, P i d Λ → P i' d Λ → i = i') → S.ampSq Q ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, S.ampSq (P i) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ ι s P Q hQ hdisj
  unfold _root_.GlobalTheory.HL.Frames.ampSq _root_.GlobalTheory.HL.Frames.sumData
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (s.card : ℝ≥0∞), mul_assoc]
  gcongr
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold _root_.GlobalTheory.HL.Frames.amp
  apply norm_tsum_sq_le_card_mul_sum_sq
  · intro a
    by_cases ht : S.IsTerm (Quotient.out o) (Quotient.out a)
    · by_cases hq : Q (Quotient.out o) (Quotient.out a)
      · obtain ⟨i, hi, hPi⟩ := (hQ _ _ ht).mp hq
        rw [if_pos ⟨ht, hq⟩, Finset.sum_eq_single_of_mem i hi, if_pos ⟨ht, hPi⟩]
        intro j hj hji
        rw [if_neg]
        rintro ⟨-, hPj⟩
        exact hji (hdisj _ _ ht j hj i hi hPj hPi)
      · rw [if_neg (fun h => hq h.2)]
        refine (Finset.sum_eq_zero fun i hi => ?_).symm
        rw [if_neg]
        rintro ⟨-, hPi⟩
        exact hq ((hQ _ _ ht).mpr ⟨i, hi, hPi⟩)
    · rw [if_neg (fun h => ht h.1)]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg (fun h => ht h.1)]
  · intro i hi a
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, (hQ _ _ h1.1).mpr ⟨i, hi, h1.2⟩⟩ h2
    · rw [norm_zero]; exact norm_nonneg _
    · simp

end GlobalTheory.AmpCS
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FramePsi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def pairL (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_span_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (s : Set (Fin n → E)) (hs : ∀ y ∈ s, hf L Hm x y = 0) :
    ∀ y ∈ Submodule.span E s, hf L Hm x y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => exact hs y h
  | zero => simp [hf]
  | add a b _ _ ha hb =>
    have : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
      simp [hf, mul_add, Finset.sum_add_distrib]
    rw [this, ha, hb, add_zero]
  | smul c a _ ha =>
    have : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
      simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, ha, mul_zero]

theorem coef_mul {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (a : S.GLV) (ha : a ∈ S.Nof g) (b : S.GLV) (hb : b ∈ S.Nof g) (j : Fin r) :
    S.coef g gs (a * b) j = S.coef g gs a j + S.coef g gs b j := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at ha hb
  obtain ⟨⟨-, ha1⟩, -⟩ := ha
  obtain ⟨⟨-, hb1⟩, hb2⟩ := hb
  have hA : b (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
    by_cases hj : (j : ℕ) + 1 < r
    · refine (hb1 ⟨j + 1, hj⟩).2 _ (Submodule.subset_span ⟨j.succ, ?_, rfl⟩)
      simp
    · have hr : (j : ℕ) + 1 = r := by have := j.2; omega
      rw [hr]
      refine hb2.2 _ ?_
      refine hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [hg, if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
  have hB := (ha1 j).2 _ hA
  have hK : S.spanTo g j ≤ LinearMap.ker (pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h0 : pairL L S.Hm (gs j) (g j.succ) = 0 := by
    change hf L S.Hm (g j.succ) (gs j) = 0
    rw [hd, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  have h1 := LinearMap.mem_ker.1 (hK hB)
  change pairL L S.Hm (gs j) (a (b (g j.succ))) =
    pairL L S.Hm (gs j) (a (g j.succ)) + pairL L S.Hm (gs j) (b (g j.succ))
  simp only [map_sub] at h1
  linear_combination h1 - h0

theorem exists_nsmul_mem [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * y ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hyF : IsAlgebraic F y := Algebra.IsAlgebraic.isAlgebraic y
  have hy : IsAlgebraic 𝒪[F] y := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 hyF
  obtain ⟨c, hc, hcy⟩ := hy.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have hp : ((Nat.card 𝓀[F] : ℕ) : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[F]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : c ∣ ((Nat.card 𝓀[F] ^ m : ℕ) : 𝒪[F]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[F] ^ m, pow_ne_zero _ Nat.card_pos.ne', (L.O_def _).2 ?_⟩
  have : ((Nat.card 𝓀[F] ^ m : ℕ) : E) * y = d • (c • y) := by
    rw [smul_smul, mul_comm d c, ← hd, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rw [this]
  exact hcy.smul d

theorem norm_additiveCharacter_typePrime_eq_one [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) : ‖L.psi0 y‖ = 1 := by
  obtain ⟨n, hn, hy⟩ := exists_nsmul_mem L y
  have h1 : L.psi0 ((n : E) * y) = 1 := by
    simpa using (L.additive_character_dual_ring _).2 hy 1 L.O.one_mem
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

theorem psi_unitary_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ a ∈ S.N, ∀ b ∈ S.N, S.psi (a * b) = S.psi a * S.psi b) ∧ (∀ a ∈ S.N', ∀ b ∈ S.N', S.psi' (a * b) = S.psi' a * S.psi' b) ∧ (∀ a, ‖S.psi a‖ = 1 ∧ ‖S.psi' a‖ = 1) ∧ ∀ y : E, ‖L.psi0 y‖ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_,
    fun a => ⟨norm_additiveCharacter_typePrime_eq_one L _, norm_additiveCharacter_typePrime_eq_one L _⟩, norm_additiveCharacter_typePrime_eq_one L⟩
  · simp only [Frames.psi, Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f S.es _ S.gram S.dual a ha b hb]
  · simp only [Frames.psi', Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f' S.es' _ S.gram' S.dual' a ha b hb]

end GlobalTheory.FramePsi
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameLevel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_coords {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) (j : ℕ)
    {y : S.V} (hy : y ∈ S.spanTo g j) :
    ∃ a : Fin (r + 1) → E, y = ∑ i, a i • g i ∧ ∀ i : Fin (r + 1), j ≤ (i : ℕ) → a i = 0 := by
  obtain ⟨c, hc, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).mp hy
  refine ⟨c, ?_, fun i hi => ?_⟩
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  · by_contra hne
    have hmem : i ∈ {i : Fin (r + 1) | (i : ℕ) < j} :=
      (Finsupp.mem_supported _ _).mp hc (Finsupp.mem_support_iff.mpr hne)
    exact absurd hi (not_le.mpr hmem)

theorem exists_coords_Mof {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g g' : Fin (r + 1) → S.V)
    {y : S.V} (hy : y ∈ S.Mof g g') :
    ∃ β γ : Fin (r + 1) → L.O, y = ∑ i, (β i : E) • g i +
      ∑ i, (γ i : E) • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
  unfold Frames.Mof at hy
  rw [Submodule.span_union, Submodule.mem_sup] at hy
  obtain ⟨u, hu, u', hu', rfl⟩ := hy
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).mp hu
  obtain ⟨γ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).mp hu'
  exact ⟨β, γ, rfl⟩

theorem th_ne_zero {L : LocE F E} {r k : ℕ} (S : Frames L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (by simpa using h)
  · exact one_ne_zero

theorem lev_le_iff {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g g' : Fin (r + 1) → S.V)
    (y : S.V) (hy : y ∈ S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) (j : ℕ) :
    S.lev g g' (algebraMap F E S.th • y) ≤ j ↔
      ∃ y₁ ∈ S.spanTo g j ⊔ S.spanTo g' j, y - y₁ ∈ S.Mof g g' := by
  constructor
  · intro hle
    unfold Frames.lev at hle
    obtain ⟨u, hu, u', hu', huy⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, hc, -⟩ := exists_coords S g (r + 1) hu
    obtain ⟨c', hc', -⟩ := exists_coords S g' (r + 1) hu'
    obtain ⟨al, al', hrep, hRR⟩ := Nat.sInf_mem (s := {j | ∃ al al' : Fin (r + 1) → E,
        algebraMap F E S.th • y = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
        ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)})
      ⟨r + 1, fun i => algebraMap F E S.th * c i, fun i => algebraMap F E S.th * c' i, by
        rw [← huy, hc, hc', smul_add, Finset.smul_sum, Finset.smul_sum]
        simp only [smul_smul], fun i hi => absurd hi (not_le.mpr i.isLt)⟩
    have hRR' : ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := fun i hi => hRR i (le_trans hle hi)
    have htt : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (th_ne_zero S), map_one]
    have hyy : y = algebraMap F E S.th⁻¹ • (∑ i, al i • g i + ∑ i, al' i • g' i) := by
      rw [← hrep, smul_smul, htt, one_smul]
    refine ⟨algebraMap F E S.th⁻¹ • (∑ i : Fin (r + 1), (if (i : ℕ) < j then al i else 0) • g i +
      ∑ i : Fin (r + 1), (if (i : ℕ) < j then al' i else 0) • g' i), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ => ?_)
        (Submodule.sum_mem _ fun i _ => ?_))
      · split_ifs with hi
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [zero_smul]
          exact Submodule.zero_mem _
      · split_ifs with hi
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [zero_smul]
          exact Submodule.zero_mem _
    · have hdiff : y - algebraMap F E S.th⁻¹ • (∑ i : Fin (r + 1), (if (i : ℕ) < j then al i else 0) • g i +
          ∑ i : Fin (r + 1), (if (i : ℕ) < j then al' i else 0) • g' i) =
          ∑ i : Fin (r + 1), algebraMap F E S.th⁻¹ • (if (i : ℕ) < j then 0 else al i • g i + al' i • g' i) := by
        rw [hyy, ← smul_sub, ← Finset.smul_sum]
        congr 1
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      rw [hdiff]
      refine Submodule.sum_mem _ fun i _ => ?_
      split_ifs with hi
      · rw [smul_zero]
        exact Submodule.zero_mem _
      · obtain ⟨hO, cc, hcc, hsum⟩ := hRR' i (not_lt.mp hi)
        have hal : al i = algebraMap F E S.th * cc - al' i := eq_sub_of_add_eq hsum
        have heq : algebraMap F E S.th⁻¹ • (al i • g i + al' i • g' i) =
            cc • g i + al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
          rw [hal]
          calc algebraMap F E S.th⁻¹ • ((algebraMap F E S.th * cc - al' i) • g i + al' i • g' i)
              = (algebraMap F E S.th⁻¹ * algebraMap F E S.th * cc) • g i +
                  al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by module
            _ = cc • g i + al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by rw [htt, one_mul]
        rw [heq]
        refine Submodule.add_mem _ ?_ ?_
        · exact Submodule.smul_mem (S.Mof g g') (⟨cc, hcc⟩ : L.O)
            (Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩))
        · exact Submodule.smul_mem (S.Mof g g') (⟨al' i, hO⟩ : L.O)
            (Submodule.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
  · rintro ⟨y₁, hy₁, hm⟩
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hy₁
    obtain ⟨a, rfl, ha⟩ := exists_coords S g j hu
    obtain ⟨a', rfl, ha'⟩ := exists_coords S g' j hu'
    obtain ⟨β, γ, hβγ⟩ := exists_coords_Mof S g g' hm
    have htt : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (th_ne_zero S), map_one]
    have hy' : y = ∑ i, ((a i + (β i : E)) • g i + a' i • g' i +
        (γ i : E) • (algebraMap F E S.th⁻¹ • (g' i - g i))) := by
      simp only [add_smul, Finset.sum_add_distrib]
      rw [eq_add_of_sub_eq hβγ]
      abel
    unfold Frames.lev
    apply Nat.sInf_le
    refine ⟨fun i => algebraMap F E S.th * a i + algebraMap F E S.th * (β i : E) - (γ i : E),
      fun i => algebraMap F E S.th * a' i + (γ i : E), ?_, fun i hi => ?_⟩
    · rw [hy', Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_add, smul_comm (algebraMap F E S.th) (γ i : E),
        smul_smul (algebraMap F E S.th) (algebraMap F E S.th⁻¹), htt, one_smul]
      module
    · unfold Frames.RR
      refine ⟨?_, (β i : E), (β i).2, ?_⟩
      · dsimp only
        rw [ha' i hi, mul_zero, zero_add]
        exact (γ i).2
      · dsimp only
        rw [ha i hi, ha' i hi]
        ring

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g g' : Fin (r + 1) → S.V), ∀ y ∈ S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1), ∀ j : ℕ, S.lev g g' (algebraMap F E S.th • y) ≤ j ↔ ∃ y₁ ∈ S.spanTo g j ⊔ S.spanTo g' j, y - y₁ ∈ S.Mof g g' := by
  intro F _ _ _ _ _ E _ _ _ L r k S g g' y hy j
  exact lev_le_iff S g g' y hy j

end GlobalTheory.FrameLevel
end
end
