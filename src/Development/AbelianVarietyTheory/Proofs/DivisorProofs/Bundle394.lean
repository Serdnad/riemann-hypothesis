module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle330
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle386
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle327
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle335
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
theorem _root_.GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT : ∀ (R : Subring ℂ) (N w : ℕ)
    (f : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = _root_.ReciprocityTheory.ChartRestriction.L1.DD τ ^ w * P.eval (_root_.ReciprocityTheory.ChartRestriction.L1.jT τ) := by
  intro R N w f hN hinv hq
  obtain ⟨a, ha, haR⟩ := hq
  have hmf : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (12 * w) f := _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N _ f a hN hinv ha
  have h1 : _root_.GlobalTheory.QFam.HasQ 1 f fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) := by
    rw [_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
    obtain ⟨g, hg⟩ := hmf
    have hgf : (⇑g : ℍ → ℂ) = f := funext hg
    have h := _root_.GlobalTheory.hasQExpansion_modularForm g
    rw [hgf] at h
    simpa using h
  have hN' := _root_.GlobalTheory.QFam.hasQ_mul_spread 1 N f _ one_pos hN h1
  rw [one_mul] at hN'
  have heq := _root_.GlobalTheory.QFam.HasQ.coeff_unique hN ha hN'
  have hcoeff : _root_.ReciprocityTheory.ChartRestriction.L1.CoeffIn R (UpperHalfPlane.qExpansion 1 f) := by
    intro m
    have h := haR (N * m)
    rw [heq] at h
    simpa [_root_.GlobalTheory.QFam.spread, Nat.mul_div_cancel_left _ hN] using h
  obtain ⟨P, hPR, -, hP⟩ := _root_.ReciprocityTheory.ChartRestriction.L1.qPrin R w f hmf hcoeff
  exact ⟨P, hPR, hP⟩

end GlobalTheory.QFam
end

section

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem delta_topPart_eq_zero {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E)
    (c : Finset ι → E) (k : ℕ) (hc : Dtot d c = 0) (hk : ∀ s, k < s.card → c s = 0) :
    delta (fun s => if s.card = k then c s else 0) = 0 := by
  funext t
  by_cases ht : t.card = k + 1
  · have h1 : delta c t = 0 := by
      have h := congrFun hc t
      simpa [Dtot, hk t (by omega)] using h
    rw [Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : (t.erase i).card = k := by rw [Finset.card_erase_of_mem hi]; omega
    simp only [this, if_true]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have h0 := Finset.card_erase_add_one hi
    have : (t.erase i).card ≠ k := by omega
    simp only [this, if_false, smul_zero]

theorem hypZero_of_cechZero : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → ∀ n, (∀ q b, q + b = n → CechZero (T q) b) → HypZero d T n := by
  intro ι _ E _ d T hdd hmono hdT n hC
  obtain ⟨-, -, hadd, hsub, -, hDD⟩ := GlobalTheory.T.cech_and_total_differential_additive_square_zero (ι := ι) d
  have key : ∀ k, k ≤ n + 1 → ∀ c, InTot T (n + 1) c → Dtot d c = 0 →
      (∀ s, k < s.card → c s = 0) → ∃ y, InTot T n y ∧ Dtot d y = c := by
    intro k
    induction k with
    | zero =>
      intro _ c hc _ h0
      refine ⟨0, ⟨rfl, fun q s _ => (T q s).zero_mem, fun _ _ => rfl⟩, ?_⟩
      funext s
      have hs : c s = 0 := by
        rcases Nat.eq_zero_or_pos s.card with h | h
        · rw [Finset.card_eq_zero.1 h]; exact hc.1
        · exact h0 s h
      simp [Dtot, delta, hs]
    | succ b ih =>
      intro hb c hc hD h0
      obtain ⟨q, hq⟩ : ∃ q, q + b = n := ⟨n - b, by omega⟩
      have hin : InCech (T q) (b + 1) (fun s => if s.card = b + 1 then c s else 0) := by
        refine ⟨by simp, fun s => ?_, fun s hs => by simp [hs]⟩
        by_cases hs : s.card = b + 1
        · simp only [hs, if_true]
          exact hc.2.1 q s (by omega)
        · simp only [hs, if_false]
          exact (T q s).zero_mem
      obtain ⟨y, hy, hyc⟩ := hC q b hq _ hin (delta_topPart_eq_zero d c (b + 1) hD h0)
      have hyT : InTot T n y := by
        refine ⟨hy.1, fun q' s hs => ?_, fun s hs => hy.2.2 s (by omega)⟩
        by_cases h : s.card = b
        · obtain rfl : q' = q := by omega
          exact hy.2.1 s
        · rw [hy.2.2 s h]; exact (T q' s).zero_mem
      have hDy : InTot T (n + 1) (Dtot d y) := (GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials d T hmono n y hyT).2 hdT
      have h1 : InTot T (n + 1) (c - Dtot d y) := by
        refine ⟨?_, fun q' s hs => (T q' s).sub_mem (hc.2.1 q' s hs) (hDy.2.1 q' s hs),
          fun s hs => ?_⟩
        · rw [Pi.sub_apply, hc.1, hDy.1, sub_zero]
        · rw [Pi.sub_apply, hc.2.2 s hs, hDy.2.2 s hs, sub_zero]
      have h2 : Dtot d (c - Dtot d y) = 0 := by rw [hsub, hD, hDD hdd, sub_zero]
      have h3 : ∀ s, b < s.card → (c - Dtot d y) s = 0 := by
        intro s hs
        have hys : y s = 0 := hy.2.2 s (by omega)
        by_cases h : s.card = b + 1
        · simp [Dtot, hyc, hys, h]
        · simp [Dtot, hyc, hys, h, h0 s (by omega)]
      obtain ⟨z, hz, hzc⟩ := ih (by omega) _ h1 h2 h3
      refine ⟨z + y, ⟨?_, fun q' s hs => (T q' s).add_mem (hz.2.1 q' s hs) (hyT.2.1 q' s hs),
        fun s hs => ?_⟩, ?_⟩
      · rw [Pi.add_apply, hz.1, hyT.1, add_zero]
      · rw [Pi.add_apply, hz.2.2 s hs, hyT.2.2 s hs, add_zero]
      · rw [hadd, hzc, sub_add_cancel]
  intro c hc hD
  exact key (n + 1) le_rfl c hc hD hc.2.2

end GlobalTheory.DI
end

section

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem prodL_mem_forms_and_vanish {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    {ι : Type} [LinearOrder ι]
    (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι)
    (hf : ∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1)
    (hh : ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) :
    ∀ (vs : List V), (∀ w ∈ vs, w ∈ L) → ∀ t : Finset ι,
      (t ⊆ s → ∀ q, q + t.card = vs.length + 1 → prodL f h vs t ∈ forms (A : Set K) L q) ∧
      (vs.length + 1 < t.card → prodL f h vs t = 0) := by
  obtain ⟨hone, hmul, hsmul, -, -⟩ := GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono A L
  intro vs
  induction vs with
  | nil =>
    intro _ t
    simp only [prodL, List.foldr_nil, oneC, List.length_nil]
    refine ⟨fun _ q hq => ?_, fun ht => ?_⟩
    · split_ifs with h1t
      · have hq0 : q = 0 := by omega
        subst hq0
        exact hone
      · exact zero_mem _
    · rw [if_neg (by omega)]
  | cons w vs ih =>
    intro hvs t
    have hw : w ∈ L := hvs w (List.mem_cons_self ..)
    have hvs' : ∀ u ∈ vs, u ∈ L := fun u hu => hvs u (List.mem_cons_of_mem _ hu)
    have key : prodL f h (w :: vs) t = Lop f h w (prodL f h vs) t := rfl
    rw [key, List.length_cons]
    refine ⟨fun hts q hq => ?_, fun hlt => ?_⟩
    · simp only [Lop]
      by_cases ht : t.Nonempty
      · rw [dite_eq_left ht]
        have hm : t.min' ht ∈ s := hts (t.min'_mem ht)
        refine add_mem ?_ ?_
        · refine zsmul_mem ?_ _
          rcases q with _ | q
          · rw [(ih hvs' t).2 (by omega), mul_zero]
            exact zero_mem _
          · exact hmul q _ _ (hf _ hm w hw) ((ih hvs' t).1 hts q (by omega))
        · split_ifs with h2
          · have hm' : (t.erase (t.min' ht)).min' h2 ∈ s :=
              hts (Finset.mem_of_mem_erase ((t.erase _).min'_mem h2))
            have hcard : (t.erase (t.min' ht)).card = t.card - 1 :=
              Finset.card_erase_of_mem (t.min'_mem ht)
            have hpos : 0 < t.card := ht.card_pos
            exact hsmul q _ _ (hh _ hm _ hm' w hw)
              ((ih hvs' _).1 ((Finset.erase_subset _ _).trans hts) q (by omega))
          · exact zero_mem _
      · rw [dite_eq_right ht]
        exact zero_mem _
    · simp only [Lop]
      by_cases ht : t.Nonempty
      · rw [dite_eq_left ht]
        have hcard : (t.erase (t.min' ht)).card = t.card - 1 :=
          Finset.card_erase_of_mem (t.min'_mem ht)
        rw [(ih hvs' t).2 (by omega), mul_zero, smul_zero, zero_add]
        split_ifs with h2
        · rw [(ih hvs' _).2 (by omega), smul_zero]
        · rfl
      · rw [dite_eq_right ht]

theorem alt_mem_forms : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι),
    (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) →
    (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) →
    ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s →
      ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  intro K _ V _ _ ι _ f h A L s hf hh a v t hv hts q hq
  rw [alt, Finset.sum_apply]
  refine AddSubgroup.sum_mem _ fun σ _ => ?_
  rw [Pi.smul_apply]
  refine zsmul_mem ?_ _
  refine (prodL_mem_forms_and_vanish f h A L s hf hh _ ?_ t).1 hts q (by rw [List.length_ofFn]; exact hq)
  intro w hw
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
  exact hv _

end GlobalTheory.DI
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  first | (exact @GlobalTheory.Shin.BlocksTwist.blocks_twist) | (exact GlobalTheory.Shin.BlocksTwist.blocks_twist) | (intros; apply GlobalTheory.Shin.BlocksTwist.blocks_twist <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.deg_liftL_and_reg_pow : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → 0 < l → (∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2) → deg (liftL q l L) = deg L ∧ ∀ p ∈ liftL q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  first | (exact @GlobalTheory.Shin.liftL_deg_reg) | (exact GlobalTheory.Shin.liftL_deg_reg) | (intros; apply GlobalTheory.Shin.liftL_deg_reg  <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ), 0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * cB N x k) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * cP N x k) ∧ IsIntegral ℤ (12 * cG N k) := by
  first | exact @GlobalTheory.WpFam.isIntegral_coefficients | exact GlobalTheory.WpFam.isIntegral_coefficients | (intros; apply GlobalTheory.WpFam.isIntegral_coefficients <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.Mass

theorem gal_id (F : Type) [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem sum_comp_surj {G M : Type} [Group G] [Group M] [Fintype G] [Fintype M]
    (π : G →* M) (hs : Function.Surjective π) (g : M → ℂ) :
    ∑ h : G, g (π h) = ((Finset.univ.filter fun h : G => π h = 1).card : ℂ) * ∑ z : M, g z := by
  rw [← Finset.sum_fiberwise Finset.univ π (fun h => g (π h)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_congr rfl (fun h hh => by rw [(Finset.mem_filter.1 hh).2]), Finset.sum_const, nsmul_eq_mul,
    MonoidHom.card_fiber_eq_of_mem_range π (hs z) (hs 1)]

theorem aux (A B k N s : ℂ) (h : k * (A * B) ≠ 0) : A * B * ((k * (A * B))⁻¹ * (N * (k * s))) = N * s := by
  calc A * B * ((k * (A * B))⁻¹ * (N * (k * s))) = (k * (A * B)) * (k * (A * B))⁻¹ * (N * s) := by ring
    _ = N * s := by rw [mul_inv_cancel₀ h, one_mul]

theorem mass : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (S : F[X] → ℂ), (Nat.card (GL (Fin a) F) : ℂ) * (Nat.card (GL (Fin b) F) : ℂ) * ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) := by
  intro F _ _ a b n hn α β S
  obtain ⟨H, π, hH, hsurj, hπ, -, hchar⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have hcl : IsCl (chG S n) := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) a b n α β).2.2 S).2
  haveI : Fintype F := Fintype.ofFinite F
  set g : GL (Fin a) F × GL (Fin b) F → ℂ := fun z => α z.1 * β z.2 *
    star (S (Matrix.charpoly (z.1 : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (z.2 : Matrix (Fin b) (Fin b) F)))
    with hg
  have hT : ∀ y : GL (Fin n) F, ∑ x : GL (Fin n) F, (if InPar a (y⁻¹ * x * y) then
      α (tlG a (y⁻¹ * x * y)) * β (brG a b (y⁻¹ * x * y)) else 0) * star (chG S n x) = ∑ p : H, g (π p) := by
    intro y
    rw [Fintype.sum_equiv (MulAut.conj y⁻¹).toEquiv _
      (fun p => (if InPar a p then α (tlG a p) * β (brG a b p) else 0) * star (chG S n p))
      (fun x => by simp [MulAut.conj_apply, show ∀ x y, chG S n (y⁻¹ * x * y) = chG S n x from hcl])]
    have h1 : ∀ p : GL (Fin n) F, (if InPar a p then α (tlG a p) * β (brG a b p) else 0) * star (chG S n p)
        = if p ∈ H then α (tlG a p) * β (brG a b p) * star (chG S n p) else 0 := by
      intro p; rw [hH p]; split_ifs <;> simp
    simp only [h1]
    rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (· ∈ H)) (p := (· ∈ H)) (by simp)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hg]
    rw [← hchar p, hπ p]
    rfl
  have hL : ∑ᶠ x, hc a b α β n x * star (chG S n x) = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
      ∑ y : GL (Fin n) F, ∑ x : GL (Fin n) F, (if InPar a (y⁻¹ * x * y) then
      α (tlG a (y⁻¹ * x * y)) * β (brG a b (y⁻¹ * x * y)) else 0) * star (chG S n x) := by
    rw [finsum_eq_sum_of_fintype]
    simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, Finset.sum_mul]
  have hR : ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y * star (S (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) = ∑ z, g z := by
    simp only [finsum_eq_sum_of_fintype]
    rw [← Fintype.sum_prod_type']
  have hP : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card H :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hH x).symm))
  have hS := sum_comp_surj π hsurj g
  have hC := sum_comp_surj π hsurj (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_prod] at hC
  rw [hL, hR, hP]
  simp only [hT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hS]
  simp only [Nat.card_eq_fintype_card]
  have hne : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hC] at hne ⊢
  push_cast at hne ⊢
  exact aux _ _ _ _ _ hne

end GlobalTheory.Shin.Mass
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (b : ZMod N) (d : ℕ+), 1 ≤ e → (∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * ch N (((j : ℕ) : ZMod N) * b) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) ∧ ∑' m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ((-1) ^ (e + 1) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * ch N (-(((j : ℕ) : ZMod N) * b)) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) := by
  first | exact @GlobalTheory.WpFam.torsion_row_series | exact GlobalTheory.WpFam.torsion_row_series | (intros; apply GlobalTheory.WpFam.torsion_row_series <;> assumption)
end

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_isH_of_isFrob : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F F' : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → IsFrob p π F' →
    ∃ h, IsH p π F F' h := by
  intro K Kt _ _ p _ _ π F F' hL hF hF'
  have hex : ∀ z, ∃ w, F' z = F z + p * w := by
    intro z
    obtain ⟨w, hw⟩ := (hL.ker (F' z - F z)).1 (by rw [map_sub, hF, hF', sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have huniq : ∀ z w w', F' z = F z + p * w → F' z = F z + p * w' → π w = π w' := by
    intro z w w' h1 h2
    have h3 : (p : Kt) * (w - w') = 0 := by rw [mul_sub]; linear_combination h2 - h1
    have h4 := (hL.ann (w - w')).1 h3
    rw [map_sub] at h4
    exact sub_eq_zero.1 h4
  let g : Kt → K := fun z => π (Classical.choose (hex z))
  have hg : ∀ z w, F' z = F z + p * w → g z = π w := fun z w hw =>
    huniq z _ w (Classical.choose_spec (hex z)) hw
  have hgadd : ∀ z z', g (z + z') = g z + g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z + z') (w + w') (by rw [map_add (f := _), map_add (f := _), h1, h2]; ring), map_add (f := _)]
  have hgp : ∀ y, g (p * y) = 0 := by
    intro y
    obtain ⟨w, h1⟩ := hex y
    rw [hg (p * y) (p * w) (by rw [map_mul, map_mul, map_natCast, map_natCast, h1]; ring), map_mul,
      map_natCast, CharP.cast_eq_zero, zero_mul]
  have hgmul : ∀ z z', g (z * z') = π z' ^ p * g z + π z ^ p * g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z * z') (w * F z' + F z * w' + p * w * w')
      (by rw [map_mul, map_mul, h1, h2]; ring)]
    simp only [map_add (f := _), map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
    rw [hF z, hF z']
    ring
  have hwd : ∀ z z', π z = π z' → g z = g z' := by
    intro z z' hzz
    obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, hzz, sub_self])
    have : z = z' + p * y := by rw [← hy]; ring
    rw [this, hgadd, hgp, add_zero]
  let φ : K →+ K := AddMonoidHom.mk' (fun x => g (Function.surjInv hL.surj x)) (by
    intro a b
    show g _ = g _ + g _
    rw [← hgadd]
    apply hwd
    rw [map_add (f := _), Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])
  have hφ : ∀ z, φ (π z) = g z := by
    intro z
    show g _ = g _
    exact hwd _ _ (Function.surjInv_eq hL.surj _)
  obtain ⟨f, hfs, hfD⟩ := GlobalTheory.T.frobeniusDerivation_factors_through_kaehler (M := K) p φ (by
    intro a b
    obtain ⟨z, rfl⟩ := hL.surj a
    obtain ⟨z', rfl⟩ := hL.surj b
    rw [← map_mul, hφ, hφ, hφ, hgmul, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨f, fun c v => by rw [hfs, smul_eq_mul], fun z w hzw => ?_⟩
  rw [hfD, hφ, hg z w hzw]

end GlobalTheory.DI
end

section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

theorem _root_.GlobalTheory.T.equivalence_generated_torus_rel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 := by
  first | exact @GlobalTheory.UCls.torus_eqvGen_main | exact GlobalTheory.UCls.torus_eqvGen_main | (intros; apply GlobalTheory.UCls.torus_eqvGen_main <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.dbarEnergyOnCoverBalls_lt_top_of_smooth : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  first | exact @GlobalTheory.n1_lt_infty_of_isSSec | exact GlobalTheory.n1_lt_infty_of_isSSec | (intros; apply GlobalTheory.n1_lt_infty_of_isSSec <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.dense_nonvanishingSet_of_ne_zero_on_components : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (T : Set Y), A.IsSec Λ τ → (∀ y, ∃ P ∈ T, P ∈ connectedComponent y) → (∀ P ∈ T, τ (A.pick P) P ≠ 0) → Dense (nz A τ) := by
  first | exact @GlobalTheory.nz_dense_of_ne_zero_on_components | exact GlobalTheory.nz_dense_of_ne_zero_on_components | (intros; apply GlobalTheory.nz_dense_of_ne_zero_on_components <;> assumption)
end
