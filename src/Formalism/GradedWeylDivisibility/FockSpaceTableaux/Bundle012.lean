module

public import Formalism.GradedWeylDivisibility.Bundle001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle006
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle008
public import Formalism.GradedWeylDivisibility.StatementD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem hwInClosed_of (h1 : HWLine) (h2 : RowDivClosedGraded) : HWInClosed := by
  intro r n hn ν hν M hMle hM hne
  obtain ⟨v, hvM, hv0, hkill⟩ := lhwin_exists_killed h2 M hM hne
  obtain ⟨c, hc⟩ := h1 ℚ r n hn ν hν v (hMle hvM) hkill
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc)
  have e : hw ℚ hn ν = c⁻¹ • v := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e]
  exact M.smul_mem _ hvM

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem peelDecomposition : PeelDecomp := by
  intro B _ r n l j hlj a0 ω g hg
  have key : ∀ m ∈ g.support, m (a0, l) + m (a0, j) = ω (a0, l) := by
    intro m hm
    have hw := hg (mem_support_iff.1 hm)
    have := lcpeel_weight_apply l j hlj m a0 l
    rw [hw] at this
    simpa using this.symm
  have hterm : ∀ k, X (a0, l) ^ k * X (a0, j) ^ (ω (a0, l) - k) * peel l j a0 k g =
      ∑ m ∈ g.support.filter (fun m => m (a0, l) = k), monomial m (AddMonoidAlgebra.coeff g m) := by
    intro k
    unfold peel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    have hkey := key m hm1
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul, one_mul, one_mul]
    refine congrArg (fun e => monomial e (AddMonoidAlgebra.coeff g m)) ?_
    ext ⟨b, t⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply, Prod.mk.injEq]
    rcases eq_or_ne b a0 with rfl | hb
    · rcases eq_or_ne t l with rfl | ht
      · simp only [hlj, hlj.symm, and_true, and_false, if_true, if_false]
        omega
      · rcases eq_or_ne t j with rfl | ht'
        · simp only [ht, Ne.symm ht, and_true, and_false, if_true, if_false]
          omega
        · simp [ht, ht', Ne.symm ht, Ne.symm ht']
    · simp [hb, Ne.symm hb]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hmaps : ∀ m ∈ g.support, (fun m : Fin r × Fin n →₀ ℕ => m (a0, l)) m ∈ Finset.range (ω (a0, l) + 1) := by
    intro m hm
    have := key m hm
    show m (a0, l) ∈ _
    rw [Finset.mem_range]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun m => monomial m (AddMonoidAlgebra.coeff g m))
  exact (hfib.trans (as_sum g).symm).symm

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerRatPos : FockQPos :=
  fun _ f g => ⟨lfockq_symm f g, fun hf => lfockq_self_pos f hf⟩

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem exists_tableau_of_sum_eq_lemma (hP : SSYTPeel) (r n : ℕ) :
    ∀ (N : ℕ) (ν : Fin n → ℕ) (m : Fin r × Fin n →₀ ℕ), ∑ t, ν t = N →
      (∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) → Interlaced m →
      ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
        shapeDeg sz = ν ∧ (∀ k, StrictMono (I k)) ∧ bidetExp sz hsz I = m := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih ν m hN hcol hint_r
  by_cases hm : m = 0
  · subst hm
    have hν : ν = 0 := by
      funext t
      rw [← hcol t]
      simp
    subst hν
    refine ⟨0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, ?_, fun k => k.elim0, ?_⟩
    · funext t
      simp [shapeDeg]
    · simp [bidetExp]
  · obtain ⟨h, hh, c, hc, hν, hle, hint', hcol'⟩ := hP r n ν m hcol hint_r hm
    obtain ⟨⟨a0, t0⟩, hne⟩ : ∃ x, m x ≠ 0 := by
      by_contra H
      push_neg at H
      exact hm (Finsupp.ext H)
    have hpos : 0 < ν t0 := by
      rw [← hcol t0]
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero hne)
        (Finset.single_le_sum (f := fun a => m (a, t0)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a0))
    have hlt : ∑ t, (ν t - if t.val < h then 1 else 0) < N := by
      rw [← hN]
      apply Finset.sum_lt_sum
      · intro t _
        exact Nat.sub_le _ _
      · refine ⟨t0, Finset.mem_univ _, ?_⟩
        rw [if_pos ((hν t0).2 hpos)]
        omega
    obtain ⟨K, sz, hsz, I, hshape, hI, hexp⟩ :=
      ih _ hlt (fun t => ν t - if t.val < h then 1 else 0) (m - colExp c hh) rfl hcol' hint'
    refine ⟨K + 1, Fin.cons h sz, lcssyt_consSz hh sz hsz, lcssyt_consI sz c I, ?_,
      lcssyt_consI_strictMono sz c I hc hI, ?_⟩
    · funext t
      rw [lcssyt_shapeDeg_cons, congrFun hshape t]
      by_cases ht : t.val < h
      · have h1 := (hν t).1 ht
        simp only [if_pos ht]
        omega
      · simp only [if_neg ht]
        omega
    · rw [lcssyt_bidetExp_cons hh c sz hsz I, hexp]
      exact add_tsub_cancel_of_le hle

theorem sSYTExists_of (hP : SSYTPeel) : SSYTExists :=
  fun r n ν m hcol hint_r => exists_tableau_of_sum_eq_lemma hP r n _ ν m rfl hcol hint_r

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem nablaLBasis_of (h : RowActMul) : NablaLBasis := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g hg
  have hid : ∀ x : MvPolynomial (Fin k × Fin n) K, rowAct K (1 : Matrix (Fin k) (Fin k) K) x = x := by
    intro x
    have e1 : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [e1]
    rfl
  have hinvA : ∀ A : Matrix (Fin k) (Fin k) K, IsUnit A.det → ∀ x : MvPolynomial (Fin k × Fin n) K,
      rowAct K A (rowAct K A⁻¹ x) = x ∧ rowAct K A⁻¹ (rowAct K A x) = x := by
    intro A hA x
    have e1 := congrArg (fun F => F x) (h K k n A A⁻¹)
    have e2 := congrArg (fun F => F x) (h K k n A⁻¹ A)
    simp only [AlgHom.comp_apply] at e1 e2
    rw [Matrix.nonsing_inv_mul A hA] at e1
    rw [Matrix.mul_nonsing_inv A hA] at e2
    exact ⟨e1.trans (hid x), e2.trans (hid x)⟩
  have hφinj : Function.Injective (map (algebraMap R K) : MvPolynomial (Fin k × Fin n) R → _) :=
    MvPolynomial.map_injective _ hinj
  let L : MvPolynomial (Fin k × Fin n) R →ₗ[R] MvPolynomial (Fin k × Fin n) K :=
    ((rowAct K g⁻¹).toLinearMap.restrictScalars R).comp (mapAlgHom (Algebra.ofId R K)).toLinearMap
  have hL : ∀ p, L p = rowAct K g⁻¹ (map (algebraMap R K) p) := fun p => rfl
  have hLinj : Function.Injective L := by
    intro p q hpq
    rw [hL, hL] at hpq
    have e := congrArg (rowAct K g) hpq
    rw [(hinvA g hg _).1, (hinvA g hg _).1] at e
    exact hφinj e
  refine ⟨?_, ?_⟩
  · exact hb.1.map' L (LinearMap.ker_eq_bot.mpr hLinj)
  · have e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = L '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, hb.2.1]
    ext F
    unfold nablaL
    rw [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      show map (algebraMap R K) p = rowAct K g (L p)
      rw [hL, (hinvA g hg _).1]
    · rintro ⟨p, hp, hpF⟩
      refine ⟨p, hp, ?_⟩
      have e : map (algebraMap R K) p = rowAct K g F := hpF
      rw [hL, e, (hinvA g hg _).2]

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem nabla_twist_mem : NablaLTwMem := by
  intro R K _ _ _ m lam g hg F
  have hd : g.det ≠ 0 := hg.ne_zero
  unfold nablaLTw nablaL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨G, hG, rfl⟩
    rw [Submodule.mem_comap] at hG
    change g.det ^ lam (Fin.last m) • rowAct K g (g.det ^ (-(lam (Fin.last m))) • G) ∈ _
    rw [map_smul, smul_smul, ← zpow_add₀ hd, add_neg_cancel, zpow_zero, one_smul]
    exact hG
  · intro hF
    refine ⟨g.det ^ (lam (Fin.last m)) • F, ?_, ?_⟩
    · rw [Submodule.mem_comap]
      change rowAct K g (g.det ^ (lam (Fin.last m)) • F) ∈ _
      rw [map_smul]
      exact hF
    · change g.det ^ (-(lam (Fin.last m))) • g.det ^ (lam (Fin.last m)) • F = F
      rw [smul_smul, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_smul]

end Formalism.GradedWeylDivisibility
end

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_diagonal_weight : RowActDiagWeight := by
  intro R _ k n t μ f hf
  have hX : (rowAct R (n := n) (Matrix.diagonal t)) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
    unfold rowAct
    congr 1
    funext v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  have hwt : ∀ (d : Fin k × Fin n →₀ ℕ) (a : Fin k), Finsupp.weight (rowW k n) d a = ∑ s, d (a, s) := by
    intro d a
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_prod_type]
    simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (rowW k n) d = μ := hf (mem_support_iff.mp hd)
  have hp : (d.prod fun v e => t v.1 ^ e) = ∏ a, t a ^ μ a := by
    rw [← hw, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hwt]
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hX, aeval_monomial, ← hp, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow, MvPolynomial.algebraMap_eq]
  ring

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem ldtensor_blockAct_comp (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) :
    (blockAct K (n := n) g).comp (blockEmb K (k := k) (n := n) s) =
      (blockEmb K s).comp (rowAct K (g s)) := by
  apply MvPolynomial.algHom_ext
  intro v

  simp [blockEmb, blockAct, rowAct, map_sum, rename_C]

theorem ldtensor_blockAct_blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) (F : MvPolynomial (Fin k × Fin n) K) :
    blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) := by
  exact AlgHom.congr_fun (ldtensor_blockAct_comp K g s) F

theorem block_action_tensor : BlockActTensor := by
  intro R K _ _ _ S _ k n g
  refine ⟨fun s F => ldtensor_blockAct_blockEmb K g s F, ?_⟩
  intro M M' hMM' P hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => rowAct K (g s) (F s), fun s => hMM' s (F s) (hF s), ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl (fun s _ => ldtensor_blockAct_blockEmb K g s (F s))
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.GradedWeylDivisibility
end
end
