module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestRankLProved
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem exists_fd_Ljj (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∃ W : Submodule ℚ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]), FiniteDimensional ℚ_[p] W ∧
      ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
  obtain ⟨W, hfd, hsub, _⟩ := exists_fd_Ljj_with_finrank_bound p (r := r) G j jp
  exact ⟨W, hfd, hsub⟩

theorem bePhi_smul_left (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (c • u) v = c * bePhi p (r := r) G j jp u v := by
  unfold bePhi
  rw [map_smul, fockK_smul_left, mul_div_assoc]

theorem bePhi_sum_left (j : Fin G.T.t → ℕ) (jp : ℕ) {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (∑ i ∈ s, f i) v = ∑ i ∈ s, bePhi p (r := r) G j jp (f i) v := by
  unfold bePhi

  rw [map_sum, fockK_sum_left, Finset.sum_div]

theorem bePhi_smul_right (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp u (c • v) = c * bePhi p (r := r) G j jp u v := by
  unfold bePhi
  rw [fockK_smul_right, mul_div_assoc]

theorem gcL_bdd (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G j jp) ∧ (∀ i, y i ∈ Ljj p (r := r) G j jp) ∧
      ∀ i k, bePhi p (r := r) G j jp (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  classical
  obtain ⟨W, hW, hsub⟩ := exists_fd_Ljj p (r := r) G j jp
  refine ⟨Module.finrank ℚ_[p] W, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hp0 : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hli : LinearIndependent ℚ_[p] (fun i => (⟨x i, hsub _ (hx i)⟩ : W)) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : ∑ k ∈ s, g k • x k = 0 := by
      have := congrArg Subtype.val hs
      simpa using this
    have h1 := congrArg (fun u => bePhi p (r := r) G j jp u (y i)) h0
    simp only [bePhi_sum_left, bePhi_smul_left, hxy] at h1
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg hk, mul_zero]) (fun h => absurd hi h), if_pos rfl] at h1
    have h2 : bePhi p (r := r) G j jp 0 (y i) = 0 := by
      have := bePhi_smul_left p (r := r) G j jp 0 0 (y i)
      simpa using this
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_right hp0
  have := hli.fintype_card_le_finrank
  simpa using this

theorem xiMons_spec (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    (∀ v ∈ m.support, ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c) ∧ (∑ c, m (Formalism.GM.M.xiVar N r G.T.t c) = n) ∧
      (∑ v ∈ m.support, m v = n) := by
  classical
  unfold xiMons at hm
  rw [Finset.mem_image] at hm
  obtain ⟨e, he, rfl⟩ := hm
  have hsum := (CountingStatementReduction.mem_Ev e).1 he
  have happ : ∀ c, (∑ d : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t d) (e d)) (Formalism.GM.M.xiVar N r G.T.t c) = e c := by
    intro c
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj (r := r) G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  refine ⟨fun v hv => ?_, by simp only [happ]; exact hsum, ?_⟩
  · by_contra hne
    push Not at hne
    apply Finsupp.mem_support_iff.1 hv
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hne d h.symm
  · have : (∑ d : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t d) (e d)).sum (fun _ k => k) = ∑ c, e c := by
      rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
      exact Finset.sum_congr rfl fun d _ => Finsupp.sum_single_index rfl
    rw [← hsum, ← this]
    rfl

theorem card_xiMons_eq (n : ℕ) : (xiMons (r := r) G n).card = dXi r n := by
  classical
  unfold xiMons
  rw [Finset.card_image_of_injective]
  · rw [CountingStatementReduction.card_Ev]
    unfold dXi
    have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have e1 : r' + 1 + n - 1 = n + r' := by omega
    have e2 : n + (r' + 1) - 1 = n + r' := by omega
    rw [e1, e2, Nat.add_sub_cancel, Nat.choose_symm_add]
  · intro e e' h
    funext c
    have := congrArg (fun f : Formalism.GM.M.BVar N r G.T.t →₀ ℕ => f (Formalism.GM.M.xiVar N r G.T.t c)) h
    simp only [Finsupp.finsetSum_apply] at this
    rwa [Finset.sum_eq_single c (fun d _ hd => by rw [Finsupp.single_apply, if_neg (fun h => hd (xiVar_inj (r := r) G h))])
      (fun h => absurd (Finset.mem_univ c) h), Finset.sum_eq_single c
      (fun d _ hd => by rw [Finsupp.single_apply, if_neg (fun h => hd (xiVar_inj (r := r) G h))])
      (fun h => absurd (Finset.mem_univ c) h), Finsupp.single_eq_same, Finsupp.single_eq_same] at this

end Level

end Formalism.MainNotions.G.SymmetricFormBlocks

end
