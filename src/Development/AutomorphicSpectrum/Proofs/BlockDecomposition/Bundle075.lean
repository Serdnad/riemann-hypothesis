module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle051
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle042
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle043
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Algebra.Group.Units.Basic

@[expose] public section

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pq_lift : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (T : Type) [CommRing T]
    (T₁ : Type) [CommRing T₁] (i : S →+* T) (I : Ideal S) (φ : S →+* T₁),
    PQ p i I → Pf p T₁ → (∀ x ∈ I, φ x = 0) → ∃! ψ : T →+* T₁, ψ.comp i = φ := by
  intro p _ S _ T _ T₁ _ i I φ hPQ hPf hI
  obtain ⟨-, hred, hroot, hinj, -⟩ := pf_facts p T₁ hPf
  have hcharT : (p : T) = 0 := hPQ.pf.char
  have hcharT₁ : (p : T₁) = 0 := hPf.char
  have hA : ∀ a b : S, i a = i b → φ a = φ b := by
    intro a b hab
    obtain ⟨j, hj⟩ := (hPQ.ker (a - b)).mp (by rw [map_sub, hab, sub_self])
    have h0 := hI _ hj
    rw [map_pow, map_sub] at h0
    exact sub_eq_zero.mp (hred _ _ h0)
  have hfrobT : ∀ (k : ℕ) (u v : T), (u + v) ^ p ^ k = u ^ p ^ k + v ^ p ^ k := by
    intro k u v
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hcharT k
    rw [← hF, ← hF, ← hF, map_add (f := _)]
  have hfrobT₁ : ∀ (k : ℕ) (u v : T₁), (u + v) ^ p ^ k = u ^ p ^ k + v ^ p ^ k := by
    intro k u v
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T₁ hcharT₁ k
    rw [← hF, ← hF, ← hF, map_add (f := _)]
  let Rel : T → T₁ → Prop := fun y z => ∃ (k : ℕ) (x : S), y ^ p ^ k = i x ∧ z ^ p ^ k = φ x
  have hex : ∀ y, ∃ z, Rel y z := by
    intro y
    obtain ⟨k, x, hx⟩ := hPQ.pow y
    obtain ⟨z, hz⟩ := hroot k (φ x)
    exact ⟨z, k, x, hx, hz⟩
  have hfun : ∀ y z z', Rel y z → Rel y z' → z = z' := by
    rintro y z z' ⟨k, x, hyx, hzx⟩ ⟨m, x', hyx', hzx'⟩
    have hi : i (x ^ p ^ m) = i (x' ^ p ^ k) := by
      rw [map_pow, map_pow, ← hyx, ← hyx', ← pow_mul, ← pow_mul, mul_comm]
    have hφ := hA _ _ hi
    rw [map_pow, map_pow, ← hzx, ← hzx', ← pow_mul, ← pow_mul, mul_comm, ← pow_add] at hφ
    exact hinj _ _ _ hφ
  choose ψf hψf using hex
  have hRelψ : ∀ y z, Rel y z → ψf y = z := fun y z h => hfun y _ _ (hψf y) h
  have hadd : ∀ y₁ y₂, ψf (y₁ + y₂) = ψf y₁ + ψf y₂ := by
    intro y₁ y₂
    apply hRelψ
    obtain ⟨k₁, x₁, hy₁, hz₁⟩ := hψf y₁
    obtain ⟨k₂, x₂, hy₂, hz₂⟩ := hψf y₂
    refine ⟨k₁ + k₂, x₁ ^ p ^ k₂ + x₂ ^ p ^ k₁, ?_, ?_⟩
    · rw [hfrobT, map_add (f := _), map_pow, map_pow, ← hy₁, ← hy₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
    · rw [hfrobT₁, map_add (f := _), map_pow, map_pow, ← hz₁, ← hz₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
  have hmul : ∀ y₁ y₂, ψf (y₁ * y₂) = ψf y₁ * ψf y₂ := by
    intro y₁ y₂
    apply hRelψ
    obtain ⟨k₁, x₁, hy₁, hz₁⟩ := hψf y₁
    obtain ⟨k₂, x₂, hy₂, hz₂⟩ := hψf y₂
    refine ⟨k₁ + k₂, x₁ ^ p ^ k₂ * x₂ ^ p ^ k₁, ?_, ?_⟩
    · rw [mul_pow, map_mul, map_pow, map_pow, ← hy₁, ← hy₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
    · rw [mul_pow, map_mul, map_pow, map_pow, ← hz₁, ← hz₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
  have h1 : ψf 1 = 1 := hRelψ 1 1 ⟨0, 1, by simp, by simp⟩
  have h0 : ψf 0 = 0 := hRelψ 0 0 ⟨0, 0, by simp, by simp⟩
  let ψ : T →+* T₁ :=
    { toFun := ψf, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }
  refine ⟨ψ, ?_, ?_⟩
  · ext s
    show ψf (i s) = φ s
    exact hRelψ (i s) (φ s) ⟨0, s, by simp, by simp⟩
  · intro ψ' hψ'
    ext y
    show ψ' y = ψf y
    obtain ⟨k, x, hx⟩ := hPQ.pow y
    refine (hRelψ y (ψ' y) ⟨k, x, hx, ?_⟩).symm
    rw [← map_pow, hx, ← RingHom.comp_apply, hψ']

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegOrder

variable {T : Type u}

theorem interleave_left_nil (b : List T) : Interleave b [] b := by
  induction b with
  | nil => exact Interleave.nil
  | cons a b ih => exact Interleave.left ih

theorem interleave_right_nil (b : List T) : Interleave [] b b := by
  induction b with
  | nil => exact Interleave.nil
  | cons a b ih => exact Interleave.right ih

theorem Interleave.append_left {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave (u ++ b) v (w ++ b) := by
  induction h with
  | nil => exact interleave_left_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih

theorem Interleave.append_right {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave u (v ++ b) (w ++ b) := by
  induction h with
  | nil => exact interleave_right_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih

theorem wt_cons (s : T → T) (a : ASeg T) (L : List (ASeg T)) :
    wt s (a :: L) = wt s L ++ ASeg.dec s a := by
  simp [wt]

theorem exists_sublists_interleave (s : T → T) (L : List (ASeg T)) :
    ∀ m n : Multiset (ASeg T), (L : Multiset (ASeg T)) = m + n →
      ∃ L₁ L₂ : List (ASeg T), L₁.Sublist L ∧ L₂.Sublist L ∧
        (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
        Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  classical
  induction L with
  | nil =>
    intro m n h
    have h0 : m = 0 ∧ n = 0 := add_eq_zero.1 (by simpa using h.symm)
    refine ⟨[], [], List.Sublist.refl _, List.Sublist.refl _, ?_, ?_, Zc.Comb.Interleave.nil⟩
    · simp [h0.1]
    · simp [h0.2]
  | cons a L ih =>
    intro m n h
    have ha : a ∈ m + n := by
      rw [← h]
      simp
    rcases Multiset.mem_add.1 ha with ha | ha
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m.erase a + n := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.cons_add, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih (m.erase a) n hL
      refine ⟨a :: L₁, L₂, List.Sublist.cons₂ a h₁, List.Sublist.cons a h₂, ?_, e₂, ?_⟩
      · rw [← Multiset.cons_coe, e₁, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_left hI _
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m + n.erase a := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.add_cons, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih m (n.erase a) hL
      refine ⟨L₁, a :: L₂, List.Sublist.cons a h₁, List.Sublist.cons₂ a h₂, e₁, ?_, ?_⟩
      · rw [← Multiset.cons_coe, e₂, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_right hI _

theorem exists_common_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m n : Multiset (ASeg T), ∃ L₁ L₂ L : List (ASeg T),
      (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
      (L : Multiset (ASeg T)) = m + n ∧ AOrdered s L₁ ∧ AOrdered s L₂ ∧ AOrdered s L ∧
      Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  intro T s hinj hs m n
  obtain ⟨L, hL, hord⟩ := exists_ordered_form s hinj hs (m + n)
  obtain ⟨L₁, L₂, h₁, h₂, c₁, c₂, hi⟩ := exists_sublists_interleave s L m n hL
  exact ⟨L₁, L₂, L, c₁, c₂, hL, List.Pairwise.sublist h₁ hord, List.Pairwise.sublist h₂ hord,
    hord, hi⟩

end GlobalTheory.CompanionTheory.SegOrder
end

section

open Zc.Comb
universe u

theorem _root_.GlobalTheory.T.shuffle_weight_square_length_lt : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L : List (ASeg T)) (n : Multiset (ASeg T)), AOrdered s L → InSh s n (wt s L) → n ≠ (L : Multiset (ASeg T)) → sqLen n < sqLen (L : Multiset (ASeg T)) := by
  first | exact @GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh | exact GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh | (intros; apply GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.multiplicativity_infinite_places : DetMono → MulI := by
  first | exact @GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | exact GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.multiplicativity_finite_places : MulF := by
  first | exact @GlobalTheory.CompanionTheory.WedgeMinor.mulF | exact GlobalTheory.CompanionTheory.WedgeMinor.mulF | (intros; apply GlobalTheory.CompanionTheory.WedgeMinor.mulF <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.pairing_bound_finite_places : MulF → PairF := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF | exact GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF | (intros; apply GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF <;> assumption)
end

section

open scoped Classical
namespace PositivityTheory.Rg.BcB.F

theorem _root_.GlobalTheory.T.regularized_exponential_sum : PositivityTheory.Rg.BcB.F.ExpSum := by
  first | exact @GlobalTheory.CompanionTheory.ExpSums.expSum_holds | exact GlobalTheory.CompanionTheory.ExpSums.expSum_holds | (intros; apply GlobalTheory.CompanionTheory.ExpSums.expSum_holds <;> assumption)
end F
end BcB
end Rg
end PositivityTheory
end

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KerPoint

theorem support_cv_adj_cv (hKB : KerBasic) (hCv : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ) (hψ : Tst ψ)
    (N : Set X.G) (hNc : IsCompact N) (hN : tsupport ψ ⊆ N) :
    Function.support (cv X.μ (adj ψ) (cv X.μ φ ψ)) ⊆ N⁻¹ * (tsupport φ * N) := by
  have hadj : Tst (adj ψ) := (hKB X ψ hψ).2.2.2.1
  have hc := hCv X φ ψ hφ hψ
  have hcc := hCv X (adj ψ) (cv X.μ φ ψ) hadj hc.1
  refine hcc.2.1.trans ?_
  have hs1 : tsupport (adj ψ) ⊆ N⁻¹ := by
    refine closure_minimal ?_ hNc.inv.isClosed
    intro z hz
    have hz' : ψ z⁻¹ ≠ 0 := by
      intro h0
      apply hz
      simp [adj, h0]
    exact Set.mem_inv.2 (hN (subset_tsupport _ hz'))
  have hs2 : tsupport (cv X.μ φ ψ) ⊆ tsupport φ * N :=
    closure_minimal (hc.2.1.trans (Set.mul_subset_mul_left hN)) (hφ.2.isCompact.mul hNc).isClosed
  exact Set.mul_subset_mul hs1 hs2

theorem inner_map_sub_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : H →L[ℂ] H)
    (a b k₁ k₂ : H) (δ : ℝ) (ha : ‖a - k₁‖ ≤ δ) (hb : ‖b - k₂‖ ≤ δ) :
    ‖inner ℂ a (U b) - inner ℂ k₁ (U k₂)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) + ‖k₁‖ * ‖U‖ * δ := by
  have e : inner ℂ a (U b) - inner ℂ k₁ (U k₂) = inner ℂ (a - k₁) (U b) + inner ℂ k₁ (U (b - k₂)) := by
    simp only [inner_sub_left, inner_sub_right, map_sub]
    ring
  have hbn : ‖b‖ ≤ ‖k₂‖ + δ := by
    have := norm_add_le (b - k₂) k₂
    rw [sub_add_cancel] at this
    linarith
  have hU : 0 ≤ ‖U‖ := norm_nonneg _
  have t1 : ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) := by
    calc ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖a - k₁‖ * ‖U b‖ := norm_inner_le_norm _ _
      _ ≤ δ * (‖U‖ * (‖k₂‖ + δ)) := by
          have h2 : ‖U b‖ ≤ ‖U‖ * (‖k₂‖ + δ) :=
            (U.le_opNorm b).trans (mul_le_mul_of_nonneg_left hbn hU)
          exact mul_le_mul ha h2 (norm_nonneg _) ((norm_nonneg _).trans ha)
      _ = ‖U‖ * δ * (‖k₂‖ + δ) := by ring
  have t2 : ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U‖ * δ := by
    calc ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U (b - k₂)‖ := norm_inner_le_norm _ _
      _ ≤ ‖k₁‖ * (‖U‖ * δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb hU)
      _ = ‖k₁‖ * ‖U‖ * δ := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

theorem eq_zero_of_le_small {D C : ℝ} (hC : 0 ≤ C) (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → D ≤ δ * C) : D ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < min 1 (ε / (C + 1)) := lt_min one_pos (div_pos hε hC1)
  have h1 := h _ hδ (min_le_left _ _)
  have h2 : min 1 (ε / (C + 1)) * C ≤ ε := by
    calc min 1 (ε / (C + 1)) * C ≤ ε / (C + 1) * (C + 1) :=
          mul_le_mul (min_le_right _ _) (by linarith) hC (div_pos hε hC1).le
      _ = ε := by field_simp
  linarith

theorem ptEq_of : KerBasic → CvTest → OpAdj → ColOp → BumpEx → ApproxU → KerClose → VecLim → PtEq := by
  intro hKB hCv hAdj hCol hBump hAU hKC hVL X ι _ Φ₁ Φ₂ Φ T₁ T₂ U h1 h2 h hT1 hT2 hT x y i j k₁ k₂ hk1 hk2
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hΩ : IsCompact (N⁻¹ * (tsupport (Φ i j) * N)) := hNc.inv.mul ((h i j).2.isCompact.mul hNc)
  obtain ⟨M, hM0, hM⟩ := hKC X _ x y hΩ
  have hadj1 : ∀ a b, Tst ((fun i j => adj (Φ₁ j i)) a b : X.G → ℂ) :=
    fun a b => (hKB X _ (h1 b a)).2.2.2.1
  have hTadj := hAdj X ι Φ₁ T₁ h1 hT1
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖ker X.Γ (Φ i j) x y - inner ℂ k₁ (U k₂)‖ ≤
      δ * (M + ‖U‖ * (‖k₂‖ + 1) + ‖k₁‖ * ‖U‖) := by
    intro δ hδ hδ1
    obtain ⟨W₁, hW₁, hL₁⟩ := hVL X ι (fun i j => adj (Φ₁ j i)) (ContinuousLinearMap.adjoint T₁) x i k₁ δ hadj1 hTadj hk1 hδ
    obtain ⟨W₂, hW₂, hL₂⟩ := hVL X ι Φ₂ T₂ y j k₂ δ h2 hT2 hk2 hδ
    obtain ⟨W₃, hW₃, hL₃⟩ := hAU X (Φ i j) δ (h i j) hδ
    obtain ⟨ψ, hψ, hsub⟩ := hBump X (N ∩ W₁ ∩ W₂ ∩ W₃)
      (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hN1 hW₁) hW₂) hW₃)
    have sN : tsupport ψ ⊆ N := fun z hz => (hsub hz).1.1.1
    have s1 : tsupport ψ ⊆ W₁ := fun z hz => (hsub hz).1.1.2
    have s2 : tsupport ψ ⊆ W₂ := fun z hz => (hsub hz).1.2
    have s3 : tsupport ψ ⊆ W₃ := fun z hz => (hsub hz).2
    have hc := hCol X ι ψ hψ.1
    obtain ⟨v, hv⟩ := hc.1 x i
    obtain ⟨u, hu⟩ := hc.1 y j
    have e1 : inner ℂ v ((T₁ * U * T₂) u) = ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y :=
      (hc.2 Φ (T₁ * U * T₂) h hT y j u hu).2 x i v hv
    have e2 : inner ℂ v ((T₁ * U * T₂) u) = inner ℂ (ContinuousLinearMap.adjoint T₁ v) (U (T₂ u)) := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl
    have b1 := hL₁ ψ hψ s1 v hv
    have b2 := hL₂ ψ hψ s2 u hu
    have b3 := inner_map_sub_le U _ _ k₁ k₂ δ b1 b2
    have b4 := hM (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) (Φ i j) δ
      (support_cv_adj_cv hKB hCv X _ ψ (h i j) hψ.1 N hNc sN)
      (by
        intro z hz
        refine ⟨1⁻¹, Set.inv_mem_inv.2 h1N, z * 1, ⟨z, subset_tsupport _ hz, 1, h1N, rfl⟩, by simp⟩)
      (fun z => (hL₃ ψ hψ s3 z).2)
    have hsplit : ker X.Γ (Φ i j) x y - inner ℂ k₁ (U k₂) =
        (inner ℂ (ContinuousLinearMap.adjoint T₁ v) (U (T₂ u)) - inner ℂ k₁ (U k₂)) -
          (ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y - ker X.Γ (Φ i j) x y) := by
      rw [← e2, e1]
      ring
    have hU : 0 ≤ ‖U‖ := norm_nonneg _
    have hk : 0 ≤ ‖k₂‖ := norm_nonneg _
    have hle : ‖U‖ * δ * (‖k₂‖ + δ) ≤ ‖U‖ * δ * (‖k₂‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hU hδ.le)
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    nlinarith [b3, b4, hle]
  have hC : 0 ≤ M + ‖U‖ * (‖k₂‖ + 1) + ‖k₁‖ * ‖U‖ := by positivity
  have := eq_zero_of_le_small hC key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end GlobalTheory.CompanionTheory.KerPoint

end
end

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem exists_delta (c : ℝ≥0∞) (hc : c ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ^ 2 * c ≤ ENNReal.ofReal ε ^ 2 := by
  have hpos : 0 < Real.sqrt (c.toReal + 1) := Real.sqrt_pos.2 (by positivity)
  refine ⟨ε / Real.sqrt (c.toReal + 1), div_pos hε hpos, ?_⟩
  have hδ : 0 ≤ ε / Real.sqrt (c.toReal + 1) := (div_pos hε hpos).le
  rw [← ENNReal.ofReal_pow hδ, ← ENNReal.ofReal_pow hε.le]
  have hct : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
  calc ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * c
      = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * ENNReal.ofReal c.toReal := by
        rw [← hct]
    _ = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2 * c.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (ε ^ 2) := ?_
  apply ENNReal.ofReal_le_ofReal
  have hsq : Real.sqrt (c.toReal + 1) ^ 2 = c.toReal + 1 := Real.sq_sqrt (by positivity)
  rw [div_pow, hsq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : 0 ≤ ε ^ 2 := by positivity
  nlinarith

theorem vecLim_of (hCnt : CntBasic) (hCv : CvTest) (hCol : ColOp) (hA : ApproxU) (hVC : VecClose) :
    VecLim := by
  intro X ι _ Φ T y j k ε hΦ hT hk hε
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  set Ω₀ : Set X.G := ⋃ l, tsupport (Φ l j) with hΩ₀
  have hΩ₀c : IsCompact Ω₀ := isCompact_iUnion fun l => (hΦ l j).2.isCompact
  set Ω : Set X.G := Ω₀ * N with hΩ
  have hΩc : IsCompact Ω := hΩ₀c.mul hNc
  set c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y) with hc
  have hctop : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ ?_)
    · exact hΩc.inv.measure_lt_top.ne
    · exact (hCnt X).1 _ (hΩc.inv.mul hΩc) y
  obtain ⟨δ, hδ, hδc⟩ := exists_delta c hctop ε hε
  choose Wl hWl hWlP using fun l => hA X (Φ l j) δ (hΦ l j) hδ
  refine ⟨N ∩ ⋂ l, Wl l, Filter.inter_mem hN1 (Filter.iInter_mem.2 hWl), ?_⟩
  intro ψ hψ hsupp u hu
  have hsN : tsupport ψ ⊆ N := hsupp.trans Set.inter_subset_left
  have hsl : ∀ l, tsupport ψ ⊆ Wl l := fun l =>
    hsupp.trans (Set.inter_subset_right.trans (Set.iInter_subset _ l))
  have hvec : X.IsVec (fun l j => cv X.μ (Φ l j) ψ) y j (T u) := fun l =>
    (((hCol X ι ψ hψ.1).2 Φ T hΦ hT y j u hu).1 l)
  have hfin := hVC X ι (fun l j => cv X.μ (Φ l j) ψ) Φ Ω δ y j (T u) k hΩc (fun l => by
    have hcv := hCv X (Φ l j) ψ (hΦ l j) hψ.1
    refine ⟨hcv.1, hΦ l j, ?_, ?_, fun z => ((hWlP l ψ hψ (hsl l) z).1)⟩
    · exact hcv.2.1.trans (Set.mul_subset_mul (Set.subset_iUnion (fun l => tsupport (Φ l j)) l) hsN)
    · intro z hz
      exact ⟨z, Set.subset_iUnion (fun l => tsupport (Φ l j)) l (subset_tsupport _ hz), 1, h1N, mul_one z⟩)
    hvec hk
  have hle : ‖T u - k‖ₑ ^ 2 ≤ ENNReal.ofReal ε ^ 2 := by
    refine hfin.trans (le_trans (le_of_eq ?_) hδc)
    rw [hc]; ring
  have hle' : ‖T u - k‖ₑ ≤ ENNReal.ofReal ε := (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hε.le] at hle'
  exact hle'

end GlobalTheory.CompanionTheory.KernelColumns

end
end

section


theorem _root_.GlobalTheory.T.height_lipschitz_holds : PositivityTheory.RgEis.HtLip := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.htLip | exact GlobalTheory.CompanionTheory.RgEis.htLip | (intros; apply GlobalTheory.CompanionTheory.RgEis.htLip <;> assumption)
end

section


theorem _root_.GlobalTheory.T.staged_estimate_holds : PositivityTheory.RgEis.PiLocalization₂ := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.stage | exact GlobalTheory.CompanionTheory.RgEis.stage | (intros; apply GlobalTheory.CompanionTheory.RgEis.stage <;> assumption)
end
