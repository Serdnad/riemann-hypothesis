module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TauDegreeOnPathBound
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroModUniformiser
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DistAddTwoLeOfSameVec
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FourHundredSixteenLeA
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrameZeroStrictMono
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle013
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle011
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle007
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumPosOfPer
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.AdmissibleSmallRatio
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle005

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem div_mul_sub_le_div_sub_div (n s P Q ee kk rr : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hs : s < kk * P) (he : ee < rr * Q) :
    ((n / (P * Q) : ℕ) : ℤ) - ((kk + rr + 1 : ℕ) : ℤ) ≤ ((((n - s) / P - ee) / Q : ℕ) : ℤ) := by
  have hA : ((n / (P * Q) : ℕ) : ℤ) * ((P : ℤ) * Q) ≤ n := by exact_mod_cast Nat.div_mul_le_self n (P * Q)
  have hU : (((n - s : ℕ)) : ℤ) < (((n - s) / P : ℕ) : ℤ) * P + P := by exact_mod_cast Nat.lt_div_mul_add hP
  have hW : ((((n - s) / P - ee : ℕ)) : ℤ) < ((((n - s) / P - ee) / Q : ℕ) : ℤ) * Q + Q := by
    exact_mod_cast Nat.lt_div_mul_add hQ
  have hns : (n : ℤ) - s ≤ ((n - s : ℕ) : ℤ) := by omega
  have hue : (((n - s) / P : ℕ) : ℤ) - ee ≤ ((((n - s) / P - ee : ℕ)) : ℤ) := by omega
  have hs' : (s : ℤ) < kk * P := by exact_mod_cast hs
  have he' : (ee : ℤ) < rr * Q := by exact_mod_cast he
  have hP' : (0 : ℤ) < P := by exact_mod_cast hP
  have hQ' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  set A : ℤ := ((n / (P * Q) : ℕ) : ℤ)
  set U : ℤ := (((n - s) / P : ℕ) : ℤ)
  set W : ℤ := ((((n - s) / P - ee) / Q : ℕ) : ℤ)
  have st1 : A * Q - kk < U + 1 := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul_of_nonneg_left hc hP'.le
    nlinarith
  have st2 : A - rr - kk < W + 1 := by
    by_contra hc
    push_neg at hc
    have h1 := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℤ) ≤ Q)
    have hk0 : (0 : ℤ) ≤ kk := by positivity
    have h2 := mul_le_mul_of_nonneg_left hQ' hk0
    nlinarith
  push_cast
  linarith

section Pad

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem eZ_lt_mul_Qc (hX : X.Hyp p K) (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ)
    (he : e ∈ X.EE p K la) (j : ℤ) (i : Fin r) : X.eZ e j i < r * X.Qc p K j := by
  have hV := hX.valid
  have hJ : 0 < X.F.J := hV.1
  unfold Dat.eZ
  rw [dite_eq_left hJ]
  have hmem := Fintype.mem_piFinset.1
    (Fintype.mem_piFinset.1 he ⟨(j % (X.F.J : ℤ)).toNat % X.F.J, Nat.mod_lt _ hJ⟩) i
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  have h0 : (0 : ℤ) ≤ j % (X.F.J : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hJ.ne')
  have h1 : j % (X.F.J : ℤ) < X.F.J := Int.emod_lt_of_pos _ (by exact_mod_cast hJ)
  have hv : ((((j % (X.F.J : ℤ)).toNat % X.F.J : ℕ)) : ℤ) = j % (X.F.J : ℤ) := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hq : X.Qc p K ((((j % (X.F.J : ℤ)).toNat % X.F.J : ℕ)) : ℤ) = X.Qc p K j := by
    rw [hv]
    have e1 : j % (X.F.J : ℤ) + (j / (X.F.J : ℤ)) * X.F.J = j := by
      exact Int.emod_add_ediv_mul j (X.F.J : ℤ)
    have e2 := sum_Qc_per (p := p) (K := K) X hV (j % (X.F.J : ℤ)) (j / (X.F.J : ℤ))
    rw [e1] at e2
    exact e2.symm
  rw [hq] at hmem
  exact hmem.1

theorem sum_la_lt (hX : X.Hyp p K) (la : Fin n' → Fin (r + K) → ℕ) (hla : la ∈ X.LA p K) (j x : ℤ)
    (hx : x ∈ X.toLate j) : ∑ c, la (posOf n' x) c < (r + K) * X.Pz p K j x := by
  classical
  have hmem := Fintype.mem_piFinset.1 hla (posOf n' x)
  have hmem2 := Finset.mem_filter.1 hmem
  have hlt := (hmem2.2.2 j x hx rfl).1
  have hne : (Finset.univ : Finset (Fin (r + K))).Nonempty :=
    ⟨⟨0, by have := NeZero.ne r; omega⟩, Finset.mem_univ _⟩
  calc ∑ c, la (posOf n' x) c < ∑ _c : Fin (r + K), X.Pz p K j x :=
        Finset.sum_lt_sum_of_nonempty hne (fun c _ => hlt c)
    _ = (r + K) * X.Pz p K j x := by simp

end Pad

theorem restPad : RestPad 1088 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk la hla e he j
  have hV := hX.valid
  have hp := hX.prime.pos
  have hr : 0 < r := NeZero.pos r
  constructor
  · intro x hx hW
    have hb := mem_letters_bounds hx
    obtain ⟨i, hi, rfl⟩ := comb_frame_top X.F hV (j - 1) x hb.2.2 hb.1 (r - 1) (Nat.sub_lt hr Nat.one_pos) hW
    have hval : X.bfam p K la e j (X.F.fr (j - 1) i) =
        (X.nz p K la (j - 1) (X.F.fr (j - 1) i) - X.eZ e (j - 1) ⟨i, hi⟩) / X.Qc p K (j - 1) := by
      unfold Dat.bfam
      rw [if_pos hx, if_pos hW, Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · rw [if_pos rfl]
      · intro b _ hb'
        rw [if_neg]
        intro heq
        apply hb'
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact absurd heq.symm (ne_of_lt (fr_lt_fr_of_lt_of_valid hV (j - 1) b.val i h hi))
        · exact absurd heq (ne_of_lt (fr_lt_fr_of_lt_of_valid hV (j - 1) i b.val h b.isLt))
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hval]
    have hPQ := sum_PzQc hX (j - 1) _ hW
    rw [sub_add_cancel] at hPQ
    unfold Dat.Bw
    rw [← hPQ]
    unfold Dat.nz
    exact div_mul_sub_le_div_sub_div _ _ _ _ _ (r + K) r (Pz_pos hp _ _) (by unfold Dat.Qc; exact pow_pos hp _)
      (sum_la_lt hX la hla (j - 1) _ (sum_frlate X hV (j - 1) ⟨i, hi⟩)) (eZ_lt_mul_Qc hX la e he (j - 1) ⟨i, hi⟩)
  · intro x hx
    have hl := sum_LLsub X hV j x hx
    obtain ⟨h1, h2, -, -⟩ := sum_late_mem hl.1
    have hval : X.bfam p K la e j x = X.nz p K la j x := by
      unfold Dat.bfam
      rw [if_pos h1, if_neg h2, if_neg (not_le.mpr hl.2)]
    rw [hval]
    exact family_degrees_admissible hr hp (fun j x hx => (sum_LLsub X hV j x hx).1) la hla j x hx

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem beta_ratio_bound : BetaRatioBound 1088 := by
  intro p n' r K _ _ _ X hX hLa hk j b hA
  classical
  have hV := hX.valid
  have B := basics hX
  have hr : 0 < r := NeZero.pos r
  have hp0 : (0 : ℝ) < p := by linarith [B.p1]
  have hp2 : 2 ≤ p := hX.prime.two_le
  have h41 := (top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1
  have ha0 : 0 < X.a := by have := TE.four_hundred_sixteen_le_a hX; linarith

  have hL1 : 1 ≤ X.L₁ := by
    by_contra h
    have h0 : X.L₁ = 0 := by omega
    have hP2 := hX.P2
    rw [h0] at hP2
    have e1 : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹ := by simp
    rw [e1] at hP2
    have e2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ B.p1
    have e3 : (1 : ℝ) ≤ 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 := by
      have k5 := B.k5
      unfold Dat.k at k5
      have a1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 := by nlinarith
      have a2 : (1 : ℝ) ≤ X.Y ^ 2 := by nlinarith [B.Y1]
      have a3 := B.Ns1
      have a4 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) := by nlinarith
      nlinarith
    linarith
  have hP2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ (X.L₁ - 1) := by
    have h := hX.P2
    have e : ((X.L₁ : ℤ) - 1) = ((X.L₁ - 1 : ℕ) : ℤ) := by omega
    rw [e, zpow_natCast] at h
    exact h
  set D1 := X.F.dist j (X.F.fr j 0) with hD1
  set s := (X.F.letters j).filter (· < X.F.fr j 0) with hs
  have hfr0 : X.F.fr j 0 ∈ X.F.letters j := k_fr_mem_letters X.F hV j hr
  have hD1c := TE.dist_cast hfr0

  have hU1 : ∀ x ∈ s, D1 + X.L₁ + 1 ≤ X.F.dist j x := by
    intro x hx
    have hne : s.Nonempty := ⟨x, hx⟩
    have hmax := Finset.max'_mem s hne
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hmax
    have hgap := hV.2.2.2.2.2.2.1 j |>.2.2 (s.max' hne) hm1 hm2 (fun z hz hzlt =>
      Finset.le_max' s z (Finset.mem_filter.mpr ⟨hz, hzlt⟩))
    have hle := Finset.le_max' s x hx
    have hxc := TE.dist_cast (Finset.mem_filter.mp hx).1
    omega

  have hA1 : (X.beS p K j (X.restr j b) : ℝ) ≤ 4 * X.a / (p : ℝ) ^ (X.Rj p K j + D1 + X.L₁ + 1) := by
    unfold Dat.beS
    push_cast
    have h1 : ∀ x ∈ s, (X.Bdeg p K j (X.restr j b) x : ℝ) ≤
        2 * X.a / (p : ℝ) ^ X.Rj p K j * (1 / (p : ℝ) ^ X.F.dist j x) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      have b1 := (TE.Bdeg_bounds hX hk h41 j b hA x hx1 hx2).2
      have b2 := (TE.c_bounds hX h41 j x hx1).2.2
      refine le_trans b1 ?_
      rw [pow_add]
      have hq1 : (0 : ℝ) < (p : ℝ) ^ X.F.dist j x := by positivity
      have hq2 : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j := by positivity
      rw [div_mul_div_comm, mul_one, mul_comm ((p : ℝ) ^ X.Rj p K j)]
      exact div_le_div_of_nonneg_right b2 (by positivity)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.mul_sum]
    have hinj : Set.InjOn (X.F.dist j) (s : Set ℤ) := by
      intro x hx y hy hxy
      have c1 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
      have c2 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1
      have : (X.F.dist j x : ℤ) = (X.F.dist j y : ℤ) := by exact_mod_cast hxy
      omega
    have h2 : ∑ x ∈ s, (1 / (p : ℝ) ^ X.F.dist j x) = ∑ D ∈ s.image (X.F.dist j), (1 / (p : ℝ) ^ D) :=
      (Finset.sum_image (f := fun D : ℕ => 1 / (p : ℝ) ^ D) hinj).symm
    have h3 := Formalism.InvariantFactorPaths.BranchingDimensions.geometricSumDistinct p (D1 + X.L₁ + 1) (s.image (X.F.dist j)) hp2 (by
      intro D hD
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD
      exact hU1 x hx)
    rw [h2]
    have hc : 0 ≤ 2 * X.a / (p : ℝ) ^ X.Rj p K j := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left h3 hc) ?_
    rw [div_mul_div_comm, ← pow_add]
    have e : X.Rj p K j + (D1 + X.L₁ + 1) = X.Rj p K j + D1 + X.L₁ + 1 := by ring
    rw [e]
    apply le_of_eq
    ring

  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) := by
    have hm : X.F.fr j (r - 1) < X.F.fr (j + 1) (r - 1) := eFr_strictMono hV (by omega : j < j + 1)
    exact ⟨(X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdist : X.F.dist (j + 1) (X.F.fr j 0) = D1 + d := by
    have : ((X.F.dist (j + 1) (X.F.fr j 0) : ℕ) : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j 0 := by
      unfold Frames.dist
      exact Int.toNat_of_nonneg (by omega)
    omega
  have hB1 : X.a / (8 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) <
      (p : ℝ) ^ X.Rj p K (j + 1) := by
    have h := lt_pow_Rj hX (j + 1)
    unfold Tj at h
    rw [add_sub_cancel_right, hdist, pow_add ((p : ℝ)) D1 d, pow_succ ((p : ℝ)) (X.Rj p K (j + 1))] at h
    unfold Dat.k at h
    have hden : 0 < 8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have k5 := B.k5
      unfold Dat.k at k5
      have := B.Ns1
      have := B.Y1
      positivity
    rw [div_lt_iff₀ hden] at h
    have hden2 : 0 < 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have e : 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) =
          (p : ℝ) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := by ring
      rw [e]; exact mul_pos hp0 hden
    rw [div_lt_iff₀ hden2]
    calc X.a < (p : ℝ) ^ X.Rj p K (j + 1) * (p : ℝ) *
          (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := h
      _ = _ := by ring
  have hcore := (Formalism.InvariantFactorPaths.BranchingDimensions.admissibleSmallRatio p (r + K) X.Ns D1 X.L₁ (X.Rj p K j) (X.Rj p K (j + 1)) X.a X.Y
    ((p : ℝ) ^ d) (X.beS p K j (X.restr j b) : ℝ) hp2 (by omega)
    (by have := B.Ns1; exact_mod_cast this) B.Y1 ha0 (by positivity) hL1 hA1 hB1 hP2).2.2

  have hexp := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX j
  have hmono : X.F.fr (j - 1) 0 ≤ X.F.fr j 0 := (mem_letters_bounds hfr0).1
  have hQ : ((X.Qc p K j : ℕ) : ℝ) = (p : ℝ) ^ d * (p : ℝ) ^ X.Rj p K (j + 1) / (p : ℝ) ^ X.Rj p K j := by
    unfold Dat.Qc
    rw [eq_div_iff (by positivity)]
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    have : (((X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat : ℕ) : ℤ) =
        X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    omega
  rw [← hQ] at hcore
  have hQpos : (0 : ℝ) < ((X.Qc p K j : ℕ) : ℝ) := by
    rw [hQ]; positivity
  rw [div_le_div_iff₀ hQpos (by have := B.Y1; positivity)] at hcore
  linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
