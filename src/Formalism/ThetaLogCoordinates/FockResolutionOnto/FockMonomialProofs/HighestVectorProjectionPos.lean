module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementH
public import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FirstWeightLeOfSupport
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
public import Formalism.PolynomialDimension.MultinomialDepth.PartnerM

@[expose] public section

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Triv
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem supp_le_of_monomial {σ : Type} (Q : Set (σ →₀ ℕ)) (S : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]))
    (h : ∀ m ∈ Q, monomial m (1 : ℚ_[p]) ∈ S) : restrictSupport ℚ_[p] Q ≤ S := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [x.as_sum]
  refine S.sum_mem fun m hm => ?_
  have hmon : monomial m (AddMonoidAlgebra.coeff x m) = AddMonoidAlgebra.coeff x m • monomial m (1 : ℚ_[p]) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon]
  exact S.smul_mem _ (h m (hx hm))

theorem glAct_none (LL : Letters N) (j : ℕ) (h : ∀ i : Fin N, ¬ (i : ℕ) < j) (c d : Fin r) :
    glAct p LL j c d = 0 := by
  simp [Formalism.GM.M.glAct, h]

theorem wt_none (LL : Letters N) (j : ℕ) (h : ∀ i : Fin N, ¬ (i : ℕ) < j) (c : Fin r)
    (m : Fin N × Fin r →₀ ℕ) : wt LL j c m = 0 := by
  simp [Formalism.GM.M.wt, h]

theorem glAct_one (LL : Letters N) (i0 : Fin N) (h0 : (i0 : ℕ) = 0) (c d : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL 1 c d x =
      if LL.vec i0 then X (i0, c) * pderiv (i0, d) x else -(X (i0, d) * pderiv (i0, c) x) := by
  simp only [Formalism.GM.M.glAct]
  rw [Finset.sum_eq_single i0]
  · have hlt : (i0 : ℕ) < 1 := by omega
    rw [if_pos hlt]
    split_ifs <;> simp
  · intro b _ hb
    have hnb : ¬ (b : ℕ) < 1 := by
      intro hlt
      exact hb (Fin.ext (by omega))
    rw [if_neg hnb]
  · intro hn
    exact absurd (Finset.mem_univ i0) hn

theorem wt_one (LL : Letters N) (i0 : Fin N) (h0 : (i0 : ℕ) = 0) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL 1 c m = if LL.vec i0 then (m (i0, c) : ℤ) else -(m (i0, c) : ℤ) := by
  simp only [Formalism.GM.M.wt]
  rw [Finset.sum_eq_single i0]
  · rw [if_pos (by omega)]
  · intro b _ hb
    have hnb : ¬ (b : ℕ) < 1 := by
      intro hlt
      exact hb (Fin.ext (by omega))
    rw [if_neg hnb]
  · intro hn
    exact absurd (Finset.mem_univ i0) hn

theorem move_mem (i0 : Fin N) (t : Fin r) (d : ℕ) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hbase : ∀ m : Fin N × Fin r →₀ ℕ, (∀ c, c ≠ t → m (i0, c) = 0) → m (i0, t) = d →
      monomial m (1 : ℚ_[p]) ∈ S)
    (hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, t) x ∈ S) :
    ∀ (n : ℕ) (m : Fin N × Fin r →₀ ℕ), m (i0, t) + n = d → ∑ c, m (i0, c) = d →
      monomial m (1 : ℚ_[p]) ∈ S := by
  intro n
  induction n with
  | zero =>
    intro m hm hs
    refine hbase m (fun c hc => ?_) (by omega)
    have h1 := Finset.add_sum_erase Finset.univ (fun c => m (i0, c)) (Finset.mem_univ t)
    have h2 : ∑ x ∈ Finset.univ.erase t, m (i0, x) = 0 := by omega
    exact Finset.sum_eq_zero_iff.mp h2 c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩)
  | succ n ih =>
    intro m hm hs
    obtain ⟨a, hat, ha⟩ : ∃ a, a ≠ t ∧ m (i0, a) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have hsum : ∑ c, m (i0, c) = m (i0, t) :=
        Finset.sum_eq_single t (fun c _ hc => hne c hc) (fun hn => absurd (Finset.mem_univ t) hn)
      omega
    obtain ⟨m', hm'⟩ : ∃ m' : Fin N × Fin r →₀ ℕ,
        m' = m - Finsupp.single (i0, a) 1 + Finsupp.single (i0, t) 1 := ⟨_, rfl⟩
    have hle : Finsupp.single (i0, a) 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have heq : m' + Finsupp.single (i0, a) 1 = m + Finsupp.single (i0, t) 1 := by
      rw [hm', add_right_comm, tsub_add_cancel_of_le hle]
    have key : ∀ (f : Fin N × Fin r →₀ ℕ) (b : Fin r),
        ∑ c, ((f + Finsupp.single (i0, b) 1 : Fin N × Fin r →₀ ℕ)) (i0, c) = ∑ c, f (i0, c) + 1 := by
      intro f b
      simp [Finsupp.single_apply, Finset.sum_add_distrib]
    have hsum : ∑ c, m' (i0, c) = d := by
      have h3 := congrArg (fun f : Fin N × Fin r →₀ ℕ => ∑ c, f (i0, c)) heq
      simp only [key] at h3
      omega
    have ht : m' (i0, t) = m (i0, t) + 1 := by
      have h3 := congrArg (fun f : Fin N × Fin r →₀ ℕ => f (i0, t)) heq
      simp [hat] at h3
      omega
    have hmem := ih m' (by omega) hsum
    have hX := hst a _ hmem
    have he : Finsupp.single (i0, a) 1 + (m' - Finsupp.single (i0, t) 1) = m := by
      rw [hm', add_tsub_cancel_right, add_tsub_cancel_of_le hle]
    have hcalc : X (i0, a) * pderiv (i0, t) (monomial m' (1 : ℚ_[p])) =
        ((m (i0, t) + 1 : ℕ) : ℚ_[p]) • monomial m (1 : ℚ_[p]) := by
      rw [pderiv_monomial, ← pow_one (X (i0, a)), ← monomial_single_add, he, smul_monomial, ht]
      simp
    rw [hcalc] at hX
    have hne : ((m (i0, t) + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m (i0, t))
    have h4 := S.smul_mem (((m (i0, t) + 1 : ℕ) : ℚ_[p]))⁻¹ hX
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4

theorem pol_le_iso (LL : Letters N) (j : ℕ) (hj : j ≤ 1) (hr : 1 ≤ r) :
    ∃ la : Fin r → ℤ, Pol p r LL ≤ IsoC p LL j univ la := by
  by_cases hex : ∃ i0 : Fin N, (i0 : ℕ) < j
  · obtain ⟨i0, hi0⟩ := hex
    have hj1 : j = 1 := by omega
    have h0 : (i0 : ℕ) = 0 := by omega
    subst hj1
    rcases Bool.eq_false_or_eq_true (LL.vec i0) with hv | hv
    ·
      refine ⟨fun c => if c = (⟨0, hr⟩ : Fin r) then (LL.deg i0 : ℤ) else 0, ?_⟩
      simp only [Formalism.GM.M.IsoC, Formalism.GM.M.Pol]
      refine le_sInf ?_
      rintro S ⟨hHS, hGS⟩
      apply supp_le_of_monomial
      intro m hm
      have hm' : ∀ i, ∑ c, m (i, c) = LL.deg i := hm
      have hbase : ∀ m : Fin N × Fin r →₀ ℕ, (∀ c, c ≠ (⟨0, hr⟩ : Fin r) → m (i0, c) = 0) →
          m (i0, ⟨0, hr⟩) = LL.deg i0 → monomial m (1 : ℚ_[p]) ∈ S := by
        intro m hz hd
        apply hHS
        simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
          LinearMap.mem_ker]
        refine ⟨?_, ?_⟩
        · rw [MvPolynomial.mem_restrictSupport_iff]
          intro m2 hm2
          have hm3 := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm2)
          rw [Finset.mem_singleton] at hm3
          subst hm3
          simp only [Set.mem_setOf_eq]
          intro c _
          rw [wt_one LL i0 h0 c, hv, if_pos rfl]
          by_cases hc : c = ⟨0, hr⟩
          · rw [if_pos hc, hc, hd]
          · rw [if_neg hc, hz c hc]
            simp
        · intro c d hcd
          have hd0 : d ≠ ⟨0, hr⟩ := by
            intro hd0
            have hlt := hcd.2.2
            rw [hd0, Fin.lt_def] at hlt
            exact Nat.not_lt_zero _ hlt
          rw [glAct_one LL i0 h0 c d, hv, if_pos rfl, pderiv_monomial, hz d hd0]
          simp
      have hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, (⟨0, hr⟩ : Fin r)) x ∈ S := by
        intro a x hx
        have h1 := hGS a (Finset.mem_univ _) ⟨0, hr⟩ (Finset.mem_univ _) x hx
        rwa [glAct_one LL i0 h0, hv, if_pos rfl] at h1
      have hle : m (i0, ⟨0, hr⟩) ≤ LL.deg i0 := by
        rw [← hm' i0]
        exact Finset.single_le_sum (f := fun c => m (i0, c)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      exact move_mem i0 ⟨0, hr⟩ (LL.deg i0) S hbase hst (LL.deg i0 - m (i0, ⟨0, hr⟩)) m
        (by omega) (hm' i0)
    ·
      refine ⟨fun c => -(if c = (⟨r - 1, by omega⟩ : Fin r) then (LL.deg i0 : ℤ) else 0), ?_⟩
      simp only [Formalism.GM.M.IsoC, Formalism.GM.M.Pol]
      refine le_sInf ?_
      rintro S ⟨hHS, hGS⟩
      apply supp_le_of_monomial
      intro m hm
      have hm' : ∀ i, ∑ c, m (i, c) = LL.deg i := hm
      have hbase : ∀ m : Fin N × Fin r →₀ ℕ,
          (∀ c, c ≠ (⟨r - 1, by omega⟩ : Fin r) → m (i0, c) = 0) →
          m (i0, ⟨r - 1, by omega⟩) = LL.deg i0 → monomial m (1 : ℚ_[p]) ∈ S := by
        intro m hz hd
        apply hHS
        simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
          LinearMap.mem_ker]
        refine ⟨?_, ?_⟩
        · rw [MvPolynomial.mem_restrictSupport_iff]
          intro m2 hm2
          have hm3 := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm2)
          rw [Finset.mem_singleton] at hm3
          subst hm3
          simp only [Set.mem_setOf_eq]
          intro c _
          rw [wt_one LL i0 h0 c, hv, if_neg Bool.false_ne_true]
          by_cases hc : c = ⟨r - 1, by omega⟩
          · rw [if_pos hc, hc, hd]
          · rw [if_neg hc, hz c hc]
            simp
        · intro c d hcd
          have hct : c ≠ ⟨r - 1, by omega⟩ := by
            intro hct
            have hlt := hcd.2.2
            rw [Fin.lt_def, hct] at hlt
            have hdr := d.isLt
            simp only at hlt
            omega
          rw [glAct_one LL i0 h0 c d, hv, if_neg Bool.false_ne_true, pderiv_monomial, hz c hct]
          simp
      have hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, (⟨r - 1, by omega⟩ : Fin r)) x ∈ S := by
        intro a x hx
        have h1 := hGS ⟨r - 1, by omega⟩ (Finset.mem_univ _) a (Finset.mem_univ _) x hx
        rw [glAct_one LL i0 h0, hv, if_neg Bool.false_ne_true] at h1
        have h2 := S.neg_mem h1
        rwa [neg_neg] at h2
      have hle : m (i0, ⟨r - 1, by omega⟩) ≤ LL.deg i0 := by
        rw [← hm' i0]
        exact Finset.single_le_sum (f := fun c => m (i0, c)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      exact move_mem i0 ⟨r - 1, by omega⟩ (LL.deg i0) S hbase hst
        (LL.deg i0 - m (i0, ⟨r - 1, by omega⟩)) m (by omega) (hm' i0)
  · push_neg at hex
    have hn : ∀ i : Fin N, ¬ (i : ℕ) < j := fun i => not_lt.mpr (hex i)
    refine ⟨0, fun F _ => ?_⟩
    refine Formalism.CountingSumsFrames.hwc_le_isoC (p := p) LL j 0 ?_
    simp only [Formalism.GM.M.HWC, Formalism.GM.M.WtSpC, Submodule.mem_inf, Submodule.mem_iInf,
      LinearMap.mem_ker, MvPolynomial.mem_restrictSupport_iff]
    refine ⟨fun m _ => ?_, fun c d _ => ?_⟩
    · simp only [Set.mem_setOf_eq]
      intro c _
      rw [wt_none LL j hn]
      rfl
    · simp [glAct_none LL j hn]

end Triv

theorem trivial_projection_holds : TrivProj := by
  intro p _ N r LL j T P hj hr hP
  obtain ⟨la, hla⟩ := pol_le_iso (p := p) LL j hj hr
  obtain ⟨hPP, hran, hker⟩ := hP
  by_cases hT : la ∈ T
  · left
    intro F hF
    have hFr : F ∈ LinearMap.range P := by
      rw [hran]
      exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hT (hla hF))
    obtain ⟨y, rfl⟩ := hFr
    have h1 := congrArg (fun f => f y) hPP
    simpa using h1
  · right
    intro F hF
    have hFk : F ∈ LinearMap.ker P := by
      rw [hker]
      exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hT (hla hF))
    exact hFk

theorem highest_vector_projection_holds : HighestVectorProjectionPos := by
  intro p _ K r _ LL q J M ρ w e1 hK hr hρ hv hP hE
  exact highest_vector_projection_of_type_projections true p K r LL J M ρ w e1
    (fun _ => ⟨hK, trivial_projection_holds p (K + 1) r LL⟩) hr hρ hv hP hE

end Formalism.InvariantFactorPaths.L4
