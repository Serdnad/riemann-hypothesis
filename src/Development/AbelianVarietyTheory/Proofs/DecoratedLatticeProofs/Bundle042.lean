module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle204
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.ResidueUnr

open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_padicInt (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact z.norm_le_one

theorem norm_aeval_le (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) (g : ℤ_[l][X]) : ‖aeval x g‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro i _
  rw [Algebra.smul_def, norm_mul, norm_pow]
  exact mul_le_one₀ (norm_algebraMap_padicInt _) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hx)

theorem norm_aeval_lt (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) (g : ℤ_[l][X])
    (hg : g.map (PadicInt.toZMod (p := l)) = 0) : ‖aeval x g‖ < 1 := by
  have hd : ∀ n, (Polynomial.C (l : ℤ_[l])) ∣ Polynomial.C (g.coeff n) := by
    intro n
    have h0 : PadicInt.toZMod (g.coeff n) = 0 := by
      have := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f n) hg
      simpa [Polynomial.coeff_map] using this
    have hm : g.coeff n ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [← PadicInt.ker_toZMod]; exact h0
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
    exact map_dvd Polynomial.C hm
  obtain ⟨h, rfl⟩ : (Polynomial.C (l : ℤ_[l])) ∣ g := (Polynomial.C_dvd_iff_dvd_coeff _ _).2
    (fun n => by simpa using (Polynomial.C_dvd_iff_dvd_coeff _ _).1 (hd n) 0)
  rw [map_mul, aeval_C, norm_mul]
  have hl : ‖algebraMap ℤ_[l] (PadicAlgCl l) (l : ℤ_[l])‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  calc _ ≤ ‖algebraMap ℤ_[l] (PadicAlgCl l) (l : ℤ_[l])‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_aeval_le x hx h) (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hl

theorem exists_monic (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) : ∃ q : ℤ_[l][X], q.Monic ∧ aeval x q = 0 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at hx
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hx n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem exists_pow_near_one (x : PadicAlgCl l) (hx : ‖x‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ‖x ^ m - 1‖ < 1 := by
  apply GlobalTheory.ResidueRoot.exists_pow_alg <;> assumption

theorem frob_inj (z : PadicAlgCl l) (hz : ‖z‖ ≤ 1) (h : ‖z ^ l - 1‖ < 1) : ‖z - 1‖ < 1 := by
  have hp := (Fact.out : l.Prime)
  have hpoly : (((Polynomial.X - 1) ^ l - (Polynomial.X ^ l - 1) : ℤ_[l][X])).map (PadicInt.toZMod (p := l)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, sub_pow_char, one_pow, sub_self]
  have h1 := norm_aeval_lt z hz _ hpoly
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at h1
  have h2 : ‖(z - 1) ^ l‖ < 1 := by
    have e : (z - 1) ^ l = ((z - 1) ^ l - (z ^ l - 1)) + (z ^ l - 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 h2

theorem frob_pow (a : ℕ) : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖z ^ (l ^ a) - 1‖ < 1 → ‖z - 1‖ < 1 := by
  induction a with
  | zero => intro z _ h; simpa using h
  | succ a ih =>
    intro z hz h
    apply frob_inj z hz
    apply ih (z ^ l) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz)
    rw [← pow_mul, ← pow_succ']
    exact h

theorem one_le_norm_prod (s : Multiset ℂ_[l]) (h : ∀ a ∈ s, 1 ≤ ‖a‖) : 1 ≤ ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun b hb => h b (Multiset.mem_cons_of_mem hb)
    nlinarith

theorem exists_root_near (x : ℂ_[l]) (m : ℕ) (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[l], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  apply GlobalTheory.ResidueRoot.exists_root <;> assumption

theorem exists_near_kur : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]), ‖x‖ ≤ 1 →
    ∃ y ∈ MaximalUnramifiedExtension l, ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1 := by
  intro l _ x hx
  obtain ⟨x', hx'⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hx'
  set X0 : ℂ_[l] := (x' : ℂ_[l]) with hX0
  have hn' : ‖X0‖ ≤ 1 := by
    have e : X0 = (X0 - x) + x := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_sub_rev]; exact hx'.le) hx)
  by_cases h0 : ‖X0‖ < 1
  · refine ⟨0, zero_mem _, by simp, ?_⟩
    rw [sub_zero]
    have e : x = (x - X0) + X0 := by ring
    rw [e]; exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx' h0)
  have h1 : ‖x'‖ = 1 := by rw [← PadicComplex.norm_extends]; exact le_antisymm hn' (not_lt.1 h0)
  obtain ⟨m0, hm0, hsm⟩ := exists_pow_near_one x' h1
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' l (Fact.out : l.Prime).ne_one
  have hz : ‖x' ^ m - 1‖ < 1 :=
    frob_pow a (x' ^ m) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1.le) (by rw [← pow_mul, mul_comm]; exact hsm)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
  have hz' : ‖X0 ^ m - 1‖ < 1 := by
    have e : X0 ^ m - 1 = ((x' ^ m - 1 : PadicAlgCl l) : ℂ_[l]) := by simp [hX0, PadicComplex.coe_eq]
    rw [e, PadicComplex.norm_extends]; exact hz
  obtain ⟨ζ, hζ, hd⟩ := exists_root_near X0 m hmpos hz'
  refine ⟨ζ, ?_, ?_, ?_⟩
  · unfold MaximalUnramifiedExtension
    exact Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hmpos, hm, hζ⟩)
  · have : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hmpos.ne').1 this).le
  · have e : x - ζ = (x - X0) + (X0 - ζ) := by ring
    rw [e]; exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx' hd)

end GlobalTheory.ResidueUnr
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem ramBig_of_ramShare : ∀ (D : D7) (u : D.what₂.Word), RamShare D u → 0 < d0 D u → 2 < (D.mem u).A.T →
    RamBig D u ((D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1)) := by
  intro D u hS hd hT
  have hT' : (2 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast hT
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by linarith
  set a : ℝ := -(1 / (((D.mem u).A.T : ℝ) - 1)) with ha
  have ha1 : 1 / (((D.mem u).A.T : ℝ) - 1) < 1 := by
    rw [div_lt_one hpos]; linarith
  have ha0 : 0 < 1 / (((D.mem u).A.T : ℝ) - 1) := by positivity
  have hb : -2 ≤ a := by rw [ha]; linarith
  have hB := one_add_mul_le_pow hb D.R.f
  have hd' : (0 : ℝ) < (d0 D u : ℝ) := by exact_mod_cast hd
  unfold RamShare at hS
  unfold RamBig
  have hbase : 0 < 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by linarith
  have hp : 0 < (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := pow_pos hbase _
  refine ⟨?_, ?_⟩
  · have : (0 : ℝ) < (dU D u : ℝ) := by rw [hS]; exact mul_pos hd' hp
    exact_mod_cast this
  · rw [hS]
    have e1 : 1 + a = 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by rw [ha]; ring
    rw [e1] at hB
    have e2 : 1 + (D.R.f : ℝ) * a = 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) := by rw [ha]; ring
    rw [e2] at hB
    rw [mul_comm ((d0 D u : ℝ))]
    exact mul_le_mul_of_nonneg_right hB hd'.le

end GlobalTheory.Core.Rk
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

theorem exists_normOne_residues {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)]
    {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S)
    (T : Finset P) (hT : ∀ Q ∈ T, ∀ Q' ∈ T, σ (Z.e Q) ≠ Z.e Q') (c : ∀ Q, (k Q)ˣ) :
    ∃ z : S, (z : A) * σ z = 1 ∧ (∀ Q ∈ T, r Q z = c Q) ∧
      ∀ b : A, (∀ Q ∈ T, Z.p Q b ∈ Z.O Q ∧ Z.p Q (σ b) ∈ Z.O Q) → (1 - (z : A)) * b ∈ S := by
  classical

  have comp : ∀ (f : P → A) Q0, Z.p Q0 (∑ Q ∈ T, Z.e Q * f Q) = if Q0 ∈ T then Z.p Q0 (f Q0) else 0 := by
    intro f Q0

    rw [map_sum]
    by_cases h : Q0 ∈ T
    · rw [if_pos h, Finset.sum_eq_single_of_mem Q0 h
        (fun Q _ hQ => by rw [map_mul, Z.e_ne Q Q0 (Ne.symm hQ), zero_mul]), map_mul, Z.e_self, one_mul]
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun Q hQ => by
        rw [map_mul, Z.e_ne Q Q0 (by rintro rfl; exact h hQ), zero_mul]
  have smem : ∀ f : P → A, (∀ Q, f Q ∈ S) → (∑ Q ∈ T, Z.e Q * f Q) ∈ S := fun f hf =>
    Subring.sum_mem _ fun Q _ => Subring.mul_mem _ (Z.e_mem Q) (hf Q)

  choose s hs using fun Q => Z.r_surj Q (c Q : k Q)
  have hval : ∀ Q, (Z.O Q).valuation (Z.p Q (s Q)) = 1 := fun Q => by
    have hm : Z.p Q (s Q) ∈ Z.O Q := (Z.int _).1 (s Q).2 Q
    refine le_antisymm (((Z.O Q).valuation_le_one_iff _).2 hm) (not_lt.1 fun hc => ?_)
    have := (Z.r_ker Q (s Q)).2 hc
    rw [hs Q] at this
    exact (c Q).ne_zero this
  have hne : ∀ Q, Z.p Q (s Q) ≠ 0 := fun Q e => by
    have := hval Q; rw [e, map_zero] at this; exact zero_ne_one this
  have hinv : ∀ Q, (Z.p Q (s Q))⁻¹ ∈ Z.O Q := fun Q => by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hval Q, inv_one]
  choose t ht using fun Q => Z.pO_surj Q ⟨_, hinv Q⟩
  have hpt : ∀ Q, Z.p Q (t Q) = (Z.p Q (s Q))⁻¹ := fun Q => by
    rw [← Z.pO_coe, ht Q]

  obtain ⟨E, hEd⟩ : ∃ E, E = ∑ Q ∈ T, Z.e Q * 1 := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a, a = ∑ Q ∈ T, Z.e Q * (s Q : A) := ⟨_, rfl⟩
  obtain ⟨bb, hbd⟩ : ∃ bb, bb = ∑ Q ∈ T, Z.e Q * (t Q : A) := ⟨_, rfl⟩
  have pE : ∀ Q0, Z.p Q0 E = if Q0 ∈ T then 1 else 0 := fun Q0 => by
    rw [hEd, comp, map_one]
  have pa : ∀ Q0, Z.p Q0 a = if Q0 ∈ T then Z.p Q0 (s Q0) else 0 := fun Q0 => by rw [had, comp]
  have pb : ∀ Q0, Z.p Q0 bb = if Q0 ∈ T then Z.p Q0 (t Q0) else 0 := fun Q0 => by rw [hbd, comp]
  have pF : ∀ Q0 ∈ T, Z.p Q0 (σ E) = 0 := fun Q0 hQ0 => by

    rw [hEd, map_sum, map_sum]
    refine Finset.sum_eq_zero fun Q hQ => ?_
    obtain ⟨Q3, h3⟩ := Z.exists_bar hσ Q
    rw [map_mul, map_one, mul_one, h3, Z.e_ne Q3 Q0 (fun h => hT Q hQ Q0 hQ0 (by rw [h3, h]))]
  have Emem : E ∈ S := hEd ▸ smem _ fun _ => one_mem _
  have amem : a ∈ S := had ▸ smem _ fun Q => (s Q).2
  have bmem : bb ∈ S := hbd ▸ smem _ fun Q => (t Q).2
  have hE : E * E = E := Z.ext' fun Q0 => by rw [map_mul, pE]; split_ifs <;> simp
  have hEF : E * σ E = 0 := Z.ext' fun Q0 => by
    rw [map_mul, map_zero]
    by_cases h : Q0 ∈ T
    · rw [pF Q0 h, mul_zero]
    · rw [pE, if_neg h, zero_mul]
  have ha : E * a = a := Z.ext' fun Q0 => by rw [map_mul, pE, pa]; split_ifs <;> simp
  have hb : E * bb = bb := Z.ext' fun Q0 => by rw [map_mul, pE, pb]; split_ifs <;> simp
  have hab : a * bb = E := Z.ext' fun Q0 => by
    rw [map_mul, pE, pa, pb]
    split_ifs
    · rw [hpt, mul_inv_cancel₀ (hne Q0)]
    · simp
  set F := σ E with hFd
  set x := σ a with hxd
  set y := σ bb with hyd
  have hF : F * F = F := by rw [hFd, ← map_mul, hE]
  have hFx : F * x = x := by rw [hFd, hxd, ← map_mul, ha]
  have hFy : F * y = y := by rw [hFd, hyd, ← map_mul, hb]
  have hxy : x * y = F := by rw [hFd, hxd, hyd, ← map_mul, hab]
  have hEx : E * x = 0 := by rw [← hFx, ← mul_assoc, hEF, zero_mul]
  have hEy : E * y = 0 := by rw [← hFy, ← mul_assoc, hEF, zero_mul]
  have hFa : F * a = 0 := by rw [← ha, ← mul_assoc, mul_comm F E, hEF, zero_mul]
  have hFb : F * bb = 0 := by rw [← hb, ← mul_assoc, mul_comm F E, hEF, zero_mul]
  have hax : a * x = 0 := by
    calc a * x = (E * a) * (F * x) := by rw [ha, hFx]
      _ = (E * F) * (a * x) := by ring
      _ = 0 := by rw [hEF, zero_mul]
  have hby : bb * y = 0 := by
    calc bb * y = (E * bb) * (F * y) := by rw [hb, hFy]
      _ = (E * F) * (bb * y) := by ring
      _ = 0 := by rw [hEF, zero_mul]
  have zmem : 1 - E - F + a + y ∈ S :=
    add_mem (add_mem (sub_mem (sub_mem (one_mem _) Emem) (hS _ Emem)) amem) (hS _ bmem)
  refine ⟨⟨1 - E - F + a + y, zmem⟩, ?_, ?_, ?_⟩
  · show (1 - E - F + a + y) * σ (1 - E - F + a + y) = 1
    have hσF : σ F = E := hσ E
    have hσy : σ y = bb := hσ bb
    rw [map_add (f := _), map_add (f := _), map_sub, map_sub, map_one, hσF, hσy]
    linear_combination hE + hF + 2 * hEF - hEx - hb - hFx - hFb - ha - hFy - hFa - hEy + hax + hab + hxy + hby
  · intro Q hQ
    rw [← hs Q]
    refine Z.r_congr Q ?_
    show Z.p Q (1 - E - F + a + y) = Z.p Q (s Q)
    have hy0 : Z.p Q y = 0 := by rw [← hFy, map_mul, pF Q hQ, zero_mul]
    rw [map_add (f := _), map_add (f := _), map_sub, map_sub, map_one, pE, if_pos hQ, pF Q hQ, pa, if_pos hQ, hy0]
    ring
  · intro w hw
    show (1 - (1 - E - F + a + y)) * w ∈ S
    have key : (1 - (1 - E - F + a + y)) * w = (E - a) * w + σ ((E - bb) * σ w) := by
      rw [map_mul, map_sub, hσ w]; ring
    rw [key]
    refine add_mem ((Z.int _).2 fun Q0 => ?_) (hS _ ((Z.int _).2 fun Q0 => ?_))
    · rw [map_mul, map_sub, pE, pa]
      by_cases h : Q0 ∈ T
      · rw [if_pos h, if_pos h]
        exact Subring.mul_mem _ (sub_mem (one_mem _) ((Z.int _).1 (s Q0).2 Q0)) (hw Q0 h).1
      · rw [if_neg h, if_neg h, sub_zero, zero_mul]; exact zero_mem _
    · rw [map_mul, map_sub, pE, pb]
      by_cases h : Q0 ∈ T
      · rw [if_pos h, if_pos h]
        exact Subring.mul_mem _ (sub_mem (one_mem _) ((Z.int _).1 (t Q0).2 Q0)) (hw Q0 h).2
      · rw [if_neg h, if_neg h, sub_zero, zero_mul]; exact zero_mem _

end GlobalTheory.LevNorm
end

section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section
namespace GlobalTheory.ScalConj

theorem single_conj_apply {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (a b i j : Fin n) :
    (A * (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) * B) i j = A i a * B b j := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

def conjInt {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K) :
    Subalgebra O (Matrix (Fin n) (Fin n) O) where
  carrier := {X | ∃ Y : Matrix (Fin n) (Fin n) O,
    Y.map O.subtype = (m : Matrix (Fin n) (Fin n) K) * X.map O.subtype * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  mul_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y * Y', ?_⟩
    rw [Matrix.map_mul, Matrix.map_mul, hY, hY']
    have : ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (m : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul m
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), this, Matrix.one_mul]
  add_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y + Y', ?_⟩
    rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hY, hY', Matrix.mul_add, Matrix.add_mul]
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap O _ r, ?_⟩
    have h : (algebraMap O (Matrix (Fin n) (Fin n) O) r).map O.subtype = (r : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.algebraMap_matrix_apply]
      · simp [Matrix.algebraMap_matrix_apply, h, Matrix.one_apply_ne h]
    rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]

theorem single_map_subtype {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (a b : Fin n) :
    (Matrix.single a b (1 : O)).map O.subtype = (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem entry_mul_inv_entry_mem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) (i a b j : Fin n) :
    (m : Matrix (Fin n) (Fin n) K) i a * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b j ∈ O := by
  have hle : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) ≤ conjInt O m := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx'⟩ := hc x hx
    exact ⟨x', congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hx'⟩
  rw [hT] at hle
  obtain ⟨Y, hY⟩ := hle (Algebra.mem_top : Matrix.single a b (1 : O) ∈ (⊤ : Subalgebra O (Matrix (Fin n) (Fin n) O)))
  have h := congrFun (congrFun hY i) j
  rw [single_map_subtype, single_conj_apply] at h
  rw [← h]
  exact (Y i j).2

theorem isScal_of_conj (K : Type) [Field K] (O : ValuationSubring K) (n : ℕ) (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) : IsScal O m := by
  have H := entry_mul_inv_entry_mem O m T hT hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  set M : Matrix (Fin n) (Fin n) K := (m : Matrix (Fin n) (Fin n) K) with hM
  set N : Matrix (Fin n) (Fin n) K := ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hN
  have hMN : M * N = 1 := Units.mul_inv m
  obtain ⟨⟨i0, a0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => O.valuation (M p.1 p.2)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  set c := M i0 a0 with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : ∀ i a, M i a = 0 := fun i a => by
      have h1 := hmax (i, a) (Finset.mem_univ _)
      simp only [h0, map_zero] at h1
      exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    have h1 := congrFun (congrFun hMN ⟨0, hn⟩) ⟨0, hn⟩
    simp [Matrix.mul_apply, hz] at h1
  have hv : 0 < O.valuation c := (Valuation.pos_iff _).2 hc0
  have hy : ∀ i a, c⁻¹ * M i a ∈ O := fun i a => by
    rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
    exact (inv_mul_le_one₀ hv).2 (hmax (i, a) (Finset.mem_univ _))
  have hz : ∀ b j, c * N b j ∈ O := fun b j => H i0 a0 b j
  let Y : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hy i j⟩
  let Z : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hz i j⟩
  have hYm : Y.map O.subtype = c⁻¹ • M := by ext i j; rfl
  have hZm : Z.map O.subtype = c • N := by ext i j; rfl
  have inj : Function.Injective fun X : Matrix (Fin n) (Fin n) O => X.map O.subtype :=
    Matrix.map_injective (Subtype.val_injective)
  have key : ∀ {A B : Matrix (Fin n) (Fin n) K}, A * B = 1 → (c⁻¹ • A) * (c • B) = 1 := fun {A B} h => by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, h]
  have hNM : N * M = 1 := Units.inv_mul m
  have e1 : Y * Z = 1 := inj (by
    show (Y * Z).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, key hMN])
  have e2 : Z * Y = 1 := inj (by
    show (Z * Y).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hc0, one_smul, hNM])
  refine ⟨Units.mk0 c hc0, ⟨Y, Z, e1, e2⟩, ?_⟩
  show M = c • (Y.map O.subtype)
  rw [hYm, smul_smul, mul_inv_cancel₀ hc0, one_smul]

end GlobalTheory.ScalConj
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

namespace GlobalTheory.HwSpan

theorem eq_top_of_hwSub_le : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), KStable M.act N →
    (∀ μ, hwSub M.act μ ≤ N) → N = ⊤ := by
  intro p q M N hN hhw
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨W, hfd, hvW, hW⟩ := M.kfin v
  have hle : W ≤ N := GlobalTheory.BlockReps.le_of_hw hL hW (fun x _ => M.wts x) hN
    (fun μ x _ hx => hhw μ hx.2)
  exact hle hvW

end GlobalTheory.HwSpan
end
