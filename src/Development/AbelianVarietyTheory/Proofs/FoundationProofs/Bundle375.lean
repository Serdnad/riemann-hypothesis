module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle365
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle369
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle267
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle359
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem norm_gSum_le : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)),
    z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  intro l _ m z ψ hz
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m / 2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = m - k := ⟨_, rfl⟩
  rw [← hk]
  have hsm : s ≤ m := by omega
  have hmss : m ≤ s + s := by omega
  have hmsk : m = s + k := by omega
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let π : ZMod (l ^ m) →+* ZMod (l ^ s) := ZMod.castHom (pow_dvd_pow l hsm) (ZMod (l ^ s))
  have hsurj : Function.Surjective π := ZMod.castHom_surjective (pow_dvd_pow l hsm)
  let q : ZMod (l ^ m) := ((l ^ s : ℕ) : ZMod (l ^ m))
  have hqq : q * q = 0 := by
    simp only [q, ← Nat.cast_mul, ← pow_add, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow l hmss
  have hπq : π q = 0 := by
    simp only [q]
    rw [map_natCast, ZMod.natCast_self]
  have hfib : ∀ x x0 : ZMod (l ^ m), π x = π x0 → ∃ y, x = x0 + q * y := by
    intro x x0 h
    have h0 : π (x - x0) = 0 := by rw [map_sub, h, sub_self]
    have hd : ((x - x0).val : ZMod (l ^ m)) = x - x0 := ZMod.natCast_zmod_val _
    rw [← hd, map_natCast, ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨j, hj⟩ := h0
    refine ⟨(j : ZMod (l ^ m)), ?_⟩
    rw [← sub_eq_iff_eq_add', ← hd, hj, Nat.cast_mul]
  let e : ZMod (l ^ m) → Qbar l := fun x => z ^ x.val
  have he : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    simp only [e, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hz).symm
  let g : ZMod (l ^ m) → Qbar l := fun x => ψ x * e x
  have hzn : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    simp only [g, e, norm_mul, norm_pow, hzn, one_pow, mul_one]
    exact DirichletCharacter.norm_le_one ψ x
  have hsum : gSum m z ψ = ∑ x, g x := by
    unfold gSum
    symm
    rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun x _ hx => by
      by_contra h; exact hx (by simp [g, MulChar.map_nonunit ψ h]))]
    refine Finset.sum_bij' (fun x hx => (Finset.mem_filter.1 hx).2.unit) (fun b _ => (b : ZMod (l ^ m)))
      ?_ ?_ ?_ ?_ ?_ <;> simp [g, e]
  have hmove : ∀ x x0 y : ZMod (l ^ m), π x = π x0 → x * q * y = x0 * q * y := by
    intro x x0 y h
    obtain ⟨y', rfl⟩ := hfib x x0 h
    linear_combination (y' * y) * hqq
  have h1 : ∀ y : ZMod (l ^ m), (1 - q * y) * (1 + q * y) = 1 := fun y => by
    linear_combination (-(y * y)) * hqq
  have hinv : ∀ x0 y : ZMod (l ^ m), ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x =
      ψ (1 + q * y) * e (x0 * q * y) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x := by
    intro x0 y
    rw [Finset.mul_sum]
    calc ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x
        = ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g (x * (1 + q * y)) := by
          refine Finset.sum_nbij' (fun x => x * (1 - q * y)) (fun x => x * (1 + q * y)) ?_ ?_ ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_sub, map_one, hπq,
              zero_mul, sub_zero, mul_one] at ha ⊢
            exact ha
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_add (f := _), map_one, hπq,
              zero_mul, add_zero, mul_one] at ha ⊢
            exact ha
          · intro a _
            simp only [mul_assoc, h1, mul_one]
          · intro a _
            simp only [mul_assoc, mul_comm (1 + q * y), h1, mul_one]
          · intro a _
            simp only [mul_assoc, h1, mul_one]
      _ = _ := Finset.sum_congr rfl fun x hx => by
          have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
          show ψ (x * (1 + q * y)) * e (x * (1 + q * y)) = ψ (1 + q * y) * e (x0 * q * y) * (ψ x * e x)
          rw [map_mul, show x * (1 + q * y) = x + x * q * y by ring, he, hmove x x0 y hx']
          ring
  have H : ∀ u w y' : ZMod (l ^ m), IsUnit u → w = u + q * y' →
      (∀ y, ψ (1 + q * y) * e (u * q * y) = 1) → g w = g u := by
    intro u w y' hu hw hχu
    obtain ⟨U, rfl⟩ := hu
    have hUU : (U : ZMod (l ^ m)) * ((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = 1 := Units.mul_inv U
    have hw' : w = (U : ZMod (l ^ m)) + U * q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y') := by
      rw [hw]; linear_combination (-(q * y')) * hUU
    have hw'' : w = (U : ZMod (l ^ m)) * (1 + q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')) := by
      rw [hw']; ring
    have := hχu (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')
    show ψ w * e w = ψ U * e U
    rw [hw'', map_mul, ← hw'', hw', he]
    linear_combination (ψ U * e U) * this
  have hcard0 : ∀ x0, (Finset.univ.filter (fun x => π x = π x0)).card =
      (Finset.univ.filter (fun x => π x = 0)).card := by
    intro x0
    refine Finset.card_nbij' (fun x => x - x0) (fun x => x + x0) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_sub, ha, sub_self]
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_add (f := _), ha, zero_add]
    · intro a _; simp
    · intro a _; simp
  have htot : l ^ m = l ^ s * (Finset.univ.filter (fun x => π x = 0)).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := π)
      (fun x _ => Finset.mem_univ _)
    rw [Finset.card_univ, ZMod.card] at this
    refine this.trans ?_
    rw [Finset.sum_congr rfl (g := fun _ => (Finset.univ.filter (fun x => π x = 0)).card) (fun c _ => by
      obtain ⟨x0, rfl⟩ := hsurj c
      exact hcard0 x0), Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  have hcardk : (Finset.univ.filter (fun x => π x = 0)).card = l ^ k := by
    have h2 : l ^ s * (Finset.univ.filter (fun x => π x = 0)).card = l ^ s * l ^ k := by
      rw [← htot, ← pow_add, ← hmsk]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos s) h2
  rw [hsum, ← Finset.sum_fiberwise Finset.univ π g]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => ?_
  obtain ⟨x0, rfl⟩ := hsurj c
  by_cases hχ : ∀ y, ψ (1 + q * y) * e (x0 * q * y) = 1
  · have hall : ∀ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = g x0 := by
      intro x hx
      have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
      obtain ⟨y', hy'⟩ := hfib x x0 hx'
      by_cases hu0 : IsUnit x0
      · exact H x0 x y' hu0 hy' hχ
      by_cases hu : IsUnit x
      · refine (H x x0 (-y') hu (by rw [hy']; ring) fun y => ?_).symm
        rw [hmove x x0 y hx']
        exact hχ y
      · show ψ x * e x = ψ x0 * e x0
        rw [MulChar.map_nonunit ψ hu, MulChar.map_nonunit ψ hu0, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, norm_mul, hcard0, hcardk]
    push_cast
    calc ‖(l : Qbar l) ^ k‖ * ‖g x0‖ ≤ ‖(l : Qbar l) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hg1 x0) (norm_nonneg _)
      _ = _ := mul_one _
  · push_neg at hχ
    obtain ⟨y, hy⟩ := hχ
    have hI := hinv x0 y
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
      have hm : (1 - ψ (1 + q * y) * e (x0 * q * y)) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
        rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 (Ne.symm hy))
    rw [h0, norm_zero]
    positivity

end GlobalTheory.KZ.Cmp
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

theorem tau_mul_dvd (c : Coef l) (n : ℕ) (b' : c.O)
    (h : ∀ a : Qn c n, tbA c n (a * red c n b') = 0) (x : c.O) :
    ∃ q : ℤ_[l], tau c (b' * x) = (l : ℤ_[l]) ^ n * q := by
  have h1 := h (red c n x)
  rw [← map_mul, tbA_red, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  rw [mul_comm]
  exact h1

theorem pair_nondeg (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n)
    (h : ∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) : b = 0 := by
  obtain ⟨b', rfl⟩ := red_surjective c n b
  have hd := tau_mul_dvd c n b' h
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let q : c.O → ℤ_[l] := fun x => Classical.choose (hd x)
  have hq : ∀ x, tau c (b' * x) = (l : ℤ_[l]) ^ n * q x := fun x => Classical.choose_spec (hd x)
  let g : c.O →ₗ[ℤ_[l]] ℤ_[l] :=
    { toFun := q
      map_add' := fun x y => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_add, map_add (f := _), hq, hq, mul_add]
      map_smul' := fun r x => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_smul_comm, map_smul, hq, RingHom.id_apply, smul_eq_mul, smul_eq_mul]
        ring }
  obtain ⟨a0, ha0⟩ := (tau_spec c g).exists
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := (tau c).comp (LinearMap.mulLeft ℤ_[l] b')
  have e1 : ∀ x, f x = tau c (b' * x) := fun x => rfl
  have e2 : ∀ x, f x = tau c ((((l : ℤ_[l]) ^ n) • a0) * x) := fun x => by
    rw [e1, hq, smul_mul_assoc, map_smul, smul_eq_mul]
    congr 1
    exact ha0 x
  have heq : b' = ((l : ℤ_[l]) ^ n) • a0 := (tau_spec c f).unique e1 e2
  rw [heq, red_eq_zero_iff_mem]
  exact smul_mem_Ik c n (Ideal.mem_span_singleton_self _) a0

end GlobalTheory.Ord2.SelPerp
end
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.VacuumScalar
open scoped BigOperators

namespace GlobalTheory.VacuumExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem exists_scalar (hc : Crv D cc δ) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {g : GA D N} {g' : GA D N'}
    {L L'} (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L') :
    ∃ c : ℂ, W.Om g g' e0 = c • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 := by
  have hg1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, sd_of_moves hL, sd_of_moves hL', rfl⟩
  obtain ⟨-, hTh, -, -⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' _ _ k0 k1 e0 he
  obtain ⟨hline, w1, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg1 cc δ hc N N' _ k1
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := lattice_facts hc he W.nz hL hL'
  have heT : e0 ∈ TT D (tor0 D cc δ) N N' := ⟨he.1, 1, one_pos, fun y hy => by rw [one_smul]; exact a6 y hy⟩
  have hGT := W.maps g g' e0 heT
  have hinv : ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om g g' (W.Om g⁻¹ g'⁻¹ F) = F := by
    intro F hF
    rw [← W.mul _ _ _ _ _ hF, mul_inv_cancel, mul_inv_cancel, W.one F hF]
  have hinv' : W.Om g⁻¹ g'⁻¹ (W.Om g g' e0) = e0 := by
    rw [← W.mul _ _ _ _ _ heT, inv_mul_cancel, inv_mul_cancel, W.one e0 heT]
  refine hline _ ⟨hGT.1, fun x hx z => ?_⟩ _ hTh a1
  have hWT : Wd D (tor0 D cc δ) x (W.Om g g' e0) ∈ TT D (tor0 D cc δ) N N' := by
    obtain ⟨hd, m, hm, hfix⟩ := hGT
    refine ⟨Wd_differentiable _ hd, (La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N') * m,
      Nat.mul_pos (Nat.pos_of_ne_zero a4) hm, fun y hy => ?_⟩
    have h1 := AddSubgroup.nsmul_relIndex_mem (La D (tor0 D cc δ) L L') hy
    have h2 := (La D (tor0 D cc δ) L L').nsmul_mem h1 m
    have h3 := hfix _ ((La0 D (tor0 D cc δ) N N').nsmul_mem hy
      ((La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N')))
    rw [smul_smul, mul_comm] at h2 h3
    rw [← Wl_apply, ← Wl_apply, ← Module.End.mul_apply, ← a3 _ h2 _ hx, add_comm, a3 _ hx _ h2,
      Module.End.mul_apply, Wl_apply _ (W.Om g g' e0), h3]
  obtain ⟨x0, hx0, hW⟩ := GlobalTheory.T.weilOperator_conj_heisenberg_moved_lattice D hg1 cc δ hc.1.1 N N' e0 W g⁻¹ g g'⁻¹ g' L _ L' _ hL hL'
    (by rw [inv_mul_cancel]; exact moves_one D N) (by rw [inv_mul_cancel]; exact moves_one D N') x hx _ hGT
  rw [hinv', ← Wl_apply x0, a6 x0 hx0] at hW
  have h := hinv _ hWT
  rw [hW, w1 x hx] at h
  exact (congrFun h z).symm

theorem split_part {e : AE D} (h1 : e * e = e) (h2 : sgA D e = e)
    (h3 : ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q e) ∧ (¬ InertQ D q → ZeroAt D q (1 - e)))
    (g : GA D N) {x : (AE D)ˣ} (hx : x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x) :
    ∃ y : (AE D)ˣ, (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((y : AE D) - 1)) ∧
      y = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g : GA D N) : GL (Fin N) (AE D)) * sgU D y ∧
      ∀ {n : ℕ} (χ : HeckeU D n), Even n → χ.f y = χ.f x := by
  set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef
  have hxv : (x : AE D) = d * sgA D x := congrArg Units.val hx
  refine ⟨Units.map (_root_.GlobalTheory.VacuumScalar.cut e h1) x, fun q hq hi => ?_, Units.ext ?_, fun χ hn => ?_⟩
  · convert VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) (x - 1) using 1
    change e * x + (1 - e) * 1 - 1 = _
    ring
  · rw [Units.val_mul, det_cutG, ← hdef]
    change e * x + (1 - e) * 1 = _ * sgA D (e * x + (1 - e) * 1)
    rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h2]
    linear_combination e * hxv + ((d - 1) * (1 - sgA D x)) * h1
  · have hsplit : x = Units.map (_root_.GlobalTheory.VacuumScalar.cut e h1) x * Units.map (_root_.GlobalTheory.VacuumScalar.cut (1 - e) (compl_idem h1)) x :=
      Units.ext (cut_mul_cut e h1 (x : AE D)).1.symm
    have htriv : χ.f (Units.map (_root_.GlobalTheory.VacuumScalar.cut (1 - e) (compl_idem h1)) x) = 1 := by
      refine GlobalTheory.T.hecke_character_trivial_near_one D _ hn χ _ fun q hq hi => ?_
      convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) (x - 1) using 1
      change (1 - e) * x + (1 - (1 - e)) * 1 - 1 = _
      ring
    conv_rhs => rw [hsplit, map_mul, htriv, mul_one]

theorem vacuum_exact : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') (x x' : (AE D)ˣ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D)) * sgU D x' → Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → W.Om g g' e0 = fun z => ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z := by
  intro D cc δ hc N N' hN hN' e0 he W g g' x x' L L' hx hx' hL hL'
  obtain ⟨ε, -, a1, a2, h3⟩ := VacMove.exists_half_idem D
  have h1 : (ε + sgA D ε) * (ε + sgA D ε) = ε + sgA D ε := by
    have a3 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, a1]
    linear_combination a1 + a3 + 2 * a2
  have h2 : sgA D (ε + sgA D ε) = ε + sgA D ε := by rw [map_add (f := _), VacMove.sgA_sgA, add_comm]
  generalize ε + sgA D ε = e at h1 h2 h3
  obtain ⟨y, b1, b2, b3⟩ := split_part h1 h2 h3 g hx
  obtain ⟨y', c1, c2, c3⟩ := split_part h1 h2 h3 g' hx'
  obtain ⟨c, hO⟩ := exists_scalar hc he W hL hL'
  obtain ⟨Ls, hLs⟩ := exists_moves (cutG e h1 h2 g)
  obtain ⟨Ls', hLs'⟩ := exists_moves (cutG e h1 h2 g')
  obtain ⟨Li, hLi⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)
  obtain ⟨Li', hLi'⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')
  have hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)
  have hi : ∀ {n : ℕ} (k : GA D n),
      SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)
  have hcc := scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1
    (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO
    (W.split _ _ y y' Ls Ls' (hs g) (hs g') (fun q hq h => ⟨b1 q hq h, c1 q hq h⟩) b2 c2 hLs hLs')
    (GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places D cc δ hc N N' (hN.mul_right N') e0 he W _ _ Li Li' (hi g) (hi g') hLi hLi')
  rw [Even.neg_one_pow ((hN.mul_right _).add (hN'.mul_right _)), one_mul, b3 _ hN', c3 _ hN] at hcc
  rw [hO, hcc]
  rfl

end GlobalTheory.VacuumExact
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws : ∀ D : D7, GL3Theta.endInt D ∧ GL3Theta.phNorm D ∧ GL3Theta.beConj D := by
  first | exact @GlobalTheory.CMEndo.endo_all | exact GlobalTheory.CMEndo.endo_all | (intros; apply GlobalTheory.CMEndo.endo_all <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.oddness_condition_holds : ∀ D : D7, odd4 D := by
  first | exact @GlobalTheory.VacuumScalar.vacuum_scalar | exact GlobalTheory.VacuumScalar.vacuum_scalar | (intros; apply GlobalTheory.VacuumScalar.vacuum_scalar <;> assumption)
end
