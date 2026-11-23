module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle503
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
import ReciprocityTheory.DualLattices.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.QLog.BFrame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_xi (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.xi ε) = ∑ i ∈ Finset.range p, (1 + Sandwich.mu ε) ^ i := by

  rw [Sandwich.xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, Sandwich.mu,
    add_sub_cancel]
  congr 2
  exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε

theorem one_add_pow {ε : PreTilt O p} (F : BFrame ε) (i : ℕ) :
    (1 + (p : F.B) * F.τ) ^ i = 1 + (i : F.B) * ((p : F.B) * F.τ) := by
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : F.B) * (p : F.B) ^ 2) * F.τ_sq

theorem a_frobenius_xi {ε : PreTilt O p} (F : BFrame ε) :
    F.a (WittVector.frobenius (Sandwich.xi ε)) = p * (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) := by

  rw [frobenius_xi, map_sum]
  have h1 : ∀ i ∈ Finset.range p, F.a ((1 + Sandwich.mu ε) ^ i) = 1 + (i : F.B) * ((p : F.B) * F.τ) :=
    fun i _ => by rw [map_pow, map_add (f := _), map_one, ← F.p_τ, one_add_pow]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  have h2 : (∑ i ∈ Finset.range p, (i : F.B)) = ((p.choose 2 : ℕ) : F.B) := by
    rw [← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]
  rw [h2]
  ring

theorem frobenius_xi_unit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∃ u : F.B, IsUnit u ∧ F.τ ∣ u - 1 ∧ F.a (WittVector.frobenius (xi ε)) = p * u := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F
  refine ⟨1 + ((p.choose 2 : ℕ) : F.B) * F.τ, ?_, ⟨((p.choose 2 : ℕ) : F.B), by ring⟩,
    a_frobenius_xi F⟩
  have h : (1 + ((p.choose 2 : ℕ) : F.B) * F.τ) * (1 - ((p.choose 2 : ℕ) : F.B) * F.τ) = 1 := by
    linear_combination (-(((p.choose 2 : ℕ) : F.B)) ^ 2) * F.τ_sq
  exact ⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩

end GlobalTheory.QLog.BFrame
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WSolve

theorem nilp_mod_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)], v.Integers O → ∀ x : O, ¬IsUnit x → IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O)}) x) := by
  intro p _ C _ _ v O _ _ hp hv x hx
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) (fun h => hx (hv.isUnit_iff_valuation_eq_one.2 h))
  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast]
    exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hp0 hx1
  refine ⟨k, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hv.dvd_iff_le, map_pow, map_pow]
  exact hk.le

theorem semilin_nil : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent

theorem perf_solve : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := GlobalTheory.T.perfection_existsUnique_sub_matrix_frobenius_eq

theorem witt_solve : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)), (∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) → ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := GlobalTheory.T.wittVector_existsUnique_sub_matrix_frobenius_eq

theorem iter_map {T T' : Type} [CommRing T] [CommRing T'] {ι : Type} [Fintype ι] (f : T →+* T')
    (σ : T →+* T) (σ' : T' →+* T') (hf : ∀ x, f (σ x) = σ' (f x)) (M : Matrix ι ι T) (k : ℕ)
    (w : ι → T) :
    (fun u : ι → T' => (M.map f).mulVec fun j => σ' (u j))^[k] (fun j => f (w j)) =
      fun i => f ((fun u : ι → T => M.mulVec fun j => σ (u j))^[k] w i) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    funext i
    simpa only [← hf, Function.comp_def] using (RingHom.map_mulVec f M (fun j => σ (w j)) i).symm

theorem coeff_nil {S : Type} [CommRing S] {p : ℕ} [Fact p.Prime] [CharP S p] (y : Perfection S p)
    (h : IsNilpotent (Perfection.coeff S p 0 y)) (n : ℕ) : IsNilpotent (Perfection.coeff S p n y) := by
  have e : ∀ n, Perfection.coeff S p n y ^ (p ^ n) = Perfection.coeff S p 0 y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, Perfection.coeff_pow_p', ih]
  exact IsNilpotent.of_pow (m := p ^ n) (by rw [e]; exact h)

theorem key (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Ainf p O)) (N : ℕ)
    (hN : ∀ j i, IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O)}) (WittVector.fontaineTheta O p
      ((fun w : ι → Ainf p O => M.mulVec fun k => WittVector.frobenius (w k))^[N] (Pi.single j 1) i)))) :
    ∀ c : ι → Ainf p O, ∃! v : ι → Ainf p O, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  apply witt_solve p (PreTilt O p) ι M
  apply perf_solve p (ModP O p) ι (M.map WittVector.constantCoeff)
  intro n
  apply semilin_nil p (ModP O p) ι _ N
  intro j i
  have e1 : (Pi.single j 1 : ι → ModP O p) =
      fun k => Perfection.coeff (ModP O p) p n ((Pi.single j 1 : ι → PreTilt O p) k) := by
    funext k; by_cases h : k = j
    · subst h; simp only [Pi.single_eq_same]; exact (map_one _).symm
    · simp only [Pi.single_eq_of_ne h]; exact (map_zero _).symm
  have e2 : (Pi.single j 1 : ι → PreTilt O p) =
      fun k => WittVector.constantCoeff ((Pi.single j 1 : ι → Ainf p O) k) := by
    funext k; by_cases h : k = j
    · subst h; simp
    · simp [h]
  have h1 := congrFun (iter_map (T := PreTilt O p) (Perfection.coeff (ModP O p) p n)
    (frobenius (PreTilt O p) p) (frobenius (ModP O p) p) (fun x => by rw [frobenius_def, frobenius_def]; exact map_pow (Perfection.coeff (ModP O p) p n) x p)
    (M.map WittVector.constantCoeff) N (Pi.single j 1)) i
  have h2 := iter_map WittVector.constantCoeff WittVector.frobenius
    (frobenius (PreTilt O p) p) (fun x => by simp [frobenius_def, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]) M N (Pi.single j 1)
  rw [e1]
  erw [h1]
  rw [e2, h2]
  apply coeff_nil
  have := hN j i
  rw [WittVector.mk_fontaineTheta] at this
  exact this

theorem frobenius_mu_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) =
      (∑ i ∈ Finset.range p, (WittVector.teichmuller p ε) ^ i) * Sandwich.mu ε := by
  have h : WittVector.frobenius (WittVector.teichmuller p ε) = (WittVector.teichmuller p ε) ^ p := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [Sandwich.mu, map_sub, map_one, h, geom_sum_mul]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (_hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (M : Matrix ι ι (Ainf p O)), IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) M → (∀ c : ι → Ainf p O, ∃ v : ι → Ainf p O, ∀ i, v i - M.mulVec (fun j => WittVector.frobenius (v j)) i = c i) ∧ ∀ v : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ v i - M.mulVec (fun j => WittVector.frobenius (v j)) i) → ∀ i, Sandwich.mu ε ∣ v i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ M hM
  classical
  obtain ⟨N, hN⟩ := hM
  have hK := key p O ι M N (fun j i => nilp_mod_p p C v O hv _ (hN _ i))
  refine ⟨fun c => ?_, ?_⟩
  · obtain ⟨x, hx, -⟩ := hK c
    exact ⟨x, fun i => congrFun hx i⟩
  intro w hw
  choose u hu using hw
  have hφμ := frobenius_mu_eq p O ε
  set s : Ainf p O := ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε) ^ i with hs
  have h1 : ε.untilt = 1 := by simpa [zeta] using hε.zeta_zero
  have hθs : WittVector.fontaineTheta O p s = p := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hs, map_sum, map_pow, WittVector.fontaineTheta_teichmuller, h1]
  have hK' := key p O ι (s • M) 1 (fun j i => by
    have e : (fun k => WittVector.frobenius ((Pi.single j 1 : ι → Ainf p O) k)) = Pi.single j 1 := by
      funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [Function.iterate_one, e, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.smul_apply, smul_eq_mul, map_mul, hθs]
    rw [← map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))]
    exact IsNilpotent.zero)
  obtain ⟨w', hw', -⟩ := hK' u
  have hz : (w - Sandwich.mu ε • w') - M.mulVec (fun k => WittVector.frobenius ((w - Sandwich.mu ε • w') k)) = 0 := by
    funext i
    have a := hu i
    have b := congrFun hw' i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      map_sub, map_mul, hφμ, Pi.zero_apply] at a b ⊢
    have hsum : ∑ x, M i x * (WittVector.frobenius (w x) - s * Sandwich.mu ε * WittVector.frobenius (w' x)) =
        ∑ x, M i x * WittVector.frobenius (w x) - Sandwich.mu ε * ∑ x, s * M i x * WittVector.frobenius (w' x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum]
    linear_combination a - Sandwich.mu ε * b
  have h0 : (0 : ι → Ainf p O) - M.mulVec (fun k => WittVector.frobenius ((0 : ι → Ainf p O) k)) = 0 := by
    funext i; simp [Matrix.mulVec, dotProduct]
  have := (hK 0).unique hz h0
  intro i
  refine ⟨w' i, ?_⟩
  have := congrFun this i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.WSolve
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.WinLift

theorem isUnit_of_isUnit_theta {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O)
    (z : Ainf p O) (hz : IsUnit (WittVector.fontaineTheta O p z)) : IsUnit z := by
  haveI := GlobalTheory.AinfXi.isLocalRing_ainf (p := p) hv
  haveI := ReciprocityTheory.PGsh.Ainf.O_local O hv
  by_contra hn
  obtain ⟨w, hw⟩ := ReciprocityTheory.PGsh.Ainf.theta_surj p O hv (↑hz.unit⁻¹ : O)
  have hm : z ∈ IsLocalRing.maximalIdeal (Ainf p O) := (IsLocalRing.mem_maximalIdeal _).2 hn
  have hk : z * w - 1 ∈ IsLocalRing.maximalIdeal (Ainf p O) := by
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (WittVector.fontaineTheta O p))
    rw [RingHom.mem_ker, map_sub, map_mul, hw, map_one, IsUnit.mul_val_inv, sub_self]
  have h1 := Ideal.sub_mem _ (Ideal.mul_mem_right w _ hm) hk
  rw [sub_sub_cancel] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal (Ainf p O)).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_unit_lift_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι F.B), IsUnit U → ∃ V : Matrix ι ι (Ainf p O), IsUnit V ∧ ∀ i j, F.τ ∣ U i j - F.a (V i j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F ι _ _ U hU
  choose x y hxy using fun i j => F.gen (U i j)
  refine ⟨Matrix.of x, ?_, fun i j => ⟨F.a (y i j), by rw [hxy i j]; simp⟩⟩
  have hτ := GlobalTheory.WinLift.theta_tau F hv hε
  have e : F.θ.mapMatrix (F.a.mapMatrix (Matrix.of x)) = F.θ.mapMatrix U :=
    Matrix.ext fun i j => by simp [hxy i j, hτ]
  have hdet : WittVector.fontaineTheta O p (Matrix.of x).det = F.θ U.det := by
    rw [← F.θ_a, RingHom.map_det, RingHom.map_det, e, ← RingHom.map_det]
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_theta hv
  rw [hdet]
  exact ((Matrix.isUnit_iff_isUnit_det U).1 hU).map F.θ

end GlobalTheory.WinLift
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

theorem GlobalTheory.WinLift.frob_lift_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V F0 hV hF hθ i m
  set ξ' : Ainf p O := WittVector.frobenius (xi ε) with hξ'
  set μ : Ainf p O := Sandwich.mu ε with hμ
  set G : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) := V.transpose * F0 with hG
  set E : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) :=
    blk d k 1 ξ' * F0.map WittVector.frobenius - ξ' • G with hEdef
  have hVt : IsUnit V.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det V).1 hV
  have key : V.transpose⁻¹ * blk d k 1 ξ' * F0.map WittVector.frobenius - ξ' • F0 =
      V.transpose⁻¹ * E := by
    rw [hEdef, hG, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc (V.transpose⁻¹),
      Matrix.nonsing_inv_mul _ hVt, Matrix.one_mul]
  have hEe : ∀ j n, E j n = Sum.elim (fun _ => (1 : Ainf p O)) (fun _ => ξ') j *
      WittVector.frobenius (F0 j n) - ξ' * G j n := by
    intro j n
    simp [hEdef, blk, Matrix.diagonal_mul]
  have hyp : ∀ j n, μ ∣ WittVector.frobenius (F0 j n) -
      Sum.elim (fun _ => (p : Ainf p O)) (fun _ => 1) j * G j n := by
    intro j n
    have := hF j n
    rw [Matrix.mul_assoc, ← hG] at this
    simpa [blk, Matrix.diagonal_mul] using this
  have hE : ∀ j n, ξ' * μ ∣ E j n := by
    intro j n
    rw [hEe]
    rcases j with j | j
    · obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton').1
        (show F0 (Sum.inl j) n ∈ Ideal.span {xi ε} by
          rw [← AinfXi.ker_theta hv ε (root_prim hε)]; exact hθ j n)
      have h1 : μ ∣ ξ' * (WittVector.frobenius w - G (Sum.inl j) n) := by
        have := dvd_sub (hyp (Sum.inl j) n) ((mu_dvd_frob_xi_sub ε).mul_right (G (Sum.inl j) n))
        convert this using 1
        simp only [Sum.elim_inl]
        rw [← hw, map_mul, ← hξ']
        ring
      have h2 := mul_dvd_mul_left ξ' (mu_dvd_of_xi_mul F _ h1)
      convert h2 using 1
      simp only [Sum.elim_inl]
      rw [← hw, map_mul, ← hξ']
      ring
    · have := mul_dvd_mul_left ξ' (hyp (Sum.inr j) n)
      convert this using 1
      simp only [Sum.elim_inr]
      ring
  have e := congrFun (congrFun key i) m
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e
  rw [e, Matrix.mul_apply]
  exact Finset.dvd_sum fun j _ => (hE j m).mul_left _
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WinLift

theorem lift_solves_div_frob_xi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V G0 hP hθ i m
  have ent : ∀ (c : Ainf p O) (i : Fin d ⊕ Fin k) (m : Fin h),
      (V * blk d k c 1 * G0.map WittVector.frobenius) i m =
        ∑ l, V i l * (Sum.elim (fun _ => c) (fun _ => (1 : Ainf p O)) l *
          WittVector.frobenius (G0 l m)) := by
    intro c i m
    rw [Matrix.mul_apply]
    simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h1 : ∀ l, ∃ w : Ainf p O,
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l *
        WittVector.frobenius (G0 l m) = WittVector.frobenius (xi ε) * w := by
    rintro (l | l)
    · exact ⟨_, rfl⟩
    · have hmem : G0 (Sum.inr l) m ∈ RingHom.ker (WittVector.fontaineTheta O p) := hθ l m
      rw [AinfXi.ker_theta hv ε (root_prim hε), Ideal.mem_span_singleton'] at hmem
      obtain ⟨w, hw⟩ := hmem
      exact ⟨WittVector.frobenius w, by rw [← hw, map_mul]; simp; ring⟩
  choose w hw using h1
  have hE : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
      WittVector.frobenius (xi ε) * G0 i m =
        WittVector.frobenius (xi ε) * ((∑ l, V i l * w l) - G0 i m) := by
    rw [ent]
    simp_rw [hw]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hdiff : ∀ l : Fin d ⊕ Fin k, Sandwich.mu ε ∣
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
        Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l := by
    rintro (l | l)
    · exact mu_dvd_frob_xi_sub ε
    · simp
  have hmu : Sandwich.mu ε ∣
      (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m := by
    have hPim := hP i m
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hPim
    have key : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m -
        ((V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius) i m - (p : Ainf p O) * G0 i m) =
        (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
          Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
            WittVector.frobenius (G0 l m))) -
        (WittVector.frobenius (xi ε) - p) * G0 i m := by
      rw [ent, ent]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    have hR : Sandwich.mu ε ∣ (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε))
        (fun _ => (1 : Ainf p O)) l - Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
          WittVector.frobenius (G0 l m))) - (WittVector.frobenius (xi ε) - p) * G0 i m :=
      dvd_sub (Finset.dvd_sum fun l _ => Dvd.dvd.mul_left ((hdiff l).mul_right _) _)
        ((mu_dvd_frob_xi_sub ε).mul_right _)
    rw [← key] at hR
    have := dvd_add hR hPim
    rwa [sub_add_cancel] at this
  rw [hE] at hmu ⊢
  exact mul_dvd_mul_left _ (mu_dvd_of_xi_mul F _ hmu)

end GlobalTheory.WinLift
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem isNil_V_blk_frob_xi :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hUV hnil
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  apply isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a
  refine isNil_of_theta_eq p F.θ F.σ (Fact.out) F.σ_pow _ _ ?_ hnil
  intro i j
  have hU : F.θ (U i j) = F.θ (F.a (V i j)) := by
    obtain ⟨c, hc⟩ := hUV i j
    have h := congrArg F.θ hc
    rw [map_sub, map_mul, theta_tau F hv hε, zero_mul, sub_eq_zero] at h
    exact h
  simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
  rcases j with j | j
  · simp only [Sum.elim_inl, map_mul, map_natCast, hU, F.θ_a, theta_frob_xi hv hε]
  · simp only [Sum.elim_inr, map_mul, map_one, mul_one, hU]

end GlobalTheory.WinLift
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift.NilF

theorem map_inv_transpose_blk {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d k : ℕ)
    (M : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) (hM : IsUnit M) (a b : R) (i j : Fin d ⊕ Fin k) :
    f ((M.transpose⁻¹ * blk d k a b) i j) = (((M.map f).transpose)⁻¹ * blk d k (f a) (f b)) i j := by
  have hMt : IsUnit M.transpose := (Matrix.isUnit_iff_isUnit_det _).2
    (by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 hM)
  have hb : (blk d k a b).map f = blk d k (f a) (f b) := by
    rw [blk, blk, Matrix.diagonal_map (map_zero f)]
    congr 1
    funext l
    rcases l with l | l <;> rfl
  have := congr_fun (congr_fun (Matrix.map_mul (f := f) (L := M.transpose⁻¹)
    (M := blk d k a b)) i) j
  rw [Matrix.map_apply] at this
  rw [this, ← map_inv_of_isUnit f _ hMt, Matrix.transpose_map, hb]

theorem isNil_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hU hV hUV hN
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθτ := theta_tau F hv hε
  have hUV' : U.map F.θ = V.map (WittVector.fontaineTheta O p) := by
    refine Matrix.ext fun i j => ?_
    obtain ⟨c, hc⟩ := hUV i j
    rw [Matrix.map_apply, Matrix.map_apply, ← F.θ_a, ← sub_eq_zero, ← map_sub, hc, map_mul, hθτ,
      zero_mul]
  refine isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a _ ?_
  refine isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN
  rw [Matrix.map_apply, F.θ_a, map_inv_transpose_blk F.θ d k U hU, map_inv_transpose_blk _ d k V hV,
    hUV', map_one, map_one, map_natCast, theta_frob_xi hv hε]

end GlobalTheory.WinLift.NilF
end
end
