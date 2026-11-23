module

public import GroundTheory.PAdicHodge.ACrisBdR
public import GroundTheory.PAdicHodge.Bundle003
public import GroundTheory.PAdicHodge.TiltAlgebra
public import GroundTheory.PAdicHodge.Bundle001
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝔸" => Localization.Away (p : AInf K p)

theorem mem_acrisZero_of_forall_dvd {z : 𝔸}
    (h : ∀ m : ℕ, ∃ s ∈ ACrisZero K p, algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) ∣ z - s) :
    z ∈ ACrisZero K p := by
  obtain ⟨N, w, hwN⟩ := IsLocalization.Away.surj (p : AInf K p) z
  rw [map_natCast] at hwN
  set m := p ^ N with hm
  have hm0 : m ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  obtain ⟨s, hs, r, hr⟩ := h m
  obtain ⟨s', hs', w', r', hw', hr'⟩ := exists_decomp ker_eq_span_xiGen m hs
  set ξm := algebraMap (AInf K p) 𝔸 (xiGen K p ^ m)
  have hz : z = s' + ξm * (r + r') := by
    rw [show z = s + (z - s) by ring, hr, hr']; ring
  have hfac : ((m.factorial : ℕ) : 𝔸) = (p : 𝔸) ^ N * ((m - 1).factorial : 𝔸) := by
    rw [← Nat.mul_factorial_pred hm0, Nat.cast_mul, hm, Nat.cast_pow]

  have hW : ξm * ((m.factorial : 𝔸) * (r + r')) =
      algebraMap (AInf K p) 𝔸 (((m - 1).factorial : AInf K p) * w - (p : AInf K p) ^ N * w') := by
    have e1 : ξm * (r + r') = z - s' := by rw [hz]; ring
    rw [map_sub, map_mul, map_mul, map_pow, map_natCast, map_natCast, ← hw', ← hwN, hfac]
    linear_combination ((p : 𝔸) ^ N * ((m - 1).factorial : 𝔸)) * e1
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 ((algebraMap_dvd_iff m _).1 ⟨_, hW.symm⟩)
  have hnz : xiGen K p ^ m ∈ nonZeroDivisors (AInf K p) :=
    pow_mem (IsPerfectoidField.mem_nonZeroDivisors_of_ker_eq_span ker_eq_span_xiGen) m
  have hR : (m.factorial : 𝔸) * (r + r') = algebraMap (AInf K p) 𝔸 d := by
    have h0 : algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) * ((m.factorial : 𝔸) * (r + r') -
        algebraMap (AInf K p) 𝔸 d) = 0 := by
      rw [mul_sub, hW, ← map_mul, ← hd, mul_comm, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_algebraMap_mul_eq_zero hnz h0)
  have hxi : ξm * (r + r') = dpow m (xiGen K p) * algebraMap (AInf K p) 𝔸 d := by
    rw [← hR, ← mul_assoc, mul_comm (dpow m (xiGen K p)), factorial_mul_dpow, ← map_pow]
  have hξmem : xiGen K p ∈ RingHom.ker (fontaineTheta (normInteger K) p) := by
    rw [ker_eq_span_xiGen]; exact Ideal.mem_span_singleton_self _
  rw [hz, hxi]
  exact add_mem hs' (Subalgebra.mul_mem _ (dpow_mem hξmem m) (Subalgebra.algebraMap_mem _ d))

theorem iotaM_eq_zero {y : ACris K p} (hy : iota K p y = 0) (m : ℕ) : embedding₂ K p m y = 0 := by
  have h := evalₐ_iota (K := K) (p := p) m y
  have h0 : @Eq (_root_.AdicCompletion (kerAway K p) 𝔸) (iota K p y) 0 := hy
  rw [h0, map_zero] at h
  exact Subtype.ext h.symm

theorem span_p_pow_map (k : ℕ) :
    (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p)) =
      Ideal.span {(p : ACris K p)} ^ k := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]



theorem exists_eq_pow_mul_of_iota_eq_zero {y : ACris K p} (hy : iota K p y = 0) {k : ℕ}
    {yk : ACrisZero K p}
    (ha : y - _root_.AdicCompletion.of _ _ yk ∈
      (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p))) :
    ∃ z ∈ ACrisZero K p, (yk : 𝔸) = (p : 𝔸) ^ k * z := by
  have hu := isUnit_natCast (K := K) (p := p) hp.out.ne_zero
  refine ⟨↑(hu.unit⁻¹ ^ k) * (yk : 𝔸), ?_, ?_⟩
  · refine mem_acrisZero_of_forall_dvd fun m => ?_

    have h1 : embedding₂ K p m (y - _root_.AdicCompletion.of _ _ yk) ∈ Ideal.span {(p : acrisQ K p m)} ^ k := by
      have hle : (Ideal.span {(p : ACrisZero K p)} ^ k).map
          ((embedding₂ K p m).comp (algebraMap (ACrisZero K p) (ACris K p))) ≤
          Ideal.span {(p : acrisQ K p m)} ^ k := by
        rw [Ideal.map_le_iff_le_comap]
        refine (Ideal.pow_right_mono ?_ k).trans (Ideal.le_comap_pow _ k)
        rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
        exact Ideal.mem_span_singleton_self _
      apply hle
      rw [← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ ha
    rw [RingHom.map_sub, iotaM_eq_zero hy, zero_sub, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨t, ht⟩ := h1
    obtain ⟨s, hs, hst⟩ := t.2
    have h3 := congrArg (fun x : acrisQ K p m => (x : 𝔸 ⧸ kerAway K p ^ m)) ht
    simp only [NegMemClass.coe_neg, SubringClass.coe_natCast, SubmonoidClass.coe_pow,
      MulMemClass.coe_mul] at h3
    rw [embedding₂, AdicCompletion.extendRingHom_of, coe_iotaZero, ← hst] at h3
    refine ⟨-s, neg_mem hs, ?_⟩
    have h4 : Ideal.Quotient.mk (kerAway K p ^ m) ((yk : 𝔸) - (p : 𝔸) ^ k * (-s)) = 0 := by
      rw [map_sub, map_mul, map_pow, map_natCast, map_neg, mul_neg, sub_neg_eq_add, ← h3,
        add_neg_cancel]
    rw [mk_eq_zero_iff] at h4
    have h5 : (yk : 𝔸) - (p : 𝔸) ^ k * (-s) =
        (p : 𝔸) ^ k * (↑(hu.unit⁻¹ ^ k) * (yk : 𝔸) - -s) := by
      rw [mul_sub, ← mul_assoc, Units.val_pow_eq_pow_val, ← mul_pow, IsUnit.mul_val_inv, one_pow,
        one_mul]
    rw [h5] at h4
    exact ((hu.pow k).dvd_mul_left).1 h4
  · rw [← mul_assoc, Units.val_pow_eq_pow_val, ← mul_pow, IsUnit.mul_val_inv, one_pow, one_mul]



theorem iota_injective : Function.Injective (iota K p) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  refine IsHausdorff.haus' (I := Ideal.span {(p : ACris K p)}) y fun k => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, ← span_p_pow_map]

  obtain ⟨yk, hyk⟩ := Ideal.Quotient.mk_surjective
    (_root_.AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) k y)
  have hker : y - _root_.AdicCompletion.of _ _ yk ∈
      (Ideal.span {(p : ACrisZero K p)} ^ k).map
        (algebraMap (ACrisZero K p) (ACris K p)) := by
    rw [← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _), RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.map_sub]
    rw [← hyk]
    exact sub_eq_zero.2 (_root_.AdicCompletion.evalₐ_of _ k yk).symm
  obtain ⟨z, hz, hzk⟩ := exists_eq_pow_mul_of_iota_eq_zero hy hker
  have hyk' : yk ∈ Ideal.span {(p : ACrisZero K p)} ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨⟨z, hz⟩, Subtype.ext (by simpa using hzk)⟩
  have := add_mem hker (Ideal.mem_map_of_mem (algebraMap (ACrisZero K p) (ACris K p)) hyk')
  rwa [show (algebraMap (ACrisZero K p) (ACris K p)) yk = _root_.AdicCompletion.of _ _ yk from rfl,
    sub_add_cancel] at this

end ACris

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace AInf

section Functor

variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M]
  [IsUltrametricDist M]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]


variable (p) in
def map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : AInf K p →+* AInf L p :=
  WittVector.map (preTiltMap p φ hφ)

theorem map_coeff (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : AInf K p) (n : ℕ) :
    (map p φ hφ x).coeff n = preTiltMap p φ hφ (x.coeff n) :=
  WittVector.map_coeff _ _ _

theorem map_teichmuller (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : PreTilt (normInteger K) p) :
    map p φ hφ (WittVector.teichmuller p x) = WittVector.teichmuller p (preTiltMap p φ hφ x) :=
  WittVector.map_teichmuller p _ x

theorem fontaineTheta_map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (w : AInf K p) :
    WittVector.fontaineTheta (normInteger L) p (map p φ hφ w) =
      integerMap φ hφ (WittVector.fontaineTheta (normInteger K) p w) :=
  fontaineTheta_map_preTiltMap φ hφ w

theorem map_congr {φ ψ : K →+* L} (h : φ = ψ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    map p φ hφ = map p ψ hψ := by
  subst h; rfl

theorem map_comp (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (ψ : L →+* M) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    map p (ψ.comp φ) (norm_comp_eq hφ hψ) = (map p ψ hψ).comp (map p φ hφ) := by
  refine RingHom.ext fun x => WittVector.ext fun n => ?_
  rw [RingHom.comp_apply, map_coeff, map_coeff, map_coeff, preTiltMap_comp, RingHom.comp_apply]

theorem preTiltMap_id (x : PreTilt (normInteger K) p) :
    preTiltMap p (RingHom.id K) (fun _ => rfl) x = x := by
  refine Perfection.ext fun n => ?_
  rw [coeff_preTiltMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Perfection.coeff (ModP (normInteger K) p) p n x)
  rw [← ha, modPMap_mk]
  congr 1

theorem map_id : map p (RingHom.id K) (fun _ => rfl) = RingHom.id (AInf K p) := by
  refine RingHom.ext fun x => WittVector.ext fun n => ?_
  rw [map_coeff, preTiltMap_id, RingHom.id_apply]

theorem map_frobeniusEquiv (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : AInf K p) :
    map p φ hφ (WittVector.frobeniusEquiv p _ x) = WittVector.frobeniusEquiv p _ (map p φ hφ x) := by
  refine WittVector.ext fun n => ?_
  rw [map_coeff, WittVector.frobeniusEquiv_coeff, WittVector.frobeniusEquiv_coeff, map_coeff,
    map_pow]




end Functor

section Galois

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem norm_galCp_toRingHom (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    ‖(galCp σ : ℂ_[p] →+* ℂ_[p]) x‖ = ‖x‖ :=
  norm_galCp σ x

def galMap (σ : Gal(PadicAlgCl p/K)) : AInf ℂ_[p] p →+* AInf ℂ_[p] p :=
  map p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ)

theorem galMap_one : galMap (1 : Gal(PadicAlgCl p/K)) = RingHom.id _ := by
  rw [galMap, ← map_id]
  exact map_congr (RingHom.ext fun x => by rw [galCp_one]; rfl) _ _

theorem galMap_mul (σ τ : Gal(PadicAlgCl p/K)) : galMap (σ * τ) = (galMap σ).comp (galMap τ) := by
  rw [galMap, galMap, galMap, ← map_comp]
  exact map_congr (RingHom.ext fun x => by rw [galCp_mul]; rfl) _ _

instance instMulSemiringActionGal : MulSemiringAction Gal(PadicAlgCl p/K) (AInf ℂ_[p] p) where
  smul σ x := galMap σ x
  one_smul x := by
    change galMap 1 x = x
    rw [galMap_one, RingHom.id_apply]
  mul_smul σ τ x := by
    change galMap (σ * τ) x = galMap σ (galMap τ x)
    rw [galMap_mul, RingHom.comp_apply]
  smul_zero σ := map_zero (galMap σ)
  smul_add σ := map_add (galMap σ)
  smul_one σ := map_one (galMap σ)
  smul_mul σ := map_mul (galMap σ)

theorem gal_smul_def (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) : σ • x = galMap σ x := rfl

theorem gal_smul_coeff (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) (n : ℕ) :
    (σ • x).coeff n = preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) (x.coeff n) :=
  map_coeff _ _ x n

theorem gal_smul_teichmuller (σ : Gal(PadicAlgCl p/K)) (x : PreTilt (normInteger ℂ_[p]) p) :
    σ • (WittVector.teichmuller p x : AInf ℂ_[p] p) =
      WittVector.teichmuller p (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) x) :=
  map_teichmuller _ _ x

theorem coe_untilt_gal (σ : Gal(PadicAlgCl p/K)) (x : PreTilt (normInteger ℂ_[p]) p) :
    ((PreTilt.untilt (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) x) :
      normInteger ℂ_[p]) : ℂ_[p]) = σ • ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [untilt_preTiltMap, coe_integerMap]
  rfl

theorem fontaineTheta_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    ((WittVector.fontaineTheta (normInteger ℂ_[p]) p (σ • x) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((WittVector.fontaineTheta (normInteger ℂ_[p]) p x : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [gal_smul_def, galMap, fontaineTheta_map, coe_integerMap]
  rfl

theorem gal_smul_frobeniusEquiv (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    σ • WittVector.frobeniusEquiv p _ x = WittVector.frobeniusEquiv p _ (σ • x) :=
  map_frobeniusEquiv _ _ x

end Galois

end AInf

end GroundTheory.PAdicHodge
end
end
