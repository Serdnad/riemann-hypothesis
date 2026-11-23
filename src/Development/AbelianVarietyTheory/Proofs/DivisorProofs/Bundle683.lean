module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalModuleActionLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoWindowsOfMatrixCongrModTau
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle646
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.TanInj

open GlobalTheory.UPel.HT.EtLev.TanKill

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

theorem core_inj {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (w0 : Ideal (𝓞 D.F))
    (hw : IsEtPlace b w0) [IsAlgClosed k] (β : R →+* k) (L : 𝓞 D.F →+* Module.End k V)
    (hlie : ∀ v, L D.ω v = β b.ρ • v → ∃ w : Fin D.a → V, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ v = ∑ i, w i)
    (c : 𝓞 D.F) (hc0 : c ≠ 0)
    (hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w)
    (v : V) (hv : L c v = 0) : v = 0 := by
  have hpr : p.Prime := Fact.out
  by_cases hp : (p : k) = 0
  swap
  ·
    set N := Ideal.absNorm (Ideal.span {c}) with hNdef
    have hNmem : ((N : ℕ) : 𝓞 D.F) ∈ Ideal.span {c} := Ideal.absNorm_mem _
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hNmem
    have hN0 : N ≠ 0 := by
      rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hc0
    obtain ⟨e, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hpr.one_lt.ne'
    have hN'u : IsUnit ((N' : ℕ) : R) := b.unit N' ((Nat.Prime.coprime_iff_not_dvd hpr).mpr hN').symm
    have hN'k : ((N' : ℕ) : k) ≠ 0 := by
      have := hN'u.map β
      rw [map_natCast] at this
      exact this.ne_zero
    have hNk : ((N : ℕ) : k) ≠ 0 := by
      rw [hNe, Nat.cast_mul, Nat.cast_pow]
      exact mul_ne_zero (pow_ne_zero _ hp) hN'k
    have h : L ((N : ℕ) : 𝓞 D.F) v = 0 := by
      rw [← hd, map_mul, Module.End.mul_apply, hv, map_zero]
    rw [L_nat] at h
    exact (smul_eq_zero.mp h).resolve_left hNk
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hpr).mpr hp
  set Tω := L D.ω with hTω
  set ρ1 := β b.ρ with hρ1
  set ρ2 := (D.tr : k) - ρ1 with hρ2
  have hquad : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    have hb : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
    have h := D.nm_eq
    rw [hb] at h
    linear_combination (-1 : 𝓞 D.F) * h
  have hq : ∀ u, Tω (Tω u) = (D.tr : k) • Tω u - (D.nm : k) • u := by
    intro u
    have h := congrArg (fun f => f u) (congrArg L hquad)
    simp only [map_add (f := _), map_sub, map_mul, map_zero, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, L_int] at h
    rw [← hTω] at h
    rw [← sub_eq_zero, ← h]
    abel
  have hρ : ρ1 ^ 2 - (D.tr : k) * ρ1 + (D.nm : k) = 0 := by
    have h := congrArg β b.ρ_root
    simpa using h
  have hsum : ρ1 + ρ2 = D.tr := by rw [hρ2]; ring
  have hprod : ρ1 * ρ2 = D.nm := by rw [hρ2]; linear_combination (-1 : k) * hρ
  clear_value Tω ρ1 ρ2
  have hδ : ρ1 - ρ2 ≠ 0 := by
    intro h0
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      have : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = (ρ1 - ρ2) ^ 2 := by
        push_cast
        rw [← hsum, ← hprod]; ring
      rw [this, h0]; ring
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).mp hd)
  have hcomm : ∀ c u, L c (Tω u) = Tω (L c u) := by
    intro c u
    rw [hTω, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  set v1 := (ρ1 - ρ2)⁻¹ • (Tω v - ρ2 • v) with hv1
  set v2 := (ρ1 - ρ2)⁻¹ • (ρ1 • v - Tω v) with hv2
  have hv12 : v = v1 + v2 := by
    rw [hv1, hv2, ← smul_add]
    have : Tω v - ρ2 • v + (ρ1 • v - Tω v) = (ρ1 - ρ2) • v := by rw [sub_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have e1 : Tω v1 = ρ1 • v1 := by
    rw [hv1, map_smul, map_sub, map_smul, hq, smul_comm ρ1]
    congr 1
    rw [← hsum, ← hprod]
    module
  have e2 : Tω v2 = ρ2 • v2 := by
    rw [hv2, map_smul, map_sub, map_smul, hq, smul_comm ρ2]
    congr 1
    rw [← hsum, ← hprod]
    module
  have k1 : L c v1 = 0 := by
    rw [hv1, map_smul, map_sub, map_smul, hcomm, hv, map_zero, smul_zero, sub_zero, smul_zero]
  have k2 : L c v2 = 0 := by
    rw [hv2, map_smul, map_sub, map_smul, hcomm, hv, map_zero, smul_zero, sub_zero, smul_zero]
  have hp0 : ((p : ℕ) : 𝓞 D.F) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have z1 : v1 = 0 := by
    have hne : ∀ i, β (b.t i c) ≠ 0 := by
      intro i h0
      have hprime : (RingHom.ker (β.comp (b.t i))).IsPrime := RingHom.ker_isPrime _
      have hpP : ((p : ℕ) : 𝓞 D.F) ∈ RingHom.ker (β.comp (b.t i)) := by
        rw [RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast, hp]
      have hbot : RingHom.ker (β.comp (b.t i)) ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hpP
        exact hp0 hpP
      have hmax : (RingHom.ker (β.comp (b.t i))).IsMaximal := hprime.isMaximal hbot
      have hnw : RingHom.ker (β.comp (b.t i)) ≠ w0 := by
        intro hP
        have hle : Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) ≤ RingHom.ker β := by
          refine Ideal.span_le.mpr ?_
          rintro _ ⟨y, hy, rfl⟩
          have : y ∈ RingHom.ker (β.comp (b.t i)) := hP ▸ hy
          exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp this)
        rw [hw.2.2.1 i, top_le_iff] at hle
        exact RingHom.ker_ne_top β hle
      exact hcw _ hmax hpP hnw (RingHom.mem_ker.mpr h0)
    obtain ⟨w, hwe, hweq⟩ := hlie v1 e1
    rw [hweq]
    refine sum_eq_zero_of_eigen (L c) Finset.univ w (fun i => β (b.t i c)) (fun i _ => hwe i c)
      (fun i _ => hne i) ?_
    rw [← hweq]; exact k1
  have z2 : v2 = 0 := by
    obtain ⟨r0, hr0⟩ := D.split
    have hr0k : ((r0 : k) - ρ1) * ((r0 : k) - ρ2) = 0 := by
      have : ((r0 ^ 2 - D.tr * r0 + D.nm : ℤ) : k) = 0 := (CharP.intCast_eq_zero_iff k p _).mpr hr0
      push_cast at this
      linear_combination this - (r0 : k) * hsum + hprod
    obtain ⟨r2, hr2⟩ : ∃ r2 : ℤ, (r2 : k) = ρ2 := by
      rcases mul_eq_zero.mp hr0k with h | h
      · exact ⟨D.tr - r0, by push_cast; rw [hρ2]; linear_combination -h⟩
      · exact ⟨r0, by linear_combination h⟩
    obtain ⟨c', hc', e', f', hcef'⟩ := exists_mem_pow_add_eq_one p D R b w0 1 hw k β r2 (by rw [hr2, hρ2, hρ1])
    rw [pow_one] at hc'
    let J : Ideal (𝓞 D.F) := Ideal.span {D.ω - (r2 : 𝓞 D.F), ((p : ℕ) : 𝓞 D.F)}
    have hJ : Ideal.span {c} ⊔ J = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      have hJm : J ≤ m := le_trans le_sup_right hle
      have hωm : D.ω - (r2 : 𝓞 D.F) ∈ m := hJm (Ideal.subset_span (Set.mem_insert _ _))
      have hpm : ((p : ℕ) : 𝓞 D.F) ∈ m := hJm (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      have hcm : c ∈ m := le_trans le_sup_left hle (Ideal.mem_span_singleton_self c)
      have hmw : m ≠ w0 := by
        intro hmw
        subst hmw
        have h1 : (1 : 𝓞 D.F) ∈ m := by
          rw [← hcef']
          exact m.add_mem (m.add_mem hc' (m.mul_mem_left _ hωm)) (m.mul_mem_left _ hpm)
        exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      exact hcw m hm hpm hmw hcm
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.mp (hJ ▸ Submodule.mem_top : (1 : 𝓞 D.F) ∈ Ideal.span {c} ⊔ J)
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨e, f, hef⟩ := Ideal.mem_span_pair.mp hj
    have h := congrArg (fun g => g v2) (congrArg L haj)
    rw [← hef] at h
    simp only [map_add (f := _), map_mul, map_sub, map_one, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, L_int, L_nat, k2] at h
    rw [← hTω, e2, hr2, sub_self] at h
    simp only [hp, zero_smul, map_zero, zero_add, add_zero] at h
    exact h.symm
  rw [hv12, z1, z2, add_zero]

end GlobalTheory.UPel.HT.EtLev.TanInj

namespace GlobalTheory.UPel.HT.EtLev.TanInj

open GlobalTheory.TanPtMod

theorem tan_eq_one_of_notMem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F), c ≠ 0 → (∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) → ∀ v : epsPtR x ⟶ o.A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 → v = 1 := by
  intro p _ D R _ b N w0 hw S s o k _ _ x c hc0 hcw v hv0 hv
  set β : R →+* k := (Spec.preimage (x ≫ s)).hom with hβ
  have hx : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let L : 𝓞 D.F →+* Module.End k (Tan x o.A) := (actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  have hL : ∀ c (u : Tan x o.A), (L c u).hom = u.hom ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := fun _ _ => rfl
  have hlie : ∀ u : Tan x o.A, L D.ω u = β b.ρ • u →
      ∃ w : Fin D.a → Tan x o.A, (∀ i c, L c (w i) = β (b.t i c) • w i) ∧ u = ∑ i, w i := by
    intro u hu
    obtain ⟨w, hw1, hw2⟩ := o.lie k β x hx u.hom
      ⟨(mem_tanSub_iff x o.A _).mp u.hom_mem, by
        have := congrArg (fun t : Tan x o.A => t.hom.left) hu
        simpa [hL, GrpTangentPt.epsScalePt_left] using this⟩
    have hmem : ∀ i, w i ∈ tanSub x o.A := fun i => (mem_tanSub_iff x o.A _).mpr (hw1 i 0).1
    refine ⟨fun i => Tan.mk (w i) (hmem i), fun i c => Tan.ext (Over.OverMorphism.ext ((hw1 i c).2)), ?_⟩
    refine Tan.ext ?_
    rw [Tan.hom_sum, hw2, List.prod_ofFn]
    rfl
  have hmv : v ∈ tanSub x o.A := (mem_tanSub_iff x o.A _).mpr hv0
  have := core_inj D b w0 hw β L hlie c hc0 hcw (Tan.mk v hmv) (Tan.ext (by rw [hL]; exact hv))
  exact congrArg Tan.hom this

end GlobalTheory.UPel.HT.EtLev.TanInj
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_ainf_solution_of_approx_mod_phi_xi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := by
  first | exact @GlobalTheory.WTop.main | exact GlobalTheory.WTop.main | (intros; apply GlobalTheory.WTop.main <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.frobXi_eigenvector_eq_of_frame_image_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := by
  first | exact @GlobalTheory.WinLift.eigen_eq_of_frame_eq | exact GlobalTheory.WinLift.eigen_eq_of_frame_eq | (intros; apply GlobalTheory.WinLift.eigen_eq_of_frame_eq <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.theta_eval_eq_zeta_pow_digit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ (t : G.Tate) (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → (∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N) → ∀ E : MvPowerSeries (Fin d) F.B →ₐ[F.B] F.B, IsEval p z E → F.θ (E g) = zeta ε n ^ GlobalTheory.PDiv.digit n (epsPairing hε G t χ) := by
  first | exact @GlobalTheory.QLogPeriod.theta_eval_char | exact GlobalTheory.QLogPeriod.theta_eval_char | (intros; apply GlobalTheory.QLogPeriod.theta_eval_char <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.SmallFirst

theorem coeff_single_frob {Q : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {d : ℕ}
    (f : MvPowerSeries (Fin d) Q) (i : Fin d) :
    coeff (Finsupp.single i p) (frob p s f) = s (lin f i) := by
  have h1 : frob p s f = expand p hp (map s f) := by
    rw [frob, expand, substAlgHom_apply]
  have h2 : (Finsupp.single i p : Fin d →₀ ℕ) = p • Finsupp.single i 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, h2, coeff_expand_smul, coeff_map, lin]

theorem coeff_comb {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ l, algebraMap B Q (b l) * coeff α (e l) := by
  unfold comb

  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MvPowerSeries.coeff_smul]

end GlobalTheory.QLog.SmallFirst

theorem GlobalTheory.QLog.small_first_of_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) → ∀ i, ¬IsUnit (F.θ (w (Sum.inl i))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU w hw i
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set J : Ideal F.B := Ideal.comap F.θ (IsLocalRing.maximalIdeal O) with hJ
  have memJ : ∀ x, x ∈ J ↔ ¬IsUnit (F.θ x) := fun x => by
    rw [hJ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpJ : (p : F.B) ∈ J := by
    rw [memJ, map_natCast]; exact Fact.out
  haveI hJp : J.IsPrime := Ideal.IsPrime.comap F.θ
  set α : Fin d →₀ ℕ := Finsupp.single i p with hα

  have hc : ∀ l, ∃ cl : F.B, (p : F.Q) * coeff α (e l) = algebraMap F.B F.Q cl := by
    intro l
    obtain ⟨b, -, hb⟩ := GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hlift ⊤ (e l) (hbas.1 l) α i
    refine ⟨b, ?_⟩
    rw [← hb, hα, Finsupp.single_eq_same]
  choose cc hcc using hc
  have key : ∀ m, algebraMap F.B F.Q (∑ l, U l m * cc l) =
      (p : F.Q) * ∑ l, algebraMap F.B F.Q (U l m) * coeff α (e l) := by
    intro m

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← hcc]; ring
  have hcol : ∀ m l, (U * blk d k (p : F.B) 1) l m = U l m * Sum.elim (fun _ => (p : F.B)) (fun _ => 1) m := by
    intro m l
    rw [blk, Matrix.mul_diagonal]
  have hR : ∀ m, (∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0) ∈ J := by
    intro m
    cases m with
    | inl i' =>
      obtain ⟨t, ht, hteq⟩ := (hU (Sum.inl i')).2 i' rfl α
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 ht
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, (hadp i').2, SmallFirst.coeff_comb] at hteq
      have hs : F.s (Pi.single (M := fun _ : Fin d => F.Q) i' 1 i) =
          algebraMap F.B F.Q (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0) := by
        by_cases h : i' = i
        · subst h; simp
        · have h' : i ≠ i' := Ne.symm h
          simp [Pi.single_apply, h', h]
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inl i')) * coeff α (e l) =
          algebraMap F.B F.Q (∑ l, U l (Sum.inl i') * cc l) := by
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inl, map_mul, map_natCast]; ring
      rw [hs, hsum, ← map_sub] at hteq
      have := F.frame.inj hteq
      have h2 : (∑ l, U l (Sum.inl i') * cc l) - (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0)
          = -(t' * p) := by rw [← this]; ring
      rw [h2]
      exact J.neg_mem (J.mul_mem_left _ hpJ)
    | inr j =>
      obtain ⟨b, -, hb⟩ := (hbas.1 (Sum.inr j)).2.1 i
      obtain ⟨t, -, hteq⟩ := (hU (Sum.inr j)).1 α
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, hb, F.s_alg, SmallFirst.coeff_comb] at hteq
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inr j)) * coeff α (e l) =
          ∑ l, algebraMap F.B F.Q (U l (Sum.inr j)) * coeff α (e l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inr, mul_one]
      rw [hsum] at hteq
      have h3 : algebraMap F.B F.Q (∑ l, U l (Sum.inr j) * cc l) =
          algebraMap F.B F.Q ((p : F.B) * (F.σ b - t)) := by
        rw [key, map_mul, map_sub, map_natCast, ← hteq]; ring
      have h4 := F.frame.inj h3
      have hne : (Sum.inr j : Fin d ⊕ Fin k) ≠ Sum.inl i := Sum.inr_ne_inl
      rw [if_neg hne, sub_zero, h4]
      exact J.mul_mem_right _ hpJ

  have hW : ∑ m, F.σ (w m) * ∑ l, U l m * cc l ∈ J := by
    have : ∑ m, F.σ (w m) * ∑ l, U l m * cc l = ∑ l, U.mulVec (fun j => F.σ (w j)) l * cc l := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [this]
    exact J.sum_mem fun l _ => J.mul_mem_right _ ((memJ _).2 (hw l))
  have hD : ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) ∈ J :=
    J.sum_mem fun m _ => J.mul_mem_left _ (hR m)
  have hσ : F.σ (w (Sum.inl i)) ∈ J := by
    have : F.σ (w (Sum.inl i)) = (∑ m, F.σ (w m) * ∑ l, U l m * cc l) -
        ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [this]
    exact J.sub_mem hW hD
  obtain ⟨z, hz⟩ := F.σ_pow (w (Sum.inl i))
  have hpow : w (Sum.inl i) ^ p ∈ J := by
    have : w (Sum.inl i) ^ p = F.σ (w (Sum.inl i)) - p * z := by rw [← hz]; ring
    rw [this]
    exact J.sub_mem hσ (J.mul_mem_right _ hpJ)
  exact (memJ _).1 (hJp.mem_of_pow_mem p hpow)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.isIso_windows_of_matrix_congr_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U U' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsUnit U' → (∀ i j, F.τ ∣ U i j - U' i j) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → ∃ X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) ∧ X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ := by
  first | exact @GlobalTheory.WindowIso.window_iso | exact GlobalTheory.WindowIso.window_iso | (intros; apply GlobalTheory.WindowIso.window_iso <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.ChartRed

def twoRing {R R' A A' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} [CommRing A]
    [Bialgebra R A] [CommRing A'] [Bialgebra R' A'] (f : SemiBialgHom σ A A') :
    A ⊗[R] A →+* A' ⊗[R'] A' where
  toFun := f.two
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    simp only [Algebra.TensorProduct.one_def, TensorProduct.map_tmul, SemiBialgHom.lin_apply,
      map_one f.toRingHom]
  map_mul' x y := by
    induction x with
    | add a b ha hb => simp only [add_mul, map_add (f := _), ha, hb]
    | tmul a b =>
      induction y with
      | add u v hu hv => simp only [mul_add, map_add (f := _), hu, hv]
      | tmul u v => simp [SemiBialgHom.lin_apply, map_mul f.toRingHom]

theorem ev₂_map {p m d : ℕ} {O k : Type} [CommRing O] [CommRing k] {r : O →+* k}
    {G : PDivGroup p O} {G' : PDivGroup p k} (s : SemiHom r G' G) (c : QLog.Chart G d)
    (c' : Katz.Chart G' d) (hc : ∀ n i, c'.x n i = s.app n (c.x n i)) (hp : (p : k) ^ m = 0)
    (n : ℕ) (f : MvPowerSeries (Fin d ⊕ Fin d) O) :
    c'.ev₂ n (map r f) = (s.app n).two (c.ev₂ n f) := by
  have e : (fun i => twoRing (s.app n)
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] 1) (fun i => 1 ⊗ₜ[O] c.x n i) i)) = c'.x₂ n := by
    funext i
    cases i with
    | inl i =>
      change (s.app n) (c.x n i) ⊗ₜ[k] (s.app n) 1 = c'.x n i ⊗ₜ[k] 1
      rw [map_one, hc]
    | inr i =>
      change (s.app n) 1 ⊗ₜ[k] (s.app n) (c.x n i) = 1 ⊗ₜ[k] c'.x n i
      rw [map_one, hc]
  have h := T.map_eval_eq_evA_map_of_isEval_of_pow_eq_zero p m O _ k (G'.A n ⊗[k] G'.A n) _ _ _ (c.isEval₂ n) r (twoRing (s.app n))
    (fun a => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        ← map_one (twoRing (s.app n))]
      exact map_smulₛₗ (s.app n).two a 1)
    (by rw [← map_natCast (algebraMap k _), ← map_pow, hp, map_zero])
    (fun i => (congrFun e i).symm ▸ c'.nil₂ n i) f
  refine Eq.trans ?_ h.symm
  unfold Katz.Chart.ev₂
  congr 2
  exact e.symm

theorem exists_chart : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ c' : Katz.Chart (G.baseChange (O ⧸ I)) d, c'.IsLawOf (fun i => map (Ideal.Quotient.mk I) (c.μ i)) ∧ (∀ n f, c'.ev n (map (Ideal.Quotient.mk I) f) = (G.toBase (O ⧸ I)).app n (c.ev n f)) ∧ ∀ n s, c'.ev₂ n (map (Ideal.Quotient.mk I) s) = ((G.toBase (O ⧸ I)).app n).two (c.ev₂ n s) := by
  intro p _ O _ G d c I m hm
  obtain ⟨hx, h1, h2⟩ := T.formalChart_presents_levels_mod_ideal p O G d c I m hm
  have hp : (p : O ⧸ I) ^ m = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  let c' : Katz.Chart (G.baseChange (O ⧸ I)) d :=
    { x := fun n i => (G.toBase (O ⧸ I)).app n (c.x n i)
      nil := hx
      res := fun n i => ((G.toBase (O ⧸ I)).res_app n _).trans (congrArg _ (c.res n i))
      aug := fun n i => by rw [((G.toBase (O ⧸ I)).app n).counit_map, c.aug, map_zero]
      presents := h2 }
  have h3 := ev₂_map (G.toBase (O ⧸ I)) c c' (fun _ _ => rfl) hp
  refine ⟨c', fun n i => ?_, h1, h3⟩
  exact (h3 n (c.μ i)).trans ((congrArg _ (c.comul n i)).trans
    (((G.toBase (O ⧸ I)).app n).two_comul _))

end GlobalTheory.QLog.ChartRed
end
end
