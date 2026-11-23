module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalToGlobal.InertKernelTheory.KernelDifferenceOfFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero

@[expose] public section

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator GlobalTheory.LastSteps

noncomputable section

namespace GlobalTheory.ColPeriod.TopTwist

theorem valuation_le_one_of_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {k : ℕ}
    (hk : k ≠ 0) (h : x ^ k = 1) : w.valuation K x ≤ 1 := by
  by_contra hn
  have h1 := one_lt_pow₀ (not_le.1 hn) hk
  rw [← map_pow, h, map_one] at h1
  exact lt_irrefl _ h1

section Phi

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem qOf_nat_ne_zero : qOf P ≠ 0 := fun h => (qOf_ne_zero (P := P)) (by rw [h, Nat.cast_zero])

omit [StarRing E] in
theorem qOf_pred_ne_zero : qOf P - 1 ≠ 0 := by
  intro h
  have h0 := qOf_nat_ne_zero (P := P)
  have h1 : qOf P = 1 := by omega
  have h2 := qOf_mem (P := P)
  rw [h1, Nat.cast_one] at h2
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

omit [StarRing E] in
theorem valuation_PhiQ [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (q k₀ r c' n' c n : ℕ)
    (x : HomE E (n' + c') (n + c)) : w.valuation K (LocE.PhiQ q ξ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ LocE.unitV
  split_ifs
  · exact valuation_le_one_of_pow w qOf_pred_ne_zero (char_pow ξ _)
  · simp
  · simp

theorem PhiQ_add (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r c' n' c n : ℕ} (h1 : r ≤ n' + c') (h2 : r ≤ n + c)
    (x z : HomE E (n' + c') (n + c)) (hz : z ∈ homS (LocE.lamY P (qOf P) n' c' 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • z) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  have hZ := entB_int k₀ hz
  unfold LocE.PhiQ
  rw [entB_add_smul]
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 z = Z at hZ
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 x = M
  have e1 := fun a p p' => intAt_add_q (a := a) (hZ p p')
  have e2 := fun a p p' => intAt_add_q_div (a := a) (hZ p p')
  refine ite_eq_ite_zero (by simp only [e1, e2]) fun h => ?_
  exact _root_.GlobalTheory.LastSteps.unitV_congr _ (redP_det_add_q (fun s s' => h.1 _ _ (by have := s.2; omega) (by have := s'.2; omega)) fun _ _ => hZ _ _)

end Phi

section Psi

variable {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB}

theorem psi_add_int' (hc : c.Ok) (P : SB) {a b : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) (hb : IntAt P.1 b) :
    c.psi P (a + b) = c.psi P a := by
  rw [hc.psi_add P a b ha ((intAt_pow (intAt_nat _) _).mul hb), hc.psi_int P b hb, mul_one]

theorem psi_pow (hc : c.Ok) (P : SB) {a : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) :
    c.psi P a ^ (qOf P.1 ^ c.D P) = 1 := by
  have h : ∀ k : ℕ, c.psi P a ^ k = c.psi P ((k : X.E) * a) := fun k => by
    induction k with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, hc.psi_int P 0 intAt_zero]
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ ha]
      rw [mul_left_comm]
      exact (intAt_nat _).mul ha
  rw [h, Nat.cast_pow, hc.psi_int P _ ha]

end Psi

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_arg (P : rowSG Pr sel mu) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E)
    (h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η y)) := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hD
  have h1 := (inDual_iff (((qOf P.1 : X.E) ^ cst.M) • η)).2 h _ hy
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
  rw [hk]
  ring

theorem valuation_ftY (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) :
    w.valuation X.K (ftY sel mu cst P η y) ≤ 1 := by
  unfold ftY
  rw [if_neg hP]
  split_ifs with h
  · have h2 : w.valuation X.K (algebraMap (𝓞 X.K) X.K (qOf P.1 : 𝓞 X.K)) = 1 :=
      (w.valuation_eq_one_iff_notMem (K := X.K)).2 hw
    rw [map_natCast] at h2
    rw [map_mul, map_inv₀, map_pow, h2, one_pow, inv_one, one_mul]
    exact valuation_le_one_of_pow w (pow_ne_zero _ qOf_nat_ne_zero) (psi_pow hc P (intAt_arg sel mu cst P hD hy η h))
  · simp

theorem ftY_add (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η z : Sp X.E n →ₗ[X.E] X.E) (hz : InDual P.1 z) :
    ftY sel mu cst P (η + ((qOf P.1 : X.E) ^ cst.B) • z) y = ftY sel mu cst P η y := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  have hz' := (inDual_iff z).1 hz
  unfold ftY
  simp only [if_neg hP]
  refine ite_eq_ite_zero (forall_congr' fun i => ?_) fun h => ?_
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add]
    exact intAt_add_iff ((intAt_pow (intAt_nat _) _).mul ((intAt_pow (intAt_nat _) _).mul (hz' i)))
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add,
      psi_add_int' hc P (intAt_arg sel mu cst P hD hy η h)]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc.M_le_B
    have h1 := hz _ hy
    rw [map_smul, smul_eq_mul] at h1
    convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
    rw [hk]
    ring

theorem frsF_mem' {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : Sp X.E (R.N j)) : frsF sel mu p P x ∈ localization₂ P.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  classical
  unfold frsF
  rw [dite_eq_right hP]
  have h : ∀ Q : QE sel (mu : Chr X.F X.E X.K), p.fr Q x ∈ localization₂ Q.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) Q.1 :=
    fun Q => p.2 Q x
  exact h ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩

theorem pow_smul_repY {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) : ((qOf P.1 : X.E) ^ cst.M) • repY Y ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, hY⟩ := hY
  have h0 : repY Y ∈ Y := Classical.epsilon_spec (p := fun y => y ∈ Y) ⟨y, by rw [hY]; simp⟩
  generalize repY Y = y' at h0
  rw [hY] at h0
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 h0 P
  rw [if_neg hP] at h1 h2
  simp only [zpow_neg, inv_inv, zpow_natCast] at h1 h2
  have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ qOf_ne_zero
  have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M) := intAt_pow (intAt_nat _) _
  have h3 := smul_mem_locP hi (smul_mem_locP hi h2)
  rw [smul_inv_smul₀ hq] at h3
  have h4 := add_mem h3 h1
  rwa [← smul_add, sub_add_cancel] at h4

end Chain

theorem topAtQ : GlobalTheory.ColPeriod.TopAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL P w hP _ hw p d Y hY
  have hc := hL.cst_ok
  have hm := hL.hm
  have hD := hL.depthQ P hP
  have hu := piT_notMem_rowSG sel mu hPr hsel u hS
  have hy : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
    rw [← map_smul, ← frsF_mem' sel mu p P hP, LinearEquiv.apply_symm_apply]
    exact pow_smul_repY sel mu cst hY P hP
  refine ⟨fun x => ?_, fun x z hz => ?_⟩
  · unfold facTop PhiTop
    rw [if_neg hP, map_mul]
    exact mul_le_one' (valuation_PhiQ w _ _ _ _ _ _ _ _ _) (valuation_ftY sel mu cst hc P hP hD w hw hy _)
  · have key : ∀ y ∈ stdAt X.E (R.N (m2 + 1)) P.1,
        (d.1.liftFr P).symm (prXp X.E R (z (frsF sel mu p P y))) ∈ stdAt X.E (R.N R.m - 1) P.1 ∧
          IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (z (frsF sel mu p P y))) := fun y hy => by
      have h := (mem_tilH (N_m_succ R) d (conj_piT_notMem hPr u) hu P.1 _).1
        (hz P.1 (Finset.mem_singleton_self _) _ ((frsF_mem' sel mu p P hP y).2 hy))
      rw [_root_.GlobalTheory.LastSteps.atNL_last, ← (liftFr_spec d.2 P).1, LinearEquiv.apply_symm_apply, inv_mul_eq_div]
      exact ⟨h.1, h.2.div_of_notMem (hu P)⟩
    have h1 : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
      unfold Ranks.r Ranks.N cOf
      rw [hm, mul_add (m2 + 1)]
      omega
    have h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0 := by
      unfold Ranks.N cOf
      rw [hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc.B_pos
    unfold facTop PhiTop
    rw [if_neg hP]
    congr 1
    · have e : (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (x + ((qOf P.1 : X.E) ^ cst.B) • z) ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
          (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) +
          (qOf P.1 : X.E) • ((((qOf P.1 : X.E) ^ k) • ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ z ∘ₗ
            (frsF sel mu p P).toLinearMap)) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
        rw [hk, pow_succ', mul_smul]
        simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]
      rw [e]
      refine PhiQ_add _ h1 (h1.trans h4) _ _ ?_
      rw [comp_funLeft_mem (cOf_top hm), lamY_zero]
      exact fun y hy => smul_mem_locP (intAt_pow (intAt_nat _) _) (key y hy).1
    · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp ((qOf P.1 : X.E) ^ cst.B), LinearMap.comp_smul]
      exact ftY_add sel mu cst hc P hP hD hy _ _ fun y hy => (key y hy).2

end GlobalTheory.ColPeriod.TopTwist
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

namespace GlobalTheory.OtherSplitPlace

theorem exists_isSplitAt_under_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧
      w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  intro E _ _ _ w₀
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E (Ideal.absNorm w₀.asIdeal)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hsplit : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
    intro w hw
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      rwa [map_natCast]
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ]
      exact Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w₁ : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  refine ⟨w₁, hsplit w₁ hpQ, fun heq => ?_⟩

  have hp₀ : (p : 𝓞 E) ∈ w₀.asIdeal := by
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w₁.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₁.asIdeal
      rw [map_natCast]; exact hpQ
    rw [heq] at hv
    have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₀.asIdeal := hv
    rwa [map_natCast] at this
  have hN : ((Ideal.absNorm w₀.asIdeal : ℕ) : 𝓞 E) ∈ w₀.asIdeal := Ideal.absNorm_mem _
  have hN0 : 0 < Ideal.absNorm w₀.asIdeal :=
    Nat.pos_of_ne_zero (fun h => w₀.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hcop : Nat.Coprime p (Ideal.absNorm w₀.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => absurd (Nat.le_of_dvd hN0 h) (not_le.mpr hmp))
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 E))
  apply w₀.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hp₀
  · simpa using hN

end GlobalTheory.OtherSplitPlace
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def intU (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Subgroup (UA E a) :=
  locU a w ⊓ ⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w), (GlobalTheory.LFun.KGL u (n := a)).comap (cLoc u)

def levelOf (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    Subgroup (UA E a) :=
  finU (E := E) (n := a) ⊓ (⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w₀), (cLoc u).ker) ⊓
    ⨅ (w : HeightOneSpectrum (𝓞 E)) (_ : Apart w w₀), ((H w).map (cLoc w)).comap (cLoc w)

variable {a : ℕ}

theorem mem_intU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} :
    x ∈ intU a w ↔ x ∈ locU a w ∧ ∀ u, ¬ Apart u w → cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  simp only [intU, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem mem_levelOf {w₀ : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)} {x : UA E a} :
    x ∈ levelOf a w₀ H ↔ x ∈ finU (E := E) (n := a) ∧ (∀ u, ¬ Apart u w₀ → cLoc u x = 1) ∧
      ∀ w, Apart w w₀ → ∃ y ∈ H w, cLoc w y = cLoc w x := by
  simp only [levelOf, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_ker, Subgroup.mem_map, and_assoc]

theorem not_apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart w u) : ¬ Apart u w := fun h' => h (Ne.symm h')

theorem not_apart_trans {w u v : HeightOneSpectrum (𝓞 E)} (h1 : ¬ Apart w u) (h2 : ¬ Apart u v) : ¬ Apart w v :=
  fun h => h ((not_not.1 h1).trans (not_not.1 h2))

theorem locU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : locU a u = locU a w := by
  have e : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := not_not.1 h
  unfold locU
  rw [e]

theorem intU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : intU a u = intU a w := by
  ext x
  rw [mem_intU, mem_intU, locU_congr h]
  exact and_congr_right fun _ => forall_congr' fun v =>
    ⟨fun h' hv => h' (not_apart_trans hv (not_apart_symm h)), fun h' hv => h' (not_apart_trans hv h)⟩

theorem intU_le_locU (w : HeightOneSpectrum (𝓞 E)) : intU a w ≤ locU a w := inf_le_left

theorem levelOf_le_finU (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    levelOf a w₀ H ≤ finU (E := E) (n := a) := fun _ hx => (mem_levelOf.1 hx).1

theorem eq_of_not_apart_of_not_split {w u : HeightOneSpectrum (𝓞 E)} (hw : ¬ IsSplitAt w) (h : ¬ Apart u w) : u = w := by
  by_contra hne
  exact hw ⟨u, hne, not_not.1 h⟩

theorem cLoc_mem_KGL_of_not_apart {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) (x : UA E a)
    (hx : cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) : cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (E := E) (not_not.1 h) with rfl | rfl
  · exact hx
  · exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w hx

theorem mem_intU_of {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (hk : cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) :
    x ∈ intU a w :=
  mem_intU.2 ⟨hx, fun _ hu => cLoc_mem_KGL_of_not_apart hu x hk⟩

theorem eq_one_of_cLoc_eq_one {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (h1 : cLoc w x = 1) :
    x = 1 := by
  by_cases hw : IsSplitAt w
  · exact congrArg Subtype.val (GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨x, hx⟩ h1)
  · have hall : ∀ u, cLoc u x = 1 := by
      intro u
      by_cases hu : Apart u w
      · exact ((GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx).2 u hu
      · rw [eq_of_not_apart_of_not_split hw hu]; exact h1
    have hinf : cInf x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact hinf.trans (map_one _).symm
    · rw [Subgroup.coe_one, map_one]
      refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
      have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (hall u)
      simp only [Units.val_one, Matrix.one_apply] at this
      refine this.trans ?_
      split_ifs with hij <;> simp [hij] <;> rfl

theorem eq_of_cLoc_eq {w : HeightOneSpectrum (𝓞 E)} {x y : UA E a} (hx : x ∈ locU a w) (hy : y ∈ locU a w)
    (h : cLoc w x = cLoc w y) : x = y := by
  have := eq_one_of_cLoc_eq_one (mul_mem hx (inv_mem hy)) (by rw [map_mul, map_inv, h, mul_inv_cancel])
  exact mul_inv_eq_one.1 this

theorem coe_subgroupOf_image {G : Type} [Group G] {H L : Subgroup G} (h : H ≤ L) :
    Subtype.val '' ((H.subgroupOf L : Subgroup L) : Set L) = (H : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, h hx⟩, hx, rfl⟩

theorem isCompact_of_le {w : HeightOneSpectrum (𝓞 E)} {H : Subgroup (UA E a)} (hH : H ≤ intU a w)
    (ho : IsOpen ((H.subgroupOf (locU a w)) : Set (locU a w))) (hc : IsCompact (intU a w : Set (UA E a))) :
    IsCompact (H : Set (UA E a)) := by
  have hcl : IsClosed ((H.subgroupOf (locU a w)) : Set (locU a w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc' : IsCompact (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, coe_subgroupOf_image (intU_le_locU w)]
    exact hc
  have h2 := (hc'.of_isClosed_subset hcl fun x hx => hH hx).image continuous_subtype_val
  rwa [coe_subgroupOf_image (hH.trans (intU_le_locU w))] at h2

end GlobalTheory.Cong.AdaptLev
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.ConjUnder

theorem complexConj_algebraMap {K M : Type} [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ _ _ w
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact complexConj_algebraMap (x : K)

end GlobalTheory.ConjUnder
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, AddMonoidAlgebra.coeff (polDY D s Q (N' := N')) α ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  first | exact @GlobalTheory.TwV.DelA.wt_polDY_framePol | exact GlobalTheory.TwV.DelA.wt_polDY_framePol | (intros; apply GlobalTheory.TwV.DelA.wt_polDY_framePol <;> assumption)
end
