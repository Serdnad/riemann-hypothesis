module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle538
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle427
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle532
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle544
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle545
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ExpImage.Tail

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}

abbrev Fr (l : ℕ) [Fact l.Prime] (n : ℕ) : Ainf l →+* Ainf l :=
  (WittVector.frobenius : Ainf l →+* Ainf l) ^ n

theorem Fr_succ (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = WittVector.frobenius (Fr l n a) := by
  rw [Fr, pow_succ']; rfl

theorem Fr_succ' (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = Fr l n (WittVector.frobenius a) := by
  rw [Fr, pow_succ]; rfl

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem Fr_teich (n : ℕ) (x : OCb l) :
    Fr l n (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l ^ n := by
  induction n with
  | zero => simp [Fr]
  | succ n ih => rw [Fr_succ, ih, map_pow, frob_teich, ← pow_mul, pow_succ']

theorem lifts_Fr {w : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) (n : ℕ) :
    Lifts AI K (Fr l n w) ((frK P K ^ n) c) := by
  induction n with
  | zero => simpa [Fr] using h
  | succ n ih =>
    rw [Fr_succ, pow_succ']
    exact ih.frob

theorem lifts_sum {ι : Type} (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K))
    (h : ∀ i ∈ T, Lifts AI K (w i) (c i)) : Lifts AI K (∑ i ∈ T, w i) (∑ i ∈ T, c i) := by
  unfold Lifts at h ⊢

  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl h

def oK (P : LocPrime l) (K : FinExt l) : ↥(K0 K) →+* P.R.BdR :=
  (oB P).comp (algebraMap ↥(K0 K) (Om l))

theorem oK_apply (c : ↥(K0 K)) : oK P K c = oB P (c : Om l) := rfl

def u (P : LocPrime l) (j : ℕ) : P.R.BdR := qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j

theorem u_mem (j : ℕ) : u P j ∈ FilB P 0 := by
  refine qB_mul_mem _ (FilB_anti ?_ (FilB_pow tD_mem j))
  simp

theorem taylor0 (hT : LocTied l P AI) (m M : ℕ) :
    io AI (WittVector.teichmuller l AI.ε ^ m) - ∑ j ∈ Finset.range M, (m : P.R.BdR) ^ j * u P j ∈
      FilB P (M : ℤ) := by
  have h := GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI hT 0 m M
  rw [P.ζQ_zero, one_pow, map_one, one_mul] at h
  convert h using 3 with j hj
  · rfl
  · rw [pow_zero, div_one, div_eq_mul_inv, map_mul, map_pow, map_natCast, u, mul_assoc]

theorem span_mem_Lat {M n : ℕ} {a : Ainf l}
    (ha : a ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI a ∈ Lat AI M n := by
  obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.mp ha
  refine ⟨x, ?_⟩
  have h := FilB_zero_mul (io_mem AI y) (FilB_pow (io_ξ_mem AI) M)
  rw [mul_one] at h
  convert h using 1
  simp only [map_add (f := _), map_mul, map_pow]
  ring

theorem tail (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ)
    (d : ℕ → ↥(K0 K)) (hM : 1 ≤ M) (hw : ∀ i ∈ T, Lifts AI K (w i) (c i))
    (hd : ∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧
      d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) :
    ∃ y : Ainf l, y - WittVector.frobenius y =
        ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧
      io AI y - ∑ j ∈ Finset.range M,
        qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hD : ∀ j, ∃ D : Ainf l, j < M → Lifts AI K D (d j) := by
    intro j
    by_cases hj : j < M
    · obtain ⟨D, hD⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l P AI hT K (d j) (hd j hj).1
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose D hD using hD
  have h0 : D 0 - WittVector.frobenius (D 0) = ∑ i ∈ T, w i := by
    have h1 := (hD 0 hM).sub (hD 0 hM).frob
    have h2 := (hd 0 hM).2
    simp only [pow_zero, one_mul, mul_one] at h2
    rw [h2] at h1
    exact h1.unique (lifts_sum T w c hw)
  obtain ⟨q, hq⟩ : AI.μ ∣ ∑ i ∈ T, w i * (WittVector.teichmuller l AI.ε ^ m i - 1) := by
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _
    have := sub_dvd_pow_sub_pow (WittVector.teichmuller l AI.ε) 1 (m i)
    rwa [one_pow] at this
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.ainf_mu_frobenius_equation_solvable_and_tendsto l P AI
  obtain ⟨y', hy'⟩ := hc1 q
  have hy : (D 0 + AI.μ * y') - WittVector.frobenius (D 0 + AI.μ * y') =
      ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hq
    rw [map_add (f := _)]
    linear_combination h0 + hy' - hq
  refine ⟨D 0 + AI.μ * y', hy, ?_⟩
  set y := D 0 + AI.μ * y' with hydef
  let E : ℕ → P.R.BdR := fun n => io AI (Fr l n y) -
    ∑ j ∈ Finset.range M, (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j
  have hstep : ∀ n, E n - E (n + 1) ∈ FilB P (M : ℤ) := by
    intro n
    have h1 : io AI (Fr l n y) - io AI (Fr l (n + 1) y) =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
          io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) := by

      rw [Fr_succ', ← map_sub, ← map_sub, hy, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, map_mul, (lifts_Fr (hw i hi) n).io_eq, map_pow (Fr l n), Fr_teich, ← pow_mul,
        mul_comm (l ^ n), oK_apply]
    have h2 : ∀ j ∈ Finset.range M,
        (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j -
          (l : P.R.BdR) ^ (j * (n + 1)) * oK P K ((frK P K ^ (n + 1)) (d j)) * u P j =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      intro j hj
      have h3 := congrArg (fun x => oK P K ((frK P K ^ n) x)) (hd j (Finset.mem_range.mp hj)).2

      simp only [map_sub, map_mul, map_pow, map_natCast, map_sum] at h3
      have h4 : (frK P K ^ (n + 1)) (d j) = (frK P K ^ n) (frK P K (d j)) := by
        rw [pow_succ]; rfl
      have h5 : ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j)
          = (l : P.R.BdR) ^ (j * n) * u P j *
            ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (m i : P.R.BdR) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [h4, h5, ← h3]
      ring
    have h6 : E n - E (n + 1) = ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
        (io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) -
          ∑ j ∈ Finset.range M, ((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [← h1, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_sub_distrib]
      simp only [E]
      ring
    rw [h6]
    refine Submodule.sum_mem _ fun i hi => FilB_zero_mul ?_ (taylor0 hT _ _)
    rw [oK_apply, ← (lifts_Fr (hw i hi) n).io_eq]
    exact io_mem AI _
  have htel : ∀ n, E 0 - E n ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (hstep n)
      rwa [sub_add_sub_cancel] at this
  have hE0 : E 0 ∈ FilB P (M : ℤ) := by
    refine GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI hT M _ fun r => ?_
    obtain ⟨k₀, hk₀⟩ := hc2 M r
    have hk : ∀ j, ∃ k : ℕ, (l : P.R.BdR) ^ k * u P j ∈ Lat AI M r := fun j =>
      (GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l P AI hT _ (u_mem j) M r).1
    choose k hk using hk
    set n := k₀ + ∑ j ∈ Finset.range M, k j with hn
    have hEn : E n ∈ Lat AI M r := by
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      have e0 : oK P K ((frK P K ^ n) (d 0)) = io AI (Fr l n (D 0)) := by
        rw [oK_apply, (lifts_Fr (hD 0 hM) n).io_eq]
      have e1 : E n = io AI (Fr l n y') * io AI (Fr l n AI.μ) - ∑ j ∈ Finset.range M',
          (l : P.R.BdR) ^ ((j + 1) * n) * oK P K ((frK P K ^ n) (d (j + 1))) * u P (j + 1) := by
        simp only [E, hydef]
        rw [Finset.sum_range_succ', e0]
        simp only [map_add (f := _), map_mul, u, zero_mul, pow_zero, Nat.factorial_zero, Nat.cast_one,
          inv_one, map_one]
        ring
      rw [e1]
      refine sub_mem (io_mul_mem_Lat AI _ (span_mem_Lat ?_)) (sum_mem fun j hj => ?_)
      · have := hk₀ n (Nat.le_add_right _ _)
        rwa [← RingHom.coe_pow] at this
      · have hj' : j + 1 < M' + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hle : k (j + 1) ≤ (j + 1) * n := by
          have a1 : k (j + 1) ≤ ∑ j ∈ Finset.range (M' + 1), k j :=
            Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj')
          have a2 : n ≤ (j + 1) * n := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
          omega
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
        have := io_mul_mem_Lat AI (((l : ℕ) : Ainf l) ^ e * Fr l n (D (j + 1))) (hk (j + 1))
        convert this using 1
        rw [he, oK_apply, ← (lifts_Fr (hD _ hj') n).io_eq, map_mul, map_pow, map_natCast]
        ring
    have := add_mem (FilB_le_Lat AI (n := r) (htel n)) hEn
    rwa [sub_add_cancel] at this
  convert hE0 using 1
  simp only [E, Fr, pow_zero, mul_zero, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [u, oK_apply, AlgHom.one_apply]
  ring

end GlobalTheory.ExpImage.Tail
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.TransitionThirdCase


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jD_Qpow (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (m : ℕ)
    (x : ((HW l).W K s LL h).DD T) :
    ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).Q ^ m • x) =
      (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ)) ^ m • ((F l).E K s LL h).tie.jD T x := by
  let W := (HW l).W K s LL h
  let E := ((F l).E K s LL h).tie
  let a : AA K LL := W.Q ^ m
  let ξ : RA LL := (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ
  let aE := @algebraMap (AA K LL) W.EE _ W.eeRing.toSemiring W.eeAlgA a
  have hQ : E.io W.Q = ξ := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  have hscalar : E.ioE aE = (inclR LL ξ) ^ m :=
    (E.ioE_ext a).trans
      ((map_pow ((inclR LL).comp E.io) W.Q m).trans
        (congrArg (fun b : RA LL => (inclR LL b) ^ m) hQ))
  have hx := (@algebraMap_smul (AA K LL) _ W.EE W.eeRing.toSemiring W.eeAlgA
    (W.DD T) (W.ddAcg T).toAddCommMonoid (W.ddModE T) (W.ddModA T) (W.ddTowA T) a x).symm
  let smulRW := (@TensorProduct.leftHasSMul ↥(OL LL) (RW LL) _ _ (RW LL) ↥T.L.T _ _
    (Semiring.toModule (R := RW LL)).toDistribMulAction _ _ _).smul
  exact (congrArg (E.jD T) hx).trans
    ((E.jD_smul T aE x).trans (congrArg (fun b => smulRW b (E.jD T x)) hscalar))

private theorem image_map_refl {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R]
    [AddCommGroup M] [Module O M] (S : Set (R ⊗[O] M)) :
    TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap '' S = S := by
  rw [show TensorProduct.map (LinearMap.id : R →ₗ[O] R)
    (LinearEquiv.refl O M).toLinearMap = LinearMap.id from TensorProduct.map_id]
  exact Set.image_id S

private theorem transfer_preimage {A B C : Type} (f : A → C) (g : B → C)
    (u : A → A) (v : B → B) (k : C → C) (S : Set A) (S' : Set B)
    (hf : Function.Injective f) (hu : ∀ y, f (u y) = k (f y))
    (hR : Set.range g = Set.range f) (hN : g '' S' = f '' S)
    (y' : B) (hy' : v y' ∈ S') (hv : g (v y') = k (g y')) :
    ∃ y, u y ∈ S ∧ f y = g y' := by
  obtain ⟨y, hy⟩ := hR.subset (Set.mem_range_self y')
  obtain ⟨z, hz, he⟩ := hN.subset (Set.mem_image_of_mem g hy')
  have hzy : z = u y := hf <| calc
    f z = g (v y') := he
    _ = k (g y') := hv
    _ = k (f y) := congrArg k hy.symm
    _ = f (u y) := (hu y).symm
  exact ⟨y, hzy ▸ hz, hy⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT m y' hy'
  let T' : Lt K' LL := resLt hle T
  let W := (HW l).W K s LL h
  let W' := (HW l).W K' s LL h'
  let E := ((F l).E K s LL h).tie
  let E' := ((F l).E K' s LL h').tie
  let j : W.DD T → RW LL ⊗[↥(OL LL)] ↥T.L.T := E.jD T
  let j' : W'.DD T' → RW LL ⊗[↥(OL LL)] ↥T.L.T := E'.jD T'
  let u := (W.ddModA T).toSMul.smul (W.Q ^ m)
  let v := (W'.ddModA T').toSMul.smul (W'.Q ^ m)
  let k := (@TensorProduct.leftHasSMul ↥(OL LL) (RW LL) _ _ (RW LL) ↥T.L.T _ _
    (Semiring.toModule (R := RW LL)).toDistribMulAction _ _ _).smul
      ((inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ)) ^ m)
  have hB := (GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0).2.2
    T T' (LinearEquiv.refl (↥(OL LL)) ↥T.L.T) (fun _ _ => rfl)
  have hId := image_map_refl (O := ↥(OL LL)) (R := RW LL) (M := ↥T.L.T)
  have hR : Set.range j' = Set.range j :=
    (hId (Set.range j')).symm.trans hB.1
  have hN : j' '' (W'.N T' : Set (W'.DD T')) = j '' (W.N T : Set (W.DD T)) :=
    (hId (j' '' (W'.N T' : Set (W'.DD T')))).symm.trans
      (hB.2 hT (restrict_crys (K' := K') D hle T hT))
  exact transfer_preimage j j' u v k (W.N T) (W'.N T') (E.jD_inj T)
    (jD_Qpow D HW F l K s LL h T m) hR hN y' hy' (jD_Qpow D HW F l K' s LL h' T' m y')

end GlobalTheory.NL.TransitionThirdCase
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u : WO S T, IsHalf (cA D a) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f


open Classical in
def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (f : WO S T → ℂ)
    (x : WO S T) : ℂ :=
  if IsHalf a x then ℓ (heisO ψ S T x f) else 0

def HasShape (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (Φ f : WO S T → ℂ) : Prop :=
  ∀ ℓ, InvForm ψ S T a ℓ → ∃ c : ℂ, ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = c * Φ x

def locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) : Submodule ℂ (WO S T → ℂ) :=
  Submodule.span ℂ {φ | ∃ u : WO S T, IsHalf (a + cA D a) u ∧ φ = heisO ψ S T u f}


open Classical in
def adjDat (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D)
    (ω : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ) (x : WO S T) : ℂ :=
  if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then ω (fun PP => redM PP (frMapAdj S T βS βT x)) else 0

def translT (S T : HSp D) (a : AE D) (Φ : WO S T → ℂ) : Set (WO S T → ℂ) :=
  {Ψ | ∃ g : GA D T, SuppAt a T g ∧ Ψ = fun x => Φ (actO S T 1 g x)}

abbrev latH (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True

def LevChart (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) : Prop :=
  Function.Surjective φ ∧ (∀ z, φ z = 0 ↔ toEAf D e * z = 0) ∧
    (∀ z, toEAf D e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ φ z ∈ v.adicCompletionIntegers D.host.F) ∧
    ∀ (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (o : GlobalTheory.SplitHecke.Ov D v), (o : Fv D.host.F v) = φ s →
      ι (resS D.host.F PP s) = IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) o

def rdAdj (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) :=
  (frMapAdj S T βS βT x).map φ

end GlobalTheory.DownLift.SplitCoef

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α → IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  first | exact @GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar | exact GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar | (intros; apply GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar <;> assumption)
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Published

theorem FontaineBcris.fund_holds (l : ℕ) [Fact l.Prime] (C : Core l) : C.Fund := by
  intro b h1 h2
  exact GlobalTheory.MemLoc.fundamental_exact l C b h1 h2

theorem FontaineBcris_holds : FontaineBcris :=
  FontaineBcris.of_rest fun l _ C =>
    ⟨GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C, FontaineBcris.fund_holds l C, GlobalTheory.MemLoc.FundOnto.fundOnto l C,
      GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)⟩

end GlobalTheory.Published
end
end

section


theorem _root_.GlobalTheory.T.fontaineBcrisBasicTheorems_proof : GlobalTheory.Published.FontaineBcris := by
  first | exact @GlobalTheory.MemLoc.fontaineBcris | exact GlobalTheory.MemLoc.fontaineBcris | (intros; apply GlobalTheory.MemLoc.fontaineBcris <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem _root_.GlobalTheory.T.lie_mem_compactFiniteVectors_of_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (X : Lie E N) (φ : Sm E N), φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) := by
  first | exact @GlobalTheory.LieFin.lie_mem_finVec | exact GlobalTheory.LieFin.lie_mem_finVec | (intros; apply GlobalTheory.LieFin.lie_mem_finVec <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem _root_.GlobalTheory.T.capelliDet_diagonalBlock_acts_by_infinitesimalCharacter : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ), (π i).HasInfChar τ M → ∀ (u : ℂ) (ψ : Sm E N), (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorForms π → ∀ m, (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  first | exact @GlobalTheory.BlockCap.qdet_block_levi | exact GlobalTheory.BlockCap.qdet_block_levi | (intros; apply GlobalTheory.BlockCap.qdet_block_levi <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

theorem _root_.GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  first | (exact @GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (exact GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (intros; apply GlobalTheory.RSNonvan.norm_prod_sat_eq_one  <;> assumption)
end
