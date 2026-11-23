module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle708
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle604
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle666
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle655
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle685
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle703
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle706
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfInertiaTrivialOnCrystallinePeriods
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle707
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem muPow_smul_actB_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g ε hε k v z hv
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, -, -, hgal, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨u, hu⟩ := hgal (sQ l g)
  have hB : ∀ x : OA l O, toB l O (galOA O (sQ l g) x) = galOB O (sQ l g) (toB l O x) := fun x => by
    simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  have hμ : galOA O (sQ l g) ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) =
      ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) := by
    rw [map_pow, galOA_tmul, hu, ← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hinv : ((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k = 1 := by
    rw [← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, ← Algebra.TensorProduct.one_def, one_pow]
  set m := toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) with hm
  set w := TWact (galOA O (sQ l g)) T g z with hw
  have h1 : actB (sQ l) T g (m • v) = TWincl (toB l O) T w := by
    rw [hv]
    exact (GlobalTheory.Cyc.Decomp.TWincl_act (toB l O) (galOA O (sQ l g)) (galOB O (sQ l g)) hB T g z).symm
  have h2 : actB (sQ l) T g (m • v) =
      toB l O (((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k) • (m • actB (sQ l) T g v) := by
    rw [actB, GlobalTheory.Cyc.Decomp.TWact_smul, hm, ← hB, hμ, map_mul, mul_smul]
  have h3 : m • actB (sQ l) T g v =
      TWincl (toB l O) T ((((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w) := by
    rw [GlobalTheory.Cyc.Decomp.TWincl_smul, ← h1, h2, smul_smul, ← map_mul, hinv, map_one, one_smul]
  refine ⟨(((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w - z, ?_⟩
  rw [smul_sub, h3, hv, map_sub]

end GlobalTheory.BKGal
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

namespace GlobalTheory.BKGal.TaylorFil

theorem dpowFil : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ), C.j (dpow x hx n) ∈ Per.FilP l n := by
  intro l _ C x hx n
  have hj : C.j (ainfToAcris l x) = GlobalTheory.MemLoc.aDp l x :=
    (congrArg C.j (GlobalTheory.MemLoc.algebraMap_ainf_acris_eq x)).trans
      ((C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)).trans
        (congrArg (algebraMap (Per.AinfP l) (Per.BdRp l)) (Subalgebra.coe_algebraMap _ x)))
  have h1 : GlobalTheory.MemLoc.aDp l x ∈ Per.FilP l 1 := by
    rw [← (GlobalTheory.MemLoc.thetaD_props l).2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, hx]
    simp
  have h2 : ∀ k : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l x) ^ k ∈ Per.FilD l k := by
    intro k
    induction k with
    | zero => simpa using (GlobalTheory.MemLoc.filD_laws l).2.1
    | succ k ih =>
      rw [pow_succ]
      have := (GlobalTheory.MemLoc.filD_laws l).2.2.1 k 1 _ _ ih (by simpa using (alg_mem_FilD_iff 1 _).2 h1)
      simpa using this
  have h3 : C.j (dpow x hx n) * (n.factorial : Per.BdRp l) ∈ Per.FilP l n := by
    have h4 := congrArg C.j (factorial_mul_dpow x hx n)
    rw [map_mul, map_natCast, map_pow, hj] at h4
    rw [mul_comm, h4, ← alg_mem_FilD_iff, map_pow]
    exact h2 n
  have hu : IsUnit (n.factorial : Per.BdRp l) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [map_natCast]; exact_mod_cast n.factorial_ne_zero)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h5 := Ideal.mul_mem_right v _ h3
  rwa [mul_assoc, hv, mul_one] at h5

end GlobalTheory.BKGal.TaylorFil

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem pow_mem_filO {C : GlobalTheory.MemLoc.Core l} {x : OB l O} (hx : x ∈ filO O C 1) (j : ℕ) :
    x ^ j ∈ filO O C j := by
  induction j with
  | zero => simpa using toOB_mem_filO_zero (O := O) C 1
  | succ j ih => rw [pow_succ]; simpa using mul_mem_filO ih hx


variable (O K) in
theorem iS_E_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) :
    toOB l O (ϖ.iS O K (EIn l e _)) ∈ filO O C 1 := by
  have hE : Per.θ l (ϖ.teich ^ e + l) = 0 := by
    rw [map_add (f := _), map_pow, ϖ.theta_teich, ϖ.seqO_zero, map_natCast, neg_add_cancel]
  have h1 : ϖ.iS O K (EIn l e _) = (1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l (ϖ.teich ^ e + l) := by
    have : EIn l e (S O K e) = uIn _ ^ e + (l : S O K e) := Subtype.ext (by simp [E])
    rw [this, map_add (f := _), map_pow, ϖ.iS_u O K, map_natCast, PiSys.teichR, toOCr_tmul, map_add (f := _), map_pow,
      map_natCast, tmul_add, Algebra.TensorProduct.tmul_pow, one_pow]
    congr 1
    exact (map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) l).symm
  have h2 := dpowFil l C _ hE 1
  rw [dpow_one] at h2
  rw [h1]
  simpa using toOB_tmul_mem_filO (O := O) h2


variable (O) in
theorem muDiv_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    toOB l O (ϖ.muDiv a O g i) ∈ filO O C i :=
  toOB_tmul_mem_filO (dpowFil l C _ _ i)

theorem gal_iSl_sub_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (g : ↥(GK (ϖ.field a)))
    (p : invL l (S O K e)) (hp : (p : K⟦X⟧) ∈ invL l (A O K))
    (hN : ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (p : K⟦X⟧) = E K l e ^ m * h) :
    galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p ∈ filO O C m := by
  obtain ⟨h, hh, k, hk⟩ := hN
  obtain ⟨s, hs⟩ := hp
  set p₀ : K⟦X⟧ := (l : K⟦X⟧) ^ s * p with hp₀def
  have hp₀A : p₀ ∈ A O K := by simpa [p₀] using hs
  let q : S O K e := ⟨p₀, A_le_S l e hp₀A⟩
  have hq : (l : invL l (S O K e)) ^ s * p = ⟨p₀, le_away _ _ q.2⟩ := Subtype.ext (by simp [p₀])
  have hiq : (l : OB l O) ^ s * ϖ.iSl O K p = toOB l O (ϖ.iS O K q) := by
    rw [← ϖ.iSl_of_mem O K q.2 (le_away _ _ q.2), ← hq, map_mul, map_pow, map_natCast]
  set D := galOCr O g (ϖ.iS O K q) - ϖ.iS O K q with hDdef
  have hD : (l : OB l O) ^ s * (galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p) = toOB l O D := by
    have h3 : (l : OB l O) ^ s * galOB O g (ϖ.iSl O K p) = galOB O g ((l : OB l O) ^ s * ϖ.iSl O K p) := by
      rw [map_mul, map_pow, map_natCast]
    rw [mul_sub, h3, hiq, galOB_toOB, hDdef, map_sub]
  refine mem_filO_of_pow_mul (s := s) ?_
  rw [hD]
  refine mem_filO_of_pow_mul (s := k) ?_
  have hk' : (l : OB l O) ^ k * toOB l O D = toOB l O ((l : OCr l O) ^ k * D) := by
    rw [map_mul, map_pow, map_natCast]
  rw [hk']
  have hdesc : ∀ i, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i p₀ = E K l e ^ (m + 1 - i) * h' := by
    intro i hi
    obtain ⟨h', hh', he⟩ := GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow l e O K (p : K⟦X⟧) h k m hh hk i hi
    refine ⟨(l : K⟦X⟧) ^ s * h', mul_mem (pow_mem (natCast_mem _ l) s) hh', ?_⟩
    have h4 : descN K i p₀ = (l : K⟦X⟧) ^ s * descN K i p := by
      have h3 : (l : K⟦X⟧) ^ s = PowerSeries.C ((l : K) ^ s) := by simp
      rw [hp₀def, h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]
    rw [h4, mul_left_comm, he]
    ring
  refine GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx l O C m _ fun r => ?_
  obtain ⟨M₀, hM⟩ := ϖ.taylor_S a O K g q r
  obtain ⟨w, hw⟩ := hM (max M₀ 1) (le_max_left _ _)
  have hM1 : 0 < max M₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h0 : ∑ i ∈ Finset.range (max M₀ 1), ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
      ϖ.iS O K q + ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
        ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hM1)]
    congr 1
    rw [PiSys.muDiv, dpow_zero, ← Algebra.TensorProduct.one_def, one_mul]
    congr 1
    exact Subtype.ext (by simp [descN])
  refine ⟨(l : OCr l O) ^ k * ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
    ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩, (l : OCr l O) ^ k * w, ?_, ?_⟩
  · rw [h0] at hw
    rw [hDdef]
    linear_combination (l : OCr l O) ^ k * hw
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi1 : 1 ≤ i := Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)
    obtain ⟨h', hh', he⟩ := hdesc i hi1
    have h2 : (l : OCr l O) ^ k * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
        ϖ.iS O K (EIn l e _) ^ (m + 1 - i) * ϖ.iS O K ⟨h', A_le_S l e hh'⟩ := by
      rw [← map_natCast (ϖ.iS O K), ← map_pow, ← map_mul, ← map_pow, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa using he)
    rw [mul_left_comm, h2, map_mul, map_mul, map_pow]
    have h5 := mul_mem_filO (mul_mem_filO (muDiv_mem O ϖ C g i) (pow_mem_filO (iS_E_mem O K ϖ C) (m + 1 - i)))
      (toOB_mem_filO_zero C (ϖ.iS O K ⟨h', A_le_S l e hh'⟩))
    rw [← mul_assoc]
    exact filO_anti (by omega) h5

end Main

theorem gal_iB_sub_mem_filO : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, (f τ : K⟦X⟧) ∈ invL l (A O K)) → (∀ τ, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (f τ : K⟦X⟧) = E K l e ^ m * h) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → galOB O (sQ l g) (ϖ.iB t K f) - ϖ.iB t K f ∈ filO O C m := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ C m f hfA hN g hg
  have key : ∀ τ, galOB O (sQ l g) (ϖ.iSl O K (f τ)) - ϖ.iSl O K (f τ) ∈ filO O C m := fun τ =>
    gal_iSl_sub_mem ϖ C m ⟨sQ l g, hg⟩ (f τ) (hfA τ) (hN τ)

  rw [PiSys.iB, glue_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun τ _ => ?_
  have hid : galOB O (sQ l g) (idem (constB t) τ) = idem (constB t) τ :=
    (galOB_toOB _ (idem (constC t) τ)).trans (congrArg _ (galOCr_idem t ϖ ⟨sQ l g, hg⟩ τ))
  rw [map_mul, hid, ← mul_sub]
  have h6 := mul_mem_filO (toOB_mem_filO_zero C (idem (constC t) τ)) (key τ)
  rw [zero_add] at h6
  exact h6

end GlobalTheory.BKGal.TaylorFil
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.LiftStep

theorem ev_eis_mul_mu {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : PiSys l e)
    {ε δ : OCb l} (hε : IsEps ε) (hδ : δ ^ l = ε) :
    ∃ u : Ainf l, IsUnit u ∧ ϖ.ev a (eis l a e) * muOf δ = u * muOf ε := by
  obtain ⟨⟨ξ, hξ, hμ⟩, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  have h : Associated (ϖ.ev a (eis l a e)) ξ := by
    rw [← Ideal.span_singleton_eq_span_singleton, hξ, PiSys.span_ev_eis]
  obtain ⟨v, hv⟩ := h
  refine ⟨((v⁻¹ : (Ainf l)ˣ) : Ainf l), Units.isUnit _, ?_⟩
  rw [hμ, ← hv]
  linear_combination (-(ϖ.ev a (eis l a e) * muOf δ)) * v.inv_mul

section Integral

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)

theorem E_pow_mul_iW (n : ℕ) (f : ZMod a → invE l e (A O K)) (hf : ∀ τ, E K l e ^ n * (f τ : K⟦X⟧) ∈ A O K) :
    inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ n * ϖ.iW t K f = inclO l O (ϖ.iTot t K fun τ => ⟨_, hf τ⟩) := by
  have h1 : inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) = ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) := by
    rw [← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  rw [h1, ← map_pow, ← map_mul, ← ϖ.iW_of_mem t K]
  congr 1

theorem integral (α β : ℕ) (hL : ∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) (hM : ∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) :
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * frobMat t ϖ P i j) ∧
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ β * frobMatInv t ϖ P i j) ∧
    ∀ y : ME P, y.1 ∈ P.EM α → ∀ i, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * toW t ϖ P y i := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun y hy i => ?_⟩
  · have hm : (fun τ k => P.mx τ k j) ∈ P.L := mem_tot.2 fun τ => Submodule.subset_span ⟨j, rfl⟩
    have h := mem_tot.1 (hL _ hm)
    exact ⟨_, (E_pow_mul_iW t ϖ α _ fun τ => h τ i).symm⟩
  · have hm : (fun (_ : ZMod a) (k : ι) => if k = j then (1 : K⟦X⟧) else 0) ∈ P.M :=
      mem_tot.2 fun τ k => by split_ifs <;> simp [Mc, mem_vecs]
    have h := fun τ => P.mem_extc_iff.1 (mem_tot.1 (hM _ hm) τ) i
    refine ⟨_, (E_pow_mul_iW t ϖ β (fun τ => ((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) i j) fun τ => ?_).symm⟩
    simpa [Matrix.mulVec, dotProduct, PhiMod.mxInv, mul_comm] using h τ
  · have h : ∀ τ, E K l e ^ α * (y.1 τ i) ∈ A O K := fun τ => by simpa using mem_tot.1 hy τ i
    refine ⟨ϖ.iTot t K fun τ => ⟨_, h τ⟩, ?_⟩
    rw [toW_apply]
    exact (E_pow_mul_iW t ϖ α (fun τ => ⟨y.1 τ i, mem_tot.1 y.2 τ i⟩) h).symm

end Integral

end GlobalTheory.BKGal.LiftStep

theorem GlobalTheory.BKGal.LiftStep.alg_step {S ι : Type} [CommRing S] [Fintype ι] (Ui Ew N Mh : S) (α β : ℕ)
    (hMN : Mh = Ui * Ew ^ (β + α) * N) (Xi : Matrix ι ι S) (m y : ι → S) (Yc : ι → ι → S) (yc : ι → S)
    (hY : ∀ i j, Yc i j = Ew ^ β * Xi i j) (hy : ∀ j, yc j = Ew ^ α * y j) :
    Mh • (Xi *ᵥ (m + y)) = (Matrix.of fun i j => Ui * Ew ^ α * Yc i j) *ᵥ (N • m) +
      fun i => Ui * ∑ j, Yc i j * (N * yc j) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, hY, hy, hMN,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


open GlobalTheory.BKGal.LiftStep in
theorem GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → ∀ (y : ME P), y.1 ∈ P.EM α → ∀ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P y → inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) • m₀ ∈ MA P ∧ inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) • phiW t ϖ P m₀ ∈ LA t ϖ P := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hL hM ε δ hε hδ y hy m₀ hm₀
  classical
  obtain ⟨u, hu, hEu⟩ := ev_eis_mul_mu a ϖ hε hδ
  have hfr : WittVector.frobenius (muOf δ) = muOf ε := ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.1
  obtain ⟨-, hXi, hyI⟩ := integral t ϖ P α β hL hM
  choose cXi hcXi using hXi
  choose cy hcy using hyI y hy
  set ui : Ainf l := ((hu.unit⁻¹ : (Ainf l)ˣ) : Ainf l) with hui
  have hμ : muOf ε = ui * ϖ.ev a (eis l a e) * muOf δ := by
    rw [mul_assoc, hEu, ← mul_assoc, hui, IsUnit.val_inv_mul, one_mul]
  set Ew := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hEw
  set N := inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) with hN
  set Mh := inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) with hMh
  set Ui := inclO l O (1 ⊗ₜ (ui ^ (β + α))) with hUi
  have hMN : Mh = Ui * Ew ^ (β + α) * N := by
    rw [hMh, hUi, hEw, hN, ← map_pow, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, hμ, mul_pow, mul_pow]
  have hFN : frobOW l O N = Mh := by
    rw [hN, frobOW_inclO, frobOA_tmul, map_pow, hfr]
  set y' := toW t ϖ P y with hy'
  have hF : (fun i => frobOW l O (m₀ i)) = frobMatInv t ϖ P *ᵥ (m₀ + y') := by
    have h1 : frobMat t ϖ P *ᵥ (fun i => frobOW l O (m₀ i)) = m₀ + y' := by
      rw [← phiW_apply]; exact sub_eq_iff_eq_add'.1 hm₀
    rw [← h1, Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec]
  set z : ι → OW l O := N • m₀ with hz
  have hFz : (fun i => frobOW l O (z i)) = Mh • (fun i => frobOW l O (m₀ i)) := by
    funext i
    simp only [hz, Pi.smul_apply, smul_eq_mul, map_mul, hFN]
  set Y : Matrix ι ι (OA l O) := fun i j => (1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j
  set w : ι → OA l O := fun i => (1 ⊗ₜ (ui ^ (β + α))) * ∑ j, cXi i j * ((1 ⊗ₜ (muOf δ ^ (β + α))) * cy j)
  have heq : (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) := by
    rw [hFz, hF, alg_step Ui Ew N Mh α β hMN (frobMatInv t ϖ P) m₀ y' (fun i j => inclO l O (cXi i j))
      (fun j => inclO l O (cy j)) hcXi hcy]
    congr 2
    · ext i j
      change _ = inclO l O ((1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j)
      rw [map_mul, map_mul, map_pow]
      rfl
    · funext i

      simp only [w, map_mul, map_sum]
      rfl
  have hint := GlobalTheory.T.frobenius_integrality_coeffTensorAinf_vector l O ι Y w z heq
  choose c hc using hint
  refine ⟨⟨c, funext fun i => hc i⟩, ⟨fun i => frobOA l O (c i), ?_⟩⟩
  rw [inclL_apply, phiW_apply, ← Matrix.mulVec_smul, ← hFz]
  congr 1
  funext i
  rw [← frobOW_inclO]
  exact congrArg _ (hc i)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoverGen

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : BKGal.Gl l),
    ∃ h k : BKGal.Gl l, g = h * k ∧ BKGal.sQ l h ∈ GK (ϖ.field a) ∧
      ∃ γ : BK.TameGal K l e a, BKGal.Covers K t ϖ (BKGal.sQ l k) γ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  obtain ⟨h, hh, k, hk, hg⟩ :=
    GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ he (BKGal.sQ l g)
  let h' : BKGal.Gl l :=
    ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
  refine ⟨h', h'⁻¹ * g, by rw [mul_inv_cancel_left], hh, ?_⟩
  have hk' : BKGal.sQ l (h'⁻¹ * g) = k := by
    rw [map_mul, map_inv, show BKGal.sQ l g = h * k from hg]
    change h⁻¹ * (h * k) = k
    rw [inv_mul_cancel_left]
  rw [hk']
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_action_cyclotomic_power l a k
  obtain ⟨z, hz, hkz⟩ := GlobalTheory.T.exists_root_of_unity_kummer_eq l a e ϖ he k hk
  exact GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller l a e O K t ϖ k s z hz hs hkz

end GlobalTheory.TameCoverGen
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bcrisCoboundary_eventually_mem_prime_pow_lattice : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := by
  first | exact @GlobalTheory.CocycleCont.cont_at_one | exact GlobalTheory.CocycleCont.cont_at_one | (intros; apply GlobalTheory.CocycleCont.cont_at_one <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.kummerTowerGalois_preserves_breuilKisinModule : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v' := by
  first | exact @GlobalTheory.GKinfStable.main | exact GlobalTheory.GKinfStable.main | (intros; apply GlobalTheory.GKinfStable.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystalline_of_inertia_trivial_on_crystallinePeriods : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' F : FinExt l), (GK K').Normal → ∀ T : QLat LL, IsCrys (Pl.PD K') (resF T K').ρ → ((∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), (g : GQ l) ∈ GK F → ∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → IsCrys (Pl.PD F) (resF T F).ρ) ∧ ∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∀ p : Polynomial ↥LL.1, (∀ x ∈ Dcris (Pl.PD K') (resF T K').ρ, Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p x = 0) → ∀ x ∈ Dcris (Pl.PD F) (resF T F).ρ, Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) p x = 0 := by
  first | exact @GlobalTheory.CrysInertDescent.main | exact GlobalTheory.CrysInertDescent.main | (intros; apply GlobalTheory.CrysInertDescent.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_OE_stability_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w : WCb l, ((l : ℕ) : WCb l) * w ∈ bk.OE → w ∈ bk.OE) ∧ (∀ w : WCb l, (∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) → w ∈ bk.OE) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ ∀ w ∈ bk.OE, IsUnit w → ∃ w' ∈ bk.OE, w * w' = 1 := by
  first | exact @GlobalTheory.OEStable.main | exact GlobalTheory.OEStable.main | (intros; apply GlobalTheory.OEStable.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.stratifiedHom_defect_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map B.D.φ) = BK.hf f bk.E ^ S'.a • ((S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g) * S.A.map (BK.hf g)) := by
  first | exact @GlobalTheory.BSP.strat_homDefect_φ | exact GlobalTheory.BSP.strat_homDefect_φ | (intros; apply GlobalTheory.BSP.strat_homDefect_φ <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_wittPowerSeries_approx_matrix_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (c : Matrix (Fin d) (Fin d) (Om l)), (∀ i j, c i j ∈ K.1) → ∀ n : ℕ, ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * C.o (c i j) ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.LiftMatK.lift_matrix) | (exact GlobalTheory.LiftMatK.lift_matrix) | (intros; apply GlobalTheory.LiftMatK.lift_matrix  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinEnvelope_point_factors_through_section : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : En.Q.A →+* O), f (En.inl.f (bk.ev X)) ≠ 0 → ¬ IsUnit (f (En.inl.f (bk.ev X))) → IsAdicComplete (Ideal.span {f (En.inl.f (bk.ev X))}) O → ∃ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)) (ψ : OCb l →+* O), s.comp En.inl = Hom.id _ ∧ s.comp En.inr = (ainfHom K g).comp bk.ι ∧ ∀ a, f a = ψ (WittVector.coeff (p := l) (R := OCb l) (s.f a) 0) := by
  first | exact @GlobalTheory.BSP.envPoint_factors | exact GlobalTheory.BSP.envPoint_factors | (intros; apply GlobalTheory.BSP.envPoint_factors <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x : κ → Cb l), (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, autCb l (galTilt l (g : GQ l)) (x j) = x j) → (∀ (T : Type) [CommRing T] (i₁ i₂ : Cb l →+* T), (∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), i₁ y = i₂ y) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → ∀ j, x j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  first | exact @GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant | exact GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant | (intros; apply GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant <;> assumption)
end
