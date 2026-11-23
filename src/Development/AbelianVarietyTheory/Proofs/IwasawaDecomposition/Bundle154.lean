module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeNormalFormUnipotent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle147
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

@[expose] public section

section

namespace GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect

theorem latticeNormalForm : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm :=
  GlobalTheory.Proof.LatticeNormalFormUnipotent.latticeNormalForm

end GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.FixR

theorem step_abs {R A K : Type} [CommRing R] [CommRing A] [IsDomain A] [Field K]
    (i : R →+* A) (f : R →+* R) (φ : A →+* A) (Θ : A →+* K) (p : A) (hp : Θ p ≠ 0)
    (hφp : φ p = p) (hf : ∀ a, φ (i a) = i (f a))
    (μ : R) (hμ : ∀ n, Θ (i (f^[n] μ)) = 0)
    (hI : ∀ a : R, (∀ n, Θ (i (f^[n] a)) = 0) → μ ∣ a)
    (w : A) (m : ℕ) (hw : p * w = i μ ^ (m + 1))
    (himg : ∀ y, ∃ a z, φ y = i a + w * z)
    (t u : A) (hu : IsUnit u) (ht : t = i μ * u) (ht0 : t ≠ 0) (hφt : φ t = p * t)
    (r : ℕ) (x : A) (hx : φ x = p ^ (r + 1) * x) (hx0 : Θ x = 0) :
    ∃ x', p ^ (r + 2) * x = t * x' ∧ φ x' = p ^ r * x' := by
  have hit : ∀ n a, φ^[n] (i a) = i (f^[n] a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro a; rw [Function.iterate_succ_apply, hf, ih, Function.iterate_succ_apply]
  have hpn : ∀ n, (φ ^ n) p = p := by
    intro n
    rw [RingHom.coe_pow]
    exact Function.iterate_fixed hφp n
  have hit' : ∀ n a, (φ ^ n) (i a) = i (f^[n] a) := by
    intro n a
    rw [RingHom.coe_pow]; exact hit n a
  have hxn : ∀ n, Θ ((φ ^ n) x) = 0 := by
    intro n
    induction n with
    | zero => simpa using hx0
    | succ n ih =>
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, hx]
      simp only [map_mul, ih, mul_zero]
  have hwn : ∀ n, Θ ((φ ^ n) w) = 0 := by
    intro n
    have := congrArg (fun y => Θ ((φ ^ n) y)) hw
    simp only [map_mul, map_pow, hpn, hit', hμ] at this
    simpa [hp] using this
  obtain ⟨a, z, haz⟩ := himg x
  obtain ⟨b, hb⟩ : μ ∣ a := by
    apply hI
    intro n
    have := congrArg (fun y => Θ ((φ ^ n) y)) (hx.symm.trans haz)
    simpa only [map_mul, map_add (f := _), hxn, hwn, hit', mul_zero, zero_mul, add_zero, eq_comm] using this
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, map_zero])
  have h1 : p ^ (r + 2) * x = t * (v * (p * i b + i μ ^ m * z)) := by
    have e := hx.symm.trans haz
    rw [hb, map_mul] at e
    rw [ht]
    linear_combination p * e + z * hw - (i μ * (p * i b + i μ ^ m * z)) * hv
  refine ⟨_, h1, ?_⟩
  set x' := v * (p * i b + i μ ^ m * z)
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, map_pow, hφp, hx, hφt] at h2
  apply mul_left_cancel₀ (mul_ne_zero hp0 ht0)
  linear_combination p ^ (r + 1) * h1 - h2

variable {l : ℕ} [Fact l.Prime]

theorem alg_eq (a : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) a =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem phi_nat (n : ℕ) : phiA l (n : Per.Acris l) = n := map_natCast _ _

theorem phi_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem j_alg {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [alg_eq, hj.on0]
  rfl

theorem theta_phi_mu (e : Per.Fl l) (he : e.untilt = 1) (n : ℕ) :
    Per.θ l ((Per.φA l)^[n] (mu e)) = 0 := by
  induction n generalizing e with
  | zero => simp [mu, he]
  | succ n ih =>
    have h : Per.φA l (mu e) = mu (e ^ l) := by
      simp only [mu, map_sub, map_one, GlobalTheory.RingIface.phiA_teich]
    rw [Function.iterate_succ_apply, h]
    exact ih _ (by rw [map_pow, he, one_pow])

theorem exists_w (e : Per.Fl l) (he : e.untilt = 1) : ∃ w : Per.Acris l,
    (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l e he
  have h : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  refine ⟨algebraMap (Per.Acris0 l) (Per.Acris l) w, ?_⟩
  rw [alg_eq, ← map_pow, ← h, map_mul, map_natCast]

theorem fil_div (C : Core l) (r : ℕ) (y : Per.BdRp l) (h : C.j C.t * y ∈ Per.FilP l (r + 1)) :
    y ∈ Per.FilP l r := by
  obtain ⟨hF, hreg, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε (GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C)
  obtain ⟨-, h1, h2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, hk, hun, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  rw [hF] at h h1 h2 ⊢
  obtain ⟨v, hv⟩ := h1
  have hvu : IsUnit v := by
    apply hun
    intro h0
    obtain ⟨c, hc⟩ := (hF _ _).1 ((hk v).1 h0)
    exact h2 ⟨c, by rw [hv, hc]; ring⟩
  obtain ⟨c, hc⟩ := h
  rw [← hvu.dvd_mul_left]
  refine ⟨c, sub_eq_zero.1 (hreg _ ?_)⟩
  rw [hv] at hc
  linear_combination hc

end GlobalTheory.MemLoc.FixR

namespace GlobalTheory.MemLoc
open FixR

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem fix_pow (l : ℕ) [Fact l.Prime] (C : Core l) (r : ℕ) (x : Per.Acris l)
    (hx : phiA l x = (l : Per.Acris l) ^ r * x) (hF : C.j x ∈ Per.FilP l r) :
    ∃ (z : ℤ_[l]) (k : ℕ), (l : Per.Acris l) ^ k * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) * C.t ^ r := by
  induction r generalizing x with
  | zero =>
    obtain ⟨z, hz⟩ := GlobalTheory.T.acris_frobenius_fixed_eq_padicInt l x (by simpa using hx)
    exact ⟨z, 0, by simpa using hz⟩
  | succ r ih =>
    have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
    haveI := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).1
    haveI : IsDomain (Per.Acris l) := (GlobalTheory.T.acrisToBdRPlus_injective l C.j C.j_cris).isDomain C.j
    obtain ⟨hFil, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
    obtain ⟨-, hk, -, hth, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
    obtain ⟨w, hw⟩ := exists_w C.ε he.1
    obtain ⟨t, u, htl, hu, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
    have htt : C.t = t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε t he.1 htl).1 _ C.t_log
    have hΘ : ∀ a, ((Per.θD l).comp C.j) (algebraMap (Per.Ainf l) (Per.Acris l) a) =
        (Per.θ l a : ℂ_[l]) := fun a => by
      rw [RingHom.comp_apply, j_alg C.j_cris, hth]
    have hl2 : l - 1 = (l - 2) + 1 := by
      have := (Fact.out : l.Prime).two_le
      omega
    obtain ⟨x', h1, h2⟩ := step_abs (algebraMap (Per.Ainf l) (Per.Acris l)) (Per.φA l) (phiA l)
      ((Per.θD l).comp C.j) (l : Per.Acris l) (by rw [map_natCast]; exact GlobalTheory.RingBasics.p_ne_zero)
      (phi_nat l) (phi_alg (l := l)) (mu C.ε)
      (fun n => by rw [hΘ, theta_phi_mu _ he.1]; rfl)
      (fun a ha => GlobalTheory.T.teichmullerTiltMinusOne_dvd_of_theta_frobenius_zero l C.ε he a fun n => Subtype.ext ((hΘ _).symm.trans (ha n)))
      w (l - 2) (hl2 ▸ hw) (GlobalTheory.T.frobenius_acris_decomposition_mu_power l C.ε he w hw) C.t u hu (htt.trans htu)
      (fun h => (GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C).2.2.1 (by rw [h, map_zero]; exact zero_mem _))
      (GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C) r x hx
      ((hk _).2 ((hFil _ _).2 ((pow_dvd_pow _ (by omega)).trans ((hFil _ _).1 hF))))
    have h3 : C.j x' ∈ Per.FilP l r := by
      apply fil_div C
      rw [← map_mul, ← h1, map_mul]
      exact Ideal.mul_mem_left _ _ hF
    obtain ⟨z, k, hz⟩ := ih x' h2 h3
    exact ⟨z, k + (r + 2), by linear_combination (l : Per.Acris l) ^ k * h1 + C.t * hz⟩

end GlobalTheory.MemLoc
end
end

section

namespace GlobalTheory.MemLoc.InvDR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem inv_ker_eq_zero (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hsep : ∀ y, (∀ n : ℕ, t ^ n ∣ y) → y = 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (z : R) (hz : θ z = 0) (hinv : ∀ g, σ g z = z) : z = 0 := by
  have key : ∀ m : ℕ, t ^ (m + 1) ∣ z := by
    intro m
    induction m with
    | zero => simpa using hker z hz
    | succ m ih =>
      obtain ⟨w, hw⟩ := ih
      have h1 : ∀ g, σ g w * c g ^ (m + 1) = w := by
        intro g
        have h := hinv g
        rw [hw, map_mul, map_pow, hσt] at h
        apply mul_left_cancel₀ (pow_ne_zero (m + 1) ht)
        rw [← h]
        ring
      have h2 : θ w = 0 := by
        refine tate ((m + 1 : ℕ) : ℤ) _ (by omega) fun g => ?_
        rw [zpow_natCast, ← hθ, ← map_pow, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hker w h2
      exact ⟨v, by rw [hw, hv]; ring⟩
  exact hsep z fun n => (pow_dvd_pow t (Nat.le_succ n)).trans (key n)

theorem eigen_eq (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * y) → ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem j_alg (C : Core l) (a : _root_.Formalism.Per.Ainf l) :
    C.j (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.RingIface.tower, C.j_cris.on0, aDp, RingHom.comp_apply, SubalgebraClass.coe_algebraMap]

set_option allowUnsafeReducibility true in
attribute [local irreducible] _root_.Formalism.Per.Acris _root_.Formalism.Per.Bcris

theorem invariants_BdR (l : ℕ) [Fact l.Prime] (C : Core l) (K : FinExt l) (b : _root_.Formalism.Per.BdR l)
    (hb : ∀ g ∈ GK K, _root_.Formalism.Per.σD g b = b) :
    ∃ y ∈ K.1, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (C.o y) = b := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  obtain ⟨-, ht1, ht2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, -, hoσ⟩ := GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec
  obtain ⟨-, hjσ, -⟩ := GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C
  have htate := GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension l C K
  have hast := GlobalTheory.T.cLTate_invariants_finiteExtension_mem l K
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  have hxt : x ∣ t := ⟨u, hu⟩
  let c : ↥(GK K) → _root_.Formalism.Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g.1 : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, _root_.Formalism.Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g.1 : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, _root_.Formalism.Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g.1).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : ↥(GK K), _root_.Formalism.Per.σDp g.1 t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, j_alg, ← C.o_sec.z]
  have hker' : ∀ y, _root_.Formalism.Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hsep : ∀ y : _root_.Formalism.Per.BdRp l, (∀ n : ℕ, t ^ n ∣ y) → y = 0 := fun y hy => by
    refine hcompl.toIsHausdorff.haus y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow_of_dvd hxt n).trans (hy n)
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : ↥(GK K), _root_.Formalism.Per.σC g.1 x * _root_.Formalism.Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g hg => by simpa only [hθc] using h ⟨g, hg⟩
  have hy : b * algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) t ^ n =
      algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : ↥(GK K), _root_.Formalism.Per.σDp g.1 y = c g ^ n * y := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g.1 g.2, map_mul, map_mul, map_pow, ← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_eq (_root_.Formalism.Per.θD l) (fun g : ↥(GK K) => _root_.Formalism.Per.σDp g.1) (fun g => _root_.Formalism.Per.σC g.1) c t ht0
    hker' hc (fun g y => hθ g.1 y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (_root_.Formalism.Per.θD l w) fun g hg => by rw [← hθ, hw' ⟨g, hg⟩]
  have hz : w - C.o k = 0 := by
    refine inv_ker_eq_zero (_root_.Formalism.Per.θD l) (fun g : ↥(GK K) => _root_.Formalism.Per.σDp g.1) (fun g => _root_.Formalism.Per.σC g.1) c t ht0
      hker' hsep (fun g y => hθ g.1 y) hσt tate _ ?_ fun g => ?_
    · rw [map_sub, C.o_sec.th, hkθ, sub_self]
    · have hg : g.1 k = k := g.2 ⟨k, hk⟩
      rw [map_sub, hw' g, hoσ, hg]
  refine ⟨k, hk, ?_⟩
  rw [← sub_eq_zero.1 hz]
  haveI : IsDomain (_root_.Formalism.Per.BdR l) := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

end GlobalTheory.MemLoc.InvDR
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.localPeriodRingsData_unramified_laws : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, (∀ c : ↥(MaximalUnramifiedExtension l), Per.φB l (C.u c) = C.u (C.σ c)) ∧ (∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) → Per.σB g (C.u c) = C.u c') ∧ (∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z) ∧ Function.Injective C.ι ∧ (∀ (g : GQ l) (b : Per.Bcris l), C.ι (Per.σB g b) = Per.σD g (C.ι b)) ∧ Per.IsCrisDR l C.ι := by
  first | exact @GlobalTheory.MemLoc.ULaws.u_laws | exact GlobalTheory.MemLoc.ULaws.u_laws | (intros; apply GlobalTheory.MemLoc.ULaws.u_laws <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone GlobalTheory.LocM

namespace GlobalTheory.MemberEt

theorem isEtaleCompletion_comp_bijective {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

theorem isEtaleCompletion_comp_openImmersion : ∀ (A X : Scheme.{0}) (g : A ⟶ X) [IsOpenImmersion g] (R : Type) [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ A), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro A X g _ R _ _ ξ h
  have hiso : IsIso (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))) :=
    (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective _ hb _ h

end GlobalTheory.MemberEt
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem latC_full_lattice : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), ∃ L : Submodule (𝓞 E) (Fin W.rank → E), (L : Set (Fin W.rank → E)) = latC W ∧ L.FG ∧ Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ := by
  intro E _ _ _ W
  refine ⟨W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)), ?_, W.standardTuple_isLattice.fg.map _, ?_⟩
  · ext x
    simp only [latC, SetLike.mem_coe, Submodule.mem_map, Set.mem_ofPred_eq]
    rw [← W.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨_, h, W.frame.equivFun.apply_symm_apply x⟩
  · have h : Submodule.span E (W.L0 : Set W.V) = ⊤ := by
      let U := Submodule.span E (W.L0 : Set W.V)
      change U = ⊤
      by_contra h
      let e : W.V ≃ₗ⋆[E] W.V :=
        (W.frame.equivFun.trans (starLinearEquiv E)).trans W.frame.equivFun.symm
      let g : W.V →ₗ[E] Module.Dual E U :=
        (LinearMap.domRestrict' U).comp (W.hT.comp e.toLinearMap)
      have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E W.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : E) : a • e z ∈ W.L0 := by
        rw [← W.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : W.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual E U => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : W.hT y (e z) = 0 := by
          have hh := W.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : E →ₗ[𝓞 E] W.L0 :=
        ((LinearMap.toSpanSingleton E _ (e z)).restrictScalars (𝓞 E)).codRestrict W.L0 hsmul
      let : Module.Finite (𝓞 E) W.L0 := Module.Finite.iff_fg.mpr W.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    have : ((W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin W.rank → E)) :
        Set (Fin W.rank → E)) = W.frame.equivFun.toLinearMap '' (W.L0 : Set W.V) := rfl
    rw [this, ← Submodule.map_span, h, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.Mem.Vol
end
