module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedEmbeddingOfInvolutionAlgebra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle205
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle090
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle210
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyCon
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial IsLocalRing

theorem pow_eq_one_eq_of_residue {S : Type*} [CommRing S] [IsLocalRing S] {n : ℕ} (hn : IsUnit (n : S))
    {y₁ y₂ : S} (h₁ : y₁ ^ n = 1) (h₂ : y₂ ^ n = 1) (h : residue S y₁ = residue S y₂) : y₁ = y₂ := by
  apply GlobalTheory.UnitLemma.UnrAny.pow_eq_one_eq_of_residue <;> assumption

theorem card_sub_one_isUnit (S : Type*) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] :
    IsUnit ((Nat.card (ResidueField S) - 1 : ℕ) : S) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub Nat.card_pos, Nat.cast_one]
  haveI := Fintype.ofFinite (ResidueField S)
  rw [Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
  simp

theorem exists_unr_embedding : ∀ (K : UQ), K.Odd → ∀ B : InvAlg K, B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by
  intro K _ B hu _ hi hl d hcard K' φ hU hz
  obtain ⟨z, hzp, hzadj⟩ := hz
  set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hR
  have hq0 : K.q ≠ 0 := by
    intro h0
    have : 0 < Nat.card (ResidueField K.O) := Nat.card_pos
    rw [K.card_res, h0] at this
    simp at this
  have hq' : K'.q = K.q ^ d := hU.1
  set N := K'.q ^ 2 - 1 with hNdef
  have hcardR : Nat.card (ResidueField R) = K'.q ^ 2 := by rw [hcard, hq', ← pow_mul, mul_comm]
  have hd : d ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq'
    rw [hq', one_pow] at hcardR
    have : Subsingleton (ResidueField R) := (Nat.card_eq_one_iff_unique.1 hcardR).1
    exact not_subsingleton (ResidueField R) this
  haveI : Finite (ResidueField R) := Nat.finite_of_card_ne_zero (by rw [hcardR, hq']; exact pow_ne_zero _ (pow_ne_zero _ hq0))

  haveI : Module.Finite K.O R := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : HenselianLocalRing K.O := GlobalTheory.henselianLocalRing_of_henselianRing K.O
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_finite K.O R
  have h1q : 1 < K'.q ^ 2 := by rw [← K'.card_res]; exact Finite.one_lt_card
  have hN : N ≠ 0 := by omega
  have hNR : IsUnit (N : R) := by
    have := card_sub_one_isUnit R
    rwa [hcardR] at this
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul K.O K'.E := (faithfulSMul_iff_algebraMap_injective _ _).2
    (φ.injective.comp (IsFractionRing.injective K.O K.E))
  have hzN : z ^ N = 1 := hzp.pow_eq_one
  have hzint : IsIntegral K.O z :=
    ⟨_, monic_X_pow_sub_C (1 : K.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hmdvd : minpoly K.O z ∣ X ^ N - C 1 := minpoly.isIntegrallyClosed_dvd hzint (by simp [hzN])
  obtain ⟨yR, hyR⟩ := GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one R ((minpoly K.O z).map (algebraMap K.O R))
    ((minpoly.monic hzint).map _)
    (by rw [(minpoly.monic hzint).natDegree_map]; exact (minpoly.natDegree_pos hzint).ne')
    (by
      rw [hcardR]
      have := Polynomial.map_dvd (algebraMap K.O R) hmdvd
      simpa using this)
  have hyN : yR ^ N = 1 := by
    obtain ⟨h, hh⟩ := hmdvd
    have := congrArg (fun p => (p.map (algebraMap K.O R)).eval yR) hh
    simp only [Polynomial.map_mul, eval_mul, hyR, zero_mul] at this
    simpa [sub_eq_zero] using this

  have hzE : IsIntegral K.E z := hzint.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzE hzadj
  have hgen : pb.gen = z := rfl
  have hy : aeval (yR : B.A) (minpoly K.E pb.gen) = 0 := by
    rw [hgen, minpoly.isIntegrallyClosed_eq_field_fractions' K.E hzint, aeval_map_algebraMap,
      ← Polynomial.aeval_subalgebra_coe, aeval_def, ← eval_map, hyR]
    rfl
  let ψ : K'.E →+* B.A := (pb.lift (yR : B.A) hy).toRingHom
  have hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e := fun e => (pb.lift (yR : B.A) hy).commutes e
  have hψz : ψ z = yR := pb.lift_gen _ hy
  haveI : Nontrivial B.A := nontrivial_of_ne (0 : B.A) 1 fun h => zero_ne_one (Subtype.ext h : (0 : R) = 1)
  have hψi : Function.Injective ψ := ψ.injective

  let τR : R →+* R := (B.σ : B.A →+* B.A).restrict R R fun x hx => Orbit.adjoin_stable B hu hi hx
  have hτR : ∀ x : R, (τR x : B.A) = B.σ x := fun x => rfl
  have hτ2 : ∀ x, τR (τR x) = x := fun x => Subtype.ext (B.σ_σ x)
  obtain ⟨a, b, hab, hres⟩ := K.c_res
  have hτa : τR (algebraMap K.O R a) = algebraMap K.O R b := by
    apply Subtype.ext
    rw [hτR]
    change B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A b
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hab, ← IsScalarTower.algebraMap_apply]
  have hne : residue R (τR (algebraMap K.O R a)) ≠ residue R (algebraMap K.O R a) := by
    rw [hτa]
    intro h
    have h2 : residue R (algebraMap K.O R (a - b)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff] at h2
    have hu' : IsUnit (a - b) := by
      by_contra hc
      exact hres ((IsLocalRing.mem_maximalIdeal _).2 hc)
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 (hu'.map _)
  obtain ⟨hfr1, hfr2⟩ := GlobalTheory.T.involution_residue_pow_and_roots_of_unity R K'.q hcardR τR hτ2 ⟨_, hne⟩
  choose τ' hτ' using K'.c_int
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let cO : K'.O →+* K'.O :=
    { toFun := τ'
      map_one' := hinj' (by rw [← hτ']; simp)
      map_mul' := fun a b => hinj' (by simp [← hτ'])
      map_zero' := hinj' (by rw [← hτ']; simp)
      map_add' := fun a b => hinj' (by simp [← hτ']) }
  have hcO : ∀ x, algebraMap K'.O K'.E (cO x) = K'.c (algebraMap K'.O K'.E x) := fun x => (hτ' x).symm
  have hc2 : ∀ x, cO (cO x) = x := fun x => hinj' (by rw [hcO, hcO, K'.c_c])
  obtain ⟨a', b', hab', hres'⟩ := K'.c_res
  have hne' : residue K'.O (cO a') ≠ residue K'.O a' := by
    have : cO a' = b' := hinj' (by rw [hcO, hab'])
    rw [this]
    intro h
    apply hres'
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  obtain ⟨-, hfc⟩ := GlobalTheory.T.involution_residue_pow_and_roots_of_unity K'.O K'.q K'.card_res cO hc2 ⟨_, hne'⟩
  obtain ⟨zO, hzO⟩ : ∃ zO : K'.O, algebraMap K'.O K'.E zO = z :=
    IsIntegrallyClosed.isIntegral_iff.1
      ⟨_, monic_X_pow_sub_C (1 : K'.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hzON : zO ^ N = 1 := hinj' (by rw [map_pow, hzO, hzN, map_one])
  have hcz : K'.c z = z ^ K'.q := by
    rw [← hzO, ← hcO, hfc zO hzON, map_pow]
  have hσz : B.σ (ψ z) = ψ (K'.c z) := by
    rw [hψz, ← hτR, hfr2 yR hyN, hcz, map_pow, hψz]
    rfl
  have hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e) := by
    intro e
    have he : e ∈ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} := hzadj ▸ Algebra.mem_top
    induction he using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hσz
    | algebraMap e =>
      change B.σ (ψ (φ e)) = ψ (K'.c (φ e))
      rw [← hU.2.1, hψ, hψ, B.σ_alg]
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | mul x y _ _ hx hy => simp only [map_mul, hx, hy]

  have hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ R := by
    intro y
    have hadj := GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic K K' d φ hU hd z hzp hzadj _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hd y)
    generalize algebraMap K'.O K'.E y = x at hadj ⊢
    induction hadj using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hψz]; exact yR.2
    | algebraMap a =>
      change ψ (φ (algebraMap K.O K.E a)) ∈ R
      rw [hψ, ← IsScalarTower.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨ψ, hψ, hσ, hO, ?_⟩
  haveI : NeZero N := ⟨hN⟩
  have hcoe : ∀ n : ℕ, ((yR ^ n : R) : B.A) = ψ (z ^ n) := fun n => by rw [map_pow, hψz]; rfl
  have hwp : IsPrimitiveRoot (residue R yR) N := by
    refine ⟨by rw [← map_pow, hyN, map_one], fun l hl => hzp.dvd_of_pow_eq_one l ?_⟩
    have h1 : yR ^ l = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [map_pow, hl, map_one])
    apply hψi
    rw [← hcoe, h1, map_one]
    rfl
  set gR : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ with hgR
  have hgu : gR * τR gR = 1 := Subtype.ext hu
  have hg0 : residue R gR ≠ 0 := (IsUnit.map (residue R) (⟨⟨gR, τR gR, hgu, by rw [mul_comm]; exact hgu⟩, rfl⟩ : IsUnit gR)).ne_zero
  have hgN : residue R gR ^ N = 1 := by
    haveI := Fintype.ofFinite (ResidueField R)
    have := FiniteField.pow_card_sub_one_eq_one _ hg0
    rwa [← Nat.card_eq_fintype_card, hcardR] at this
  obtain ⟨j, -, hj⟩ := hwp.eq_pow_of_pow_eq_one hgN
  let zOu : K'.Oˣ := Units.ofPowEqOne zO N hzON hN
  have hs : algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O) = z ^ j := by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_ofPowEqOne, hzO]
  refine ⟨zOu ^ j, ?_, ?_⟩
  · set e := j + j * K'.q with he
    have hres : residue R (yR ^ e) = 1 := by
      rw [map_pow, he, pow_add, pow_mul, hj, ← hfr1 gR, ← map_mul, hgu, map_one]
    have hye : yR ^ e = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [hres, map_one])
    rw [hs, map_pow, hcz, ← pow_mul, ← pow_add, mul_comm K'.q j, ← he]
    apply hψi
    rw [← hcoe, hye, map_one]
    rfl
  · have : (⟨ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)), hO _⟩ : R) = yR ^ j :=
      Subtype.ext (by
        change ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)) = ((yR ^ j : R) : B.A)
        rw [hs, hcoe])
    rw [this, map_pow, hj]

end GlobalTheory.UnitLemma.Unr
end
end

section

noncomputable section

open Formalism.Per Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable {l : ℕ} [Fact l.Prime]

theorem pw_zero (x : Fl l) : pw 0 x = x := by simp [pw]

theorem pw_succ (k : ℤ) (x : Fl l) : pw (k + 1) x = pw k x ^ l := by
  unfold pw
  rw [add_comm, zpow_add, zpow_one]
  rfl

theorem pw_add (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  unfold pw
  rw [zpow_add]
  rfl

theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_zero]
  | succ n ih => rw [Nat.cast_succ, pw_succ, ih, ← pow_mul, pow_succ]

theorem sh_pow (x : Fl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  unfold sh
  rw [map_pow]; push_cast; rfl

theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
theorem two_le_l : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le

theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  apply GlobalTheory.PSer.PwLaws.norm_sh_pw <;> assumption

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]; simp

def sz (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (n : ℤ) : ℝ :=
  ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))

theorem norm_term (h j : ℕ) (x : Fl l) (n : ℤ) :
    ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖ = sz l h j ‖sh x‖ n := by
  rw [norm_mul, norm_zpow, norm_sh_pw]; rfl

theorem sz_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℤ) : 0 ≤ sz l h j r n :=
  mul_nonneg (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hr _)

theorem sz_mono (h j : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (n : ℤ) :
    sz l h j r n ≤ sz l h j s n :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs (zpow_nonneg l_pos.le _))
    (zpow_nonneg (norm_nonneg _) _)

theorem tendsto_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (sz l h j r) cofinite (𝓝 0) := by
  have hl := l_pos (l := l)
  have hl2 := two_le_l (l := l)
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · have hb : Tendsto (fun n : ℤ => (l : ℝ) ^ n) atBot (𝓝 0) := by
      have := (tendsto_rpow_atBot_of_base_gt_one (l : ℝ) (by linarith)).comp
        ((tendsto_intCast_atBot_iff (R := ℝ)).2 (tendsto_id (α := ℤ) (x := atBot)))
      refine this.congr fun n => ?_
      simp
    refine squeeze_zero (sz_nonneg h j hr) (fun n => ?_) hb
    unfold sz
    rw [norm_l, inv_zpow', neg_neg]
    exact mul_le_of_le_one_right (zpow_nonneg hl.le _)
      (Real.rpow_le_one hr hr1.le (zpow_nonneg hl.le _))
  · rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
    have h1 : Tendsto (fun n : ℕ => l ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp h1
    refine squeeze_zero (fun n => sz_nonneg h j hr _) (fun n => ?_) h2
    simp only [Function.comp, sz]
    rw [norm_l, inv_zpow', neg_neg, zpow_natCast, Nat.cast_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl.le _)
    have : ((n : ℤ) * h + j : ℤ) = ((n * h + j : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
    refine pow_le_pow_of_le_one hr hr1.le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos ?_)
    nlinarith

theorem summable_lam {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} (hx : ‖sh x‖ < 1) :
    Summable fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_term]
  exact tendsto_sz hh j (norm_nonneg _) hx

theorem bdd_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    BddAbove (Set.range (sz l h j r)) :=
  (tendsto_sz hh j hr hr1).bddAbove_range_of_cofinite

theorem gam_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gam l h j r :=
  Real.iSup_nonneg (sz_nonneg h j hr)

theorem norm_lam_le {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} {r : ℝ} (hx : ‖sh x‖ ≤ r) (hr : r < 1) :
    ‖lam h j x‖ ≤ gam l h j r := by
  have h0 : 0 ≤ r := (norm_nonneg _).trans hx
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gam_nonneg h j h0) fun n => ?_
  rw [norm_term]
  exact (sz_mono h j (norm_nonneg _) hx n).trans (le_ciSup (bdd_sz hh j h0 hr) n)

theorem lam_shift (h j : ℕ) (x : Fl l) : lam h (j + h) x = l * lam h j x := by
  unfold lam
  rw [← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n : ℤ => (l : ℂ_[l]) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)))]
  refine tsum_congr fun n => ?_
  have h1 : (n * h + ((j + h : ℕ) : ℤ)) = (n + 1) * h + j := by push_cast; ring
  simp only [Equiv.coe_addRight]
  rw [h1, ← mul_assoc, ← zpow_one_add₀ GlobalTheory.RingBasics.p_ne_zero]
  congr 2; ring

theorem lam_pow (h j k : ℕ) (x : Fl l) : lam h j (x ^ l ^ k) = lam h (j + k) x := by
  unfold lam
  refine tsum_congr fun n => ?_
  rw [← pw_nat, ← pw_add]
  congr 3
  push_cast; ring

end GlobalTheory.PSer.Laws

namespace GlobalTheory.PSer

open Laws

theorem lam_hasSum_norm_le_frob : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 →
    ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧
      ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧
      lam h j (x ^ l) = lam h (j + 1) x := by
  intro l _ h j r x hh hr hx
  refine ⟨(summable_lam hh j (hx.trans_lt hr)).hasSum, norm_lam_le hh j hx hr, ?_, ?_⟩
  · rw [lam_pow, lam_shift]
  · have := lam_pow (l := l) h j 1 x
    rwa [pow_one] at this

end GlobalTheory.PSer

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransfer

open scoped Pointwise
open UpperTheory.V.Base (galOf galEmb galEmbTop range_galEmb galEmb_mem)
open Formalism.L2.Host (IsUnitAt IsUnifAt aboveF)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

section Group

variable {Γ B : Type} [Group Γ] [CommGroup B] {H : Subgroup Γ} [H.FiniteIndex] (φ : H →* B)

end Group

section Places

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]


variable [Algebra K L] [IsScalarTower K L Ω]

end Places

section Ideles

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {K} in
theorem loc_same (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

variable {K} in
theorem loc_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleMap_apply (a : Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (ideleMap K L a).val.2 w = finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

end Ideles

section Artin

variable {K L Ω B : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [CommGroup B]

variable [Algebra K L]


variable [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

end Artin

end GlobalTheory.ArtinTransfer

end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  first | exact @GlobalTheory.JR.orb_integrand_isTest | exact GlobalTheory.JR.orb_integrand_isTest | (intros; apply GlobalTheory.JR.orb_integrand_isTest <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F), orbG M f' (act g Y) = orbG M f' Y) ∧ (∀ (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E), orbU M f (actU g X) = orbU M f X) ∧ (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ a₀ : Inv r F, Delta a₀ ≠ 0 → ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀)) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a₀ : Inv r F) (X₀ : Hn r F E), Delta a₀ ≠ 0 → HasInv X₀ a₀ → ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  first | exact @GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant | exact GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant | (intros; apply GlobalTheory.JR.OrbLC.orbital_integrals_invariant_locally_constant <;> assumption)
end
