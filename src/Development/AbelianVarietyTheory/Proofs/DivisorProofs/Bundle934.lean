module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle006
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle910
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle911
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
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
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds

theorem sumBound_of_local : ∀ {F : Type} [Field F] [NumberField F], Formalism.PairingDivisionLocalBalance.CESum → ∀ (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ), 2 ≤ k → 16 ≤ finrank ℚ F * k →
    (∀ l : ℕ, l.Prime → cE z l ≤ finrank ℚ F * padicValNat l 2 + Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k)) → SumBound k z := by
  intro F _ _ hCE k z hk h16 hloc
  set f := finrank ℚ F with hf
  set X := f * k with hX
  have h2f : 2 * f ≤ X := by rw [hX, mul_comm 2 f]; exact Nat.mul_le_mul_left f hk

  have hvan : ∀ l : ℕ, l.Prime → X + 2 ≤ l → cE z l = 0 := by
    intro l hl hlX
    have hl2 : l ≠ 2 := by omega
    have hv : padicValNat l 2 = 0 := by
      rw [Nat.padicValNat_def]
      apply multiplicity_eq_zero_of_not_dvd
      intro h
      have := Nat.le_of_dvd (by norm_num : 0 < 2) h
      omega
    have hm : Formalism.PairingDivisionLocalBalance.mE l X = 0 := by
      unfold Formalism.PairingDivisionLocalBalance.mE
      rw [if_neg hl2, if_neg]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have := hloc l hl
    rw [hv, hm] at this
    simpa using this
  set S : Finset Nat.Primes := (Finset.range (X + 2)).subtype Nat.Prime with hS
  have hsupp : (Function.support fun l : Nat.Primes => (cE z l : ℝ) * Real.log (l : ℕ)) ⊆ (S : Set Nat.Primes) := by
    intro l hl
    simp only [Function.mem_support] at hl
    rw [Finset.mem_coe, hS]
    refine (Finset.mem_subtype (p := Nat.Prime) (a := (l : {p : ℕ // p.Prime}))).2 (Finset.mem_range.2 ?_)
    by_contra hlt
    apply hl
    rw [hvan l l.2 (by omega)]
    simp
  refine ⟨S.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hsub : ∑ l ∈ S, (cE z l : ℝ) * Real.log (l : ℕ) =
      ∑ l ∈ (Finset.range (X + 2)).filter Nat.Prime, (cE z l : ℝ) * Real.log l :=
    Finset.sum_subtype_eq_sum_filter (f := fun l : ℕ => (cE z l : ℝ) * Real.log l) (s := Finset.range (X + 2))
  rw [hsub]
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (hCE f X _ h16 h2f (fun l hl => (Finset.mem_filter.1 hl).2))
  have hlp := (Finset.mem_filter.1 hl).2
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hloc l hlp)
    (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))

end GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds
end

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.MinValClosed

theorem mE_le_padicValNat {l n a : ℕ} (hl : l.Prime) (hn : 2 ≤ n) (he : Even n) (ha : 2 ≤ a)
    (hac : a.Coprime l) : Formalism.PairingDivisionLocalBalance.mE l n ≤ padicValNat l (a ^ n - 1) := by
  haveI := Fact.mk hl
  unfold Formalism.PairingDivisionLocalBalance.mE
  split_ifs with h2 hd
  · subst h2
    have hodd : ¬ 2 ∣ a := by
      intro h
      have := Nat.Coprime.coprime_dvd_left h hac
      norm_num at this
    have ha1 : 1 < a := by omega
    have := padicValNat.pow_two_sub_one_ge ha1 hodd (by omega) he
    simp only [← Nat.padicValNat_def] at this
    omega
  · obtain ⟨k, rfl⟩ := hd
    have hl3 : 3 ≤ l := by have := hl.two_le; omega
    have hk : k ≠ 0 := by rintro rfl; simp at hn
    have hodd : Odd l := hl.odd_of_ne_two h2
    set b := a ^ (l - 1) with hb
    have hb1 : 1 < b := Nat.one_lt_pow (by omega) (by omega)
    have hfer : l ∣ b - 1 := by
      have := Nat.ModEq.pow_card_sub_one_eq_one hl hac
      exact (Nat.modEq_iff_dvd' hb1.le).mp this.symm
    have hnd : ¬ l ∣ b := by
      intro h
      have h1 : l ∣ a := hl.dvd_of_dvd_pow h
      have : l ∣ Nat.gcd a l := Nat.dvd_gcd h1 dvd_rfl
      rw [hac] at this
      exact hl.one_lt.ne' (Nat.dvd_one.mp this)
    have hpow : a ^ ((l - 1) * k) - 1 = b ^ k - 1 ^ k := by rw [pow_mul, one_pow]
    rw [hpow]
    have hval := padicValNat.pow_sub_pow hodd hb1 (by simpa using hfer) hnd hk
    simp only [← Nat.padicValNat_def] at hval
    rw [hval]
    have hv1 : 1 ≤ padicValNat l (b - 1) := by
      rw [Nat.padicValNat_def]
      exact one_le_multiplicity_of_dvd (by omega) hfer
    have hvl : padicValNat l (l - 1) = 0 := by
      rw [Nat.padicValNat_def]
      apply multiplicity_eq_zero_of_not_dvd
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) hk, hvl]
    omega
  · exact Nat.zero_le _

theorem mMin_eq_mE : Formalism.PairingDivisionLocalBalance.MinVal → ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n → mMin l n = Formalism.PairingDivisionLocalBalance.mE l n := by
  intro hmv l n hl hn he
  apply le_antisymm
  · obtain ⟨a, ha, hac, hv⟩ := hmv l n hl hn he
    exact Nat.sInf_le ⟨a, ha, hac, hv.symm⟩
  · obtain ⟨a, ha, hac, hv⟩ := mMin_mem hl.one_lt.le n
    rw [hv]
    exact mE_le_padicValNat hl hn he ha hac

end GlobalTheory.MinValClosed
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FinitePlacesCompare

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

variable {K : Type} [Field K] [NumberField K]

theorem lw_nonneg (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

omit [NumberField K] in
theorem localization_mono' {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    {L L' : Submodule (𝓞 K) W} (h : L ≤ L') : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem primePow_anti (w : HeightOneSpectrum (𝓞 K)) {n n' : ℤ} (h : n' ≤ n) : primePow w n ≤ primePow w n' := by
  have hP : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot
  obtain ⟨k, rfl⟩ := Int.le.dest h
  have h1 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ k ≤ 1 := by
    rw [← FractionalIdeal.coeIdeal_pow]; exact FractionalIdeal.coeIdeal_le_one
  have h2 : (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (n' + (k : ℤ)) ≤
      (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' := by
    rw [zpow_add₀ hP, zpow_natCast]
    calc _ ≤ (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n' * 1 := by gcongr
      _ = _ := mul_one _
  exact FractionalIdeal.coe_le_coe.mpr h2

theorem scaledAt_anti {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) (Fin d → K)) {n n' : ℤ}
    (h : n' ≤ n) : scaledAt w n B ≤ scaledAt w n' B := by
  refine localization_mono' _ (Submodule.span_mono ?_)
  rintro z ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, primePow_anti w h ha, x, hx, rfl⟩

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

end GlobalTheory.FinitePlacesCompare
end
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.blockGLHom_conj_permMatrix_of_blocks_match : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ) (w : Equiv.Perm (Fin r)), (∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) → ∀ i : Fin r, (block b (b i)).card = (block b' (b' (w i))).card ∧ ∀ (d : ℕ) (h : (block b (b i)).card = d) (h' : (block b' (b' (w i))).card = d), ∃ π : GL (Fin d) F, ∀ g : GL (Fin d) F, (blockHom F b' (b' (w i)) h' (π * g * π⁻¹) : GL (Fin r) F) * permGL F w = permGL F w * (blockHom F b (b i) h g : GL (Fin r) F) := by
  first | exact @GlobalTheory.Proof.BlockConj.blockHom_conj_permGL | exact GlobalTheory.Proof.BlockConj.blockHom_conj_permGL | (intros; apply GlobalTheory.Proof.BlockConj.blockHom_conj_permGL <;> assumption)
end

section

open scoped ComplexOrder Matrix
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.BrNormCompare

open GlobalTheory.IndefiniteRowSideFullHecke

theorem gramSum_eq_sumGram {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) :
    OrthogonalNormSquareSum.gramSum hN G' g = ScaledCoisometryNorms.sumGram N G' g := by
  ext a b
  simp only [OrthogonalNormSquareSum.gramSum, ScaledCoisometryNorms.sumGram, Matrix.of_apply]
  by_cases ha : a.1 < n
  · simp [ha]
  · by_cases hb : b.1 < n
    · simp [ha, hb]
    · have h1 : a = Br.iL hN := Fin.ext (by have := a.2; simp only [Br.iL]; omega)
      have h2 : b = Br.iL hN := Fin.ext (by have := b.2; simp only [Br.iL]; omega)
      rw [dite_eq_right ha, dite_eq_right ha, if_neg hb, if_neg hb, if_pos ⟨h1, h2⟩]

theorem length_eq {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) (hs : ∀ x : K, s (star x) = star (s x)) (g t : K) :
    s (star t * g * t) = ((‖s t‖ ^ 2 : ℝ) : ℂ) * s g := by
  rw [map_mul, map_mul, hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

section

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {N n : ℕ}

theorem isScaledCoisometry_iff (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' P ρ ↔ 0 < ρ ^ 2 ∧ ScaledCoisometryNorms.IsScaledCoisometry s lam sg G G' P (ρ ^ 2) := by
  unfold OrthogonalNormSquareSum.IsScaledCoisometry ScaledCoisometryNorms.IsScaledCoisometry
  refine and_congr_left' ⟨fun h => pow_pos h 2, fun h => lt_of_le_of_ne hρ ?_⟩
  rintro rfl
  simp at h

theorem factor_nonneg (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) {T : ℝ} (hT : 0 < T) :
    0 ≤ OrthogonalNormSquareSum.factor hN lam sg T :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (abs_nonneg _)) (Real.sqrt_nonneg _)

theorem prod_factor_sq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ^ 2 = ScaledCoisometryNorms.brSq hN lam sg T := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun τ _ => OrthogonalNormSquareSum.factor_sq hN _ _ hT

theorem const_eq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg = ScaledCoisometryNorms.brSq hN lam sg T :=
  (ScaledCoisometryNorms.brSq_eq hN lam sg hT).symm

theorem whole_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K) (t : ι → K) {T : ℝ} (hT : 0 < T) :
    (OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' (Br.brAt hN lam sg t) (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ∧
      OrthogonalNormSquareSum.HasOpNormSq s lam G sg G' (Br.brAt hN lam sg t)
        (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg)) ↔
    ScaledCoisometryNorms.NormConcl s hN lam sg G G' t T := by
  rw [isScaledCoisometry_iff s lam G sg G' _ (Finset.prod_nonneg fun τ _ => factor_nonneg hN _ _ hT),
    prod_factor_sq hN lam sg hT, const_eq hN lam sg hT, and_assoc]
  rfl

theorem single_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin n) (Fin n) K) (t : K) {T : ℝ} (hT : 0 < T) :
    OrthogonalNormSquareSum.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ => G) (fun _ : Unit => sg) (fun _ => G')
        (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t) (OrthogonalNormSquareSum.factor hN lam sg T) ↔
      0 < ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T ∧
        ScaledCoisometryNorms.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ : Unit => sg) (fun _ => G) (fun _ => G')
          (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t)
          (ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T) := by
  rw [isScaledCoisometry_iff _ _ _ _ _ _ (factor_nonneg hN lam sg hT), ← prod_factor_sq hN _ _ hT]
  simp

end

theorem lastMapNorm_iff_brNorm : OrthogonalNormSquareSum.LastMapNorm ↔ ScaledCoisometryNorms.BrNorm := by
  constructor
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG g t T hT ht
    have := (h K s hs ι N n hN lam sg h1 h2 G' hG T hT g t fun τ => by rw [length_eq s hs, ht τ]).2
    rw [whole_iff s hN lam sg _ G' t hT] at this
    simpa only [gramSum_eq_sumGram] using this
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG T hT g t ht
    have ht' : ∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ) := fun τ => by rw [← length_eq s hs, ht τ]
    refine ⟨fun τ => ?_, ?_⟩
    · have := h K s hs Unit N n hN (fun _ => lam τ) (fun _ => sg τ) (fun _ => h1 τ) (fun _ => h2 τ) (fun _ => G' τ)
        (fun _ => hG τ) (fun _ => g τ) (fun _ => t τ) T hT (fun _ => ht' τ)
      rw [single_iff s hN _ _ _ _ _ hT, gramSum_eq_sumGram]
      exact ⟨this.1, this.2.1⟩
    · rw [whole_iff s hN lam sg _ G' t hT]
      simpa only [gramSum_eq_sumGram] using h K s hs ι N n hN lam sg h1 h2 G' hG g t T hT ht'

theorem last_ineq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h1 : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (a : ℝ) (ha : ∀ τ, (((lam τ).spread : ℤ) : ℝ) ≤ 2 * a) :
    ∑ τ, (2 * ((N : ℝ) - 1) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ≤
      2 * ∑ τ, ((N : ℝ) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) ^ 2) * Real.log (2 * a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hd : (0 : ℤ) ≤ OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) := by
    refine Finset.sum_nonneg fun i _ => le_min ?_ (Finset.sum_nonneg fun j _ => (h1 τ j).1)
    have := h1 τ i
    simp only [Br.aBr, Br.bBr] at this
    omega
  have hs : (1 : ℤ) ≤ (lam τ).spread := by
    have hpos : 0 < N := by omega
    have := (lam τ).anti (show (⟨0, hpos⟩ : Fin N) ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.mpr (Nat.zero_le _))
    simp only [DomWeight.spread, dif_pos hpos]
    omega
  have hd' : (0 : ℝ) ≤ ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) := by exact_mod_cast hd
  have hs' : (1 : ℝ) ≤ (((lam τ).spread : ℤ) : ℝ) := by exact_mod_cast hs
  have hl : 0 ≤ Real.log (2 * a) := Real.log_nonneg (hs'.trans (ha τ))
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  nlinarith [sq_nonneg (N : ℝ)]

end GlobalTheory.BrNormCompare
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbertEisenstein_fourier_expansion_support : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ), HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧ (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : Emb F, 0 < i ξ) ∧ ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w) ((cK F k : ℂ) * G w / (omegaFactor 𝔞 : ℂ) ^ k) := by
  first | exact @GlobalTheory.HilbFam.fourier_with_support | exact GlobalTheory.HilbFam.fourier_with_support | (intros; apply GlobalTheory.HilbFam.fourier_with_support <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowAmple

theorem pw_pw_mul {X : Scheme.{0}} (H : LB X) (a b : ℤ) :
    GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw H a) b = GlobalTheory.AbLaw.pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem relAmple_pw : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left),
    L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  intro R _ B L hL hA a ha
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R B.left B.hom (GlobalTheory.AbLaw.pw L d) n s
    (GlobalTheory.AbLaw.isLB_pw hL d) hs a ha
  have e : GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d : ℤ)) (a : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ) := by
    rw [pw_pw_mul, pw_pw_mul, mul_comm]
  have h2 : ∃ t : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy B.hom _ t := by
    rw [← e]; exact ⟨s', hs'⟩
  obtain ⟨t, ht⟩ := h2
  exact GlobalTheory.Unif.relAmple_of_veryAmpleBy (GlobalTheory.AbLaw.isLB_pw hL a) hd t ht

end GlobalTheory.PowAmple
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.isClosedImmersion_of_veryAmpleSections_compatible : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → IsClosedImmersion φ := by
  first | exact @GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat | exact GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat | (intros; apply GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundlePow_h1Vanishes_geometricFibre_all : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  first | exact @GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all | exact GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all | (intros; apply GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)

namespace GlobalTheory.CechPic

theorem intCast_mul_eq_zero_of_isIntegral {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X]
    (hc : CharZero Γ(X, ⊤)) (W : X.Opens) {m : ℤ} (hm : m ≠ 0) {c : Γ(X, W)}
    (h : (m : Γ(X, W)) * c = 0) : c = 0 := by
  by_cases hW : Nonempty W
  · have hinj := AlgebraicGeometry.map_injective_of_isIntegral X (homOfLE (le_top : W ≤ ⊤))
    have hm' : (m : Γ(X, W)) ≠ 0 := by
      intro h0
      apply hm
      have : (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (m : Γ(X, ⊤)) =
          (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom 0 := by
        rw [map_intCast, map_zero, h0]
      exact_mod_cast hinj this
    exact (mul_eq_zero.1 h).resolve_left hm'
  · have hb : W = ⊥ := eq_bot_iff.2 fun x hx => (hW ⟨⟨x, hx⟩⟩).elim
    subst hb
    have := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
    exact Subsingleton.elim _ _

theorem cechLB_X_noZSMulDivisors : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) →
    ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 →
    ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  intro X _ hc f M κ _ D n m hm x hx
  have key : ∀ (V : X.Opens) (y : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V), m • y = 0 → y = 0 := by
    intro V y hy
    refine GlobalTheory.AbLaw.SecOnR.ext (R := ℤ) (f := f) fun i => ?_
    let c : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V →+ Γ(X, V ⊓ M.U i) :=
      { toFun := fun z => GlobalTheory.AbLaw.SecOnR.coord z i
        map_zero' := GlobalTheory.AbLaw.SecOnR.coord_zero i
        map_add' := fun z w => GlobalTheory.AbLaw.SecOnR.coord_add z w i }
    have hi : c (m • y) = c 0 := congrArg c hy
    rw [map_zsmul, map_zero, zsmul_eq_mul] at hi
    exact intCast_mul_eq_zero_of_isIntegral hc _ hm hi
  funext s
  refine key _ (x s) ?_
  exact congrFun hx s

end GlobalTheory.CechPic
end

section

open NumberField GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsCuspForm φ → GlobalTheory.CuspRep.IsCuspidal (GlobalTheory.CuspRep.lie E a X φ).1 := by
  first | exact @GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm | exact GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm | (intros; apply GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm <;> assumption)
end
