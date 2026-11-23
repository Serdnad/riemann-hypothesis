module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle034
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle047
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.exists_unitarySignatureStabiliserCosetCutoff : ∀ (c : CDHaar) (P Q P' Q' : ℕ) (x₀ : ActionCoordinates.Wsp P Q), ActionCoordinates.qf x₀ ≠ 0 → ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q), ActionCoordinates.IsPerpFrame x₀ j ι → Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} → ∃ u : UpqT P Q → ℝ≥0∞, Measurable u ∧ ∀ g, Measurable (fun h => u (ι h * g)) ∧ ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1 := by
  first | exact @GlobalTheory.StabiliserCutoff.exists_cutoff | exact GlobalTheory.StabiliserCutoff.exists_cutoff | (intros; apply GlobalTheory.StabiliserCutoff.exists_cutoff <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.selfDual_sumPairing_map_eq_pi : ∀ (T V W : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] (e : W ≃ₜ+ (T → V)) (ε : ℝ) (β : V → V → ℝ) (μ₀ : Measure V), μ₀.IsAddHaarMeasure → ActionCoordinates.IsSelfDualFor ε β μ₀ → ∀ (μ : Measure W) (χ : W → W → ℂ), (∀ x y, χ x y = Complex.exp (2 * Real.pi * Complex.I * ((ε * ∑ ρ, β (e x ρ) (e y ρ) : ℝ) : ℂ))) → SelfDual μ χ → μ.map e = Measure.pi fun _ : T => μ₀ := by
  first | exact @GlobalTheory.SelfDualProduct.map_eq_pi | exact GlobalTheory.SelfDualProduct.map_eq_pi | (intros; apply GlobalTheory.SelfDualProduct.map_eq_pi <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.hermitianNormFibre_lintegral_ne_zero_of_pos : ActionCoordinates.QuotientMeasure → CDHaar → ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x₀ = β → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : ActionCoordinates.Wsp P Q → ℝ, Continuous φ → 0 < φ x₀ → ∫⁻ y, ENNReal.ofReal (φ y) ∂(fib β) ≠ 0 := by
  first | exact @GlobalTheory.FibrePositive.fibre_lintegral_ne_zero | exact GlobalTheory.FibrePositive.fibre_lintegral_ne_zero | (intros; apply GlobalTheory.FibrePositive.fibre_lintegral_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.exists_localComponent_adelicAddChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), LocalAdditiveCharacterDual.IndexFinite F ψ v → ∃ χ : AddChar (Fv F v) ℂ, PlaceSplittingTypes.IsLocalChar F v χ ∧ ∀ t, χ t = psiV F ψ v t := by
  first | exact @GlobalTheory.LocalComponentChar.exists_localChar | exact GlobalTheory.LocalComponentChar.exists_localChar | (intros; apply GlobalTheory.LocalComponentChar.exists_localChar <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LatticePeriodEtaProof

open Formalism.MainNotions.TaylorLogMetric GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement
open scoped UpperHalfPlane

theorem lattice_discriminant_eq_weierstrass_discr (Λ : AddSubgroup ℂ) : discr Λ = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr Λ := rfl

theorem latt_eq_closure (ω₁ τ : ℂ) : latt ω₁ τ = AddSubgroup.closure {ω₁, ω₁ * τ} := by
  ext w
  rw [mem_latt, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_mem_closure]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨![n, m], by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v 1, v 0, by ring⟩

theorem discrEta : DiscrEta := by
  intro ω₁ τ h
  rw [lattice_discriminant_eq_weierstrass_discr, latt_eq_closure]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_discr ω₁ τ h τ.2

theorem im_conj_mul (ω τ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (ω * ((m : ℂ) + (n : ℂ) * τ)) * (ω * ((m' : ℂ) + (n' : ℂ) * τ))).im =
      ‖ω‖ ^ 2 * τ.im * ((m * n' - n * m' : ℤ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_im, Complex.mul_re]
  ring

theorem areaEq : AreaEq := by
  intro ω₁ τ h
  have hy : 0 < τ.im := τ.2
  have hω : 0 < ‖ω₁‖ := norm_pos_iff.2 h
  have hc : 0 < ‖ω₁‖ ^ 2 * τ.im := by positivity
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨hc, ω₁ * ((1 : ℤ) + ((0 : ℤ) : ℂ) * (τ : ℂ)), ⟨1, 0, rfl⟩,
    ω₁ * (((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ : ℂ)), ⟨0, 1, rfl⟩, ?_⟩, ?_⟩
  · rw [im_conj_mul]
    norm_num [UpperHalfPlane.coe_im, abs_of_pos hy]
  · rintro a ⟨ha, w₁, ⟨m, n, rfl⟩, w₂, ⟨m', n', rfl⟩, rfl⟩
    rw [im_conj_mul] at ha ⊢
    simp only [UpperHalfPlane.coe_im] at ha ⊢
    rw [abs_mul, abs_of_pos hc]
    have hd : (m * n' - n * m' : ℤ) ≠ 0 := by
      rintro h0
      rw [h0] at ha
      simp at ha
    have h1 : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hd
    nlinarith

theorem periodEta : PeriodEta := by
  intro ω₁ τ h
  have hω : 0 < ‖ω₁‖ := norm_pos_iff.2 h
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold period
  rw [discrEta ω₁ τ h, areaEq ω₁ τ h]
  have e : ‖(2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24‖ =
      ((2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [norm_mul, norm_pow, norm_pow, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hπ.le]
    norm_num
    ring
  have hx : 0 ≤ (2 * Real.pi / ‖ω₁‖) ^ 2 * ‖ModularForm.eta (τ : ℂ)‖ ^ 4 := by positivity
  rw [e, show ((1 : ℝ) / 6) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hx (by norm_num)]
  field_simp
  ring

theorem discrScale : DiscrScale := by
  intro ω₁ τ c h hc
  rw [scale_latt, discrEta _ τ (mul_ne_zero hc h), discrEta ω₁ τ h]
  rw [zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp

theorem hasSum_G (L : PeriodPair) {n : ℕ} (hn : 2 < n) :
    HasSum (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ n) (L.G n) := by
  have h := L.hasSum_sumInvPow 0 hn
  simp only [sub_zero, PeriodPair.sumInvPow_zero] at h
  have h1 : HasSum (((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n)) (L.G n) := by
    rw [← hasSum_subtype_iff_indicator]
    simp only [one_div]
    exact h
  have h2 : ((L.lattice : Set ℂ)).indicator (fun w : ℂ => 1 / w ^ n) =
      ({w : ℂ | w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0}).indicator (fun w : ℂ => 1 / w ^ n) := by
    ext w
    by_cases hw : w = 0
    · subst hw
      simp [Set.indicator, zero_pow (by omega : n ≠ 0)]
    · classical
      have e : (w ∈ (L.lattice : Set ℂ)) ↔ (w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0) :=
        ⟨fun h => ⟨h, hw⟩, fun h => h.1⟩
      simp only [Set.indicator]
      exact if_congr e rfl rfl
  rw [h2, ← hasSum_subtype_iff_indicator] at h1
  exact h1

theorem agreePeriodPair : AgreePeriodPair := by
  intro L
  have hk : ∀ k : ℕ, 2 ≤ k →
      (Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧
      eisG L.lattice.toAddSubgroup k = L.G (2 * k)) := by
    intro k hk
    have h := hasSum_G L (n := 2 * k) (by omega)
    exact ⟨h.summable, h.tsum_eq⟩
  refine ⟨hk, ?_, ?_⟩
  · rw [g2, PeriodPair.g₂, (hk 2 le_rfl).2]
  · rw [g3, PeriodPair.g₃, (hk 3 (by norm_num)).2]

theorem latticePeriodEta : LatticePeriodEta :=
  ⟨discrEta, areaEq, periodEta, discrScale, agreePeriodPair⟩

end GlobalTheory.LatticePeriodEtaProof
end
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧ (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ ord χ β = 1 ∧ c / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧ ∀ (χ : DirichletCharacter ℂ M) (ρ : ℂ), ρ.re < 1 → LFunction χ ρ = 0 → (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / Real.log (M * (|ρ.im| + 2)) := by
  first | exact @GlobalTheory.ExceptionalPair.main | exact GlobalTheory.ExceptionalPair.main | (intros; apply GlobalTheory.ExceptionalPair.main <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem exists_dvd_mul_add_of_prime (l q r : ℕ) (hl : l.Prime) (hq : ¬ l ∣ q) : ∃ c : ℕ, l ∣ q * c + r := by
  haveI := Fact.mk hl
  have hq' : (q : ZMod l) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q l).1 h)
  refine ⟨(-(r : ZMod l) * (q : ZMod l)⁻¹).val, (ZMod.natCast_eq_zero_iff _ l).1 ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring

theorem card_large_primes_class_le (q a Q M N : ℕ) (P : Finset ℕ) (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≡ a [MOD q] ∧ Q < p ∧ q * M ≤ p ∧ p < q * (M + N)) :
    (P.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  have hdec : ∀ p ∈ P, p = q * (p / q) + a % q := fun p hp => by
    have h : p % q = a % q := (hP p hp).2.1
    rw [← h, Nat.div_add_mod]
  have hinj : Set.InjOn (fun p => p / q + 1) (P : Set ℕ) := by
    intro p hp p' hp' h
    have h' : p / q = p' / q := by simpa using h
    rw [hdec p hp, hdec p' hp', h']
  have key := GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime M N Q q (P.image fun p => p / q + 1) hQ hq ?_ ?_
  · rwa [Finset.card_image_of_injOn hinj] at key
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨-, -, -, h1, h2⟩ := hP p hp
    have h3 : M ≤ p / q := (Nat.le_div_iff_mul_le hq).2 (by rwa [mul_comm])
    have h4 : p / q < M + N := (Nat.div_lt_iff_lt_mul hq).2 (by rwa [mul_comm])
    exact Finset.mem_Ioc.2 ⟨by omega, by omega⟩
  · intro l hl hlQ hlq
    obtain ⟨c, hc⟩ := exists_dvd_mul_add_of_prime l q (a % q) hl hlq
    refine ⟨c + 1, fun n hn h => ?_⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
    have h1 : p / q ≡ c [MOD l] := Nat.ModEq.add_right_cancel' 1 h
    have h2 : q * (p / q) + a % q ≡ q * c + a % q [MOD l] := (h1.mul_left q).add_right _
    rw [← hdec p hp] at h2
    have h3 : l ∣ p := (Nat.modEq_zero_iff_dvd).1 (h2.trans ((Nat.modEq_zero_iff_dvd).2 hc))
    have h4 := (Nat.prime_dvd_prime_iff_eq hl (hP p hp).1).1 h3
    have := (hP p hp).2.2.1
    omega

theorem brun_titchmarsh_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  refine ⟨48, by norm_num, fun q a x y hq _ hx hy => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = y / q := ⟨_, rfl⟩
  have hyz : y = q * z := by rw [hz]; field_simp
  have hz2 : 2 ≤ z := by rw [hz, le_div_iff₀ hq0]; exact hy
  rw [← hz]
  have hfl : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz2)
  have hflz : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzfl : z < ⌊z⌋₊ + 1 := Nat.lt_floor_add_one z
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt ⌊z⌋₊ := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hs2 : s * s ≤ ⌊z⌋₊ := hs ▸ Nat.sqrt_le _
  have hs3 : ⌊z⌋₊ < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt _
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = s + 1 := ⟨_, rfl⟩
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast (by omega : 2 ≤ Q)
  have hQz : (Q : ℝ) ^ 2 ≤ 4 * z := by
    have : Q ^ 2 ≤ 4 * ⌊z⌋₊ := by rw [hQ]; nlinarith
    have : (Q : ℝ) ^ 2 ≤ 4 * ⌊z⌋₊ := by exact_mod_cast this
    linarith
  have hzQ : z ≤ (Q : ℝ) ^ 2 := by
    have : ⌊z⌋₊ + 1 ≤ Q ^ 2 := by rw [hQ]; nlinarith
    have : (⌊z⌋₊ : ℝ) + 1 ≤ (Q : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : Real.log z ≤ 2 * Real.log Q := by
    have := Real.log_le_log (by linarith) hzQ
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hlQ : Real.log Q ≤ Q := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Q)
    linarith
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set P := (primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q]) with hP
  have hbig := card_large_primes_class_le q a Q (⌊x⌋₊ / q) (⌊z⌋₊ + 2) (P.filter fun p => Q < p) hq (by omega) (by
    intro p hp
    simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    refine ⟨h3, h4, h5, (Nat.mul_div_le _ _).trans h1.le, ?_⟩
    have h6 : (p : ℝ) ≤ x + y := (Nat.le_floor_iff (by nlinarith)).1 h2
    have h7 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h8 : ⌊x⌋₊ + 1 ≤ q * (⌊x⌋₊ / q + 1) := Nat.lt_mul_div_succ _ hq
    have h9 : (⌊x⌋₊ : ℝ) + 1 ≤ q * (((⌊x⌋₊ / q : ℕ) : ℝ) + 1) := by exact_mod_cast h8
    have h10 : (p : ℝ) < q * (((⌊x⌋₊ / q : ℕ) : ℝ) + (⌊z⌋₊ + 2)) := by nlinarith
    exact_mod_cast h10)
  have hsmall : (P.filter fun p => ¬ Q < p).card ≤ Q := by
    calc _ ≤ (Finset.Icc 1 Q).card := Finset.card_le_card fun p hp => by
            simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
            exact Finset.mem_Icc.2 ⟨hp.1.1.2.one_le, by omega⟩
      _ = Q := by simp
  have hsum := Finset.card_filter_add_card_filter_not (s := P) (fun p => Q < p)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((P.filter fun p => Q < p).card : ℝ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ Nat.cast_nonneg _
  have hcard : (P.card : ℝ) ≤ B + Q := by
    rw [hB]; exact_mod_cast (by omega)
  rw [← hB] at hbig
  push_cast at hbig
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have h1 : B * ((q.totient : ℝ) / q * Real.log Q) ≤ 20 * z := by nlinarith
  have h2 : B * (q.totient * Real.log Q) ≤ 20 * y := by
    have := mul_le_mul_of_nonneg_left h1 hq0.le
    rw [hyz]
    calc _ = q * (B * ((q.totient : ℝ) / q * Real.log Q)) := by field_simp
      _ ≤ _ := by linarith
  have h3 : B * (q.totient * Real.log z) ≤ 40 * y := by
    have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB0 hφ0.le)
    nlinarith
  have h4 : (Q : ℝ) * Real.log z ≤ 8 * z := by nlinarith
  have h5 : (Q : ℝ) * (q.totient * Real.log z) ≤ 8 * y := by
    have : (q.totient : ℝ) * (Q * Real.log z) ≤ q * (8 * z) :=
      mul_le_mul hφq h4 (by positivity) hq0.le
    rw [hyz]; nlinarith
  rw [le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ q.totient * Real.log z)
  nlinarith

end GlobalTheory.Lin
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

theorem hcVal_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ} (μ : Fin N → R) (k : ℕ) :
    hcVal S (fun i => φ (μ i)) k = φ (hcVal R μ k) := by
  have hM : hcMat S (fun i => φ (μ i)) = (hcMat R μ).map φ := by
    ext i l
    simp only [hcMat, shift, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hP : (hcMat S (fun i => φ (μ i))) ^ k = ((hcMat R μ) ^ k).map φ := by
    rw [hM]
    exact (map_pow (RingHom.mapMatrix φ) (hcMat R μ) k).symm

  simp only [hcVal, hP, Matrix.map_apply, map_sum]

theorem gel_dualWeyl_int (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (j : ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N ν) : gel ℤ N N j f = hcVal ℤ (fun i => (ν i : ℤ)) j • f := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℤ N N).2.2 ℚ (Int.castRingHom ℚ) j f,
    GlobalTheory.T.traceRowOperatorPower_dualWeyl_highestWeight N ν hν j _ (dualWeylMap ℤ ℚ (Int.castRingHom ℚ) N N ν f hf),
    smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  congr 2
  rw [← hcVal_map]
  simp

theorem gel_dualWeyl_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ j : ℕ,
    ∀ f ∈ dualWeyl k N N ν, gel k N N j f = hcVal k (fun i => (ν i : k)) j • f := by
  intro k _ N ν hν j f hf
  rw [standardMonomialSpanDomain k N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hg
    have hb : bideterminant k sz hsz I = map (Int.castRingHom k) (bideterminant ℤ sz hsz I) := by
      simp only [bideterminant, initMinor, map_prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [RingHom.map_det]
      congr 1
      ext p q
      simp
    have hmem : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ N N ν := hsh ▸ bidetMem ℤ N N K sz hsz I
    rw [hb, ← (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℤ N N).2.2 k (Int.castRingHom k) j, gel_dualWeyl_int N ν hν j _ hmem,
      smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
    congr 2
    rw [← hcVal_map]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory.Alc
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_summableMajorant_rationalVectors_locallyUniform : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω → ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧ ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  first | exact @GlobalTheory.SumMaj.summable_majorant | exact GlobalTheory.SumMaj.summable_majorant | (intros; apply GlobalTheory.SumMaj.summable_majorant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions

theorem _root_.GlobalTheory.T.scale_polynomial_quantities_comparison : ∀ eps c κ : ℝ, 0 < eps → 0 < κ → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → s.x ^ c ≤ Real.exp (s.x ^ (s.eps / 8)) ∧ s.x ^ c ≤ s.X' ^ κ ∧ s.x ^ c * s.X' ≤ s.b ^ κ ∧ s.b' * s.x ^ c ≤ s.b ∧ s.b ^ (1 - κ) * s.x ^ c ≤ s.b' ∧ (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ s.x ^ (3 : ℝ) → s.b ^ (1 - κ) * s.x ^ c ≤ s.w'' n ∧ s.w'' n ≤ s.b' ∧ s.X'' n = s.x * n * s.X') ∧ Real.exp (c * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ c ≤ s.X' ^ κ := by
  first | exact @GlobalTheory.scale_poly_comparison | exact GlobalTheory.scale_poly_comparison | (intros; apply GlobalTheory.scale_poly_comparison <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem natCast_residueField_completion_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem unipotent_type_character_finite_order : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (a t skip fc : ℕ) (zl : Bool) (_ : GLev S G a t 0 skip fc zl) (K : Type) [Field K] (s : K →+* ℂ), (∀ i, (gp i).Prime) → (∀ i, ∃ ζ : K, IsPrimitiveRoot ζ (gp i)) → ∃ N : ℕ, 0 < N ∧ ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G a t skip fc zl L K _ s hp hζ
  refine ⟨gp 0 * gp 1, Nat.mul_pos (hp 0).pos (hp 1).pos, fun x => ?_⟩
  rw [L.chi_eq x]
  let P : ℂ → Prop := fun z => z ^ (gp 0 * gp 1) = 1 ∧ ∃ r : K, s r = z
  have h1 : P 1 := ⟨one_pow _, 1, map_one s⟩
  have hm : ∀ y z, P y → P z → P (y * z) := by
    rintro y z ⟨hy, r, rfl⟩ ⟨hz, q, rfl⟩
    exact ⟨by rw [mul_pow, hy, hz, one_mul], r * q, map_mul s r q⟩
  change P _
  refine Finset.prod_induction _ P hm h1 fun i _ => ?_
  refine finprod_induction P h1 hm fun v => ?_
  refine finprod_induction P h1 hm fun h => ?_
  obtain ⟨⟨r, hr⟩, hpow⟩ := GlobalTheory.T.level_character_no_blocks_pth_root_of_unity (kv F v) K s (gp i) (hp i)
    (natCast_residueField_completion_eq_zero F v (gp i) h) (hζ i) n (G.psi0 i v h) (G.chiB i v h) a t skip
    (redM F v (G.mat i v h (L.fr i v h) (bc (prV (E := E) v) x.1)))
  refine ⟨?_, r⁻¹, by rw [map_inv₀, hr]⟩
  have hd : gp i ∣ gp 0 * gp 1 := by
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  obtain ⟨c, hc⟩ := hd
  rw [inv_pow, hc, pow_mul, hpow, one_pow, inv_one]

end GlobalTheory
end
