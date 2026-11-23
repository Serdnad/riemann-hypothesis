module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle072
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle177
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle176
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle166
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatFG

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dpE_eq (i : ℕ) : Lat.dpE f ξ l M i =
    (((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ i := by
  simp only [Lat.dpE, Lat.η, smul_pow, mul_smul]

theorem dpE_mem {k i : ℕ} (h : k ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ k} := by
  rw [dpE_eq, Ideal.mem_span_singleton']
  refine ⟨(((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ (i - k), ?_⟩
  rw [smul_mul_assoc, ← pow_add, Nat.sub_add_cancel h]

variable {f ξ} in
theorem dpE_eq_zero {m : ℕ} (hn : f ξ ^ m = 0) {i : ℕ} (h : m ≤ i) : Lat.dpE f ξ l M i = 0 := by
  rw [dpE_eq, pow_eq_zero_of_le h hn, smul_zero]

theorem mul_dpE {l : ℕ} (hl : l ≠ 0) (j : ℕ) :
    f ξ * Lat.dpE f ξ l M j = ((l ^ M * (j + 1) : ℕ) : B) * Lat.dpE f ξ l M (j + 1) := by
  have hl' : ((l : ℚ) ^ M) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl)
  have h : f ξ = ((l : ℚ) ^ M) • Lat.η f ξ l M := by
    simp only [Lat.η, smul_smul, mul_inv_cancel₀ hl', one_smul]
  have hnat : ((l ^ M * (j + 1) : ℕ) : B) = ((l : ℚ) ^ M * ((j : ℚ) + 1)) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, ← map_natCast (algebraMap ℚ B)]; push_cast; rfl
  simp only [Lat.dpE]
  generalize Lat.η f ξ l M = e at h
  rw [h, hnat]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, pow_succ']
  congr 1
  rw [Nat.factorial_succ]
  have h1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((j.factorial : ℚ)) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  push_cast
  field_simp

variable {f ξ l M} in
theorem sum_single {m : ℕ} (hn : f ξ ^ m = 0) (k : ℕ) (a : W) :
    ∑ i ∈ Finset.range m, f ((Pi.single k a : ℕ → W) i) * Lat.dpE f ξ l M i = f a * Lat.dpE f ξ l M k := by
  by_cases hk : k < m
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_range.2 hk) h
  · rw [dpE_eq_zero l M hn (not_lt.1 hk), mul_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i ≠ k := by
      have := Finset.mem_range.1 hi
      omega
    simp [Pi.single_eq_of_ne this]

variable {f ξ l} in
theorem l_ne {m : ℕ} (h : Lat.Hyp f ξ l m) : l ≠ 0 := by
  rintro rfl
  exact h.l0 (by simp)


variable {f ξ l} in
theorem dvd_of_mem {m : ℕ} (h : Lat.Hyp f ξ l m) {j : ℕ} (hj : j < m) {a : W}
    (hmem : f a * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)}) : ξ ∣ a := by
  have hl' : ((l : ℚ) ^ M)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (l_ne h)))
  have h2 : ((j.factorial : ℚ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast j.factorial_ne_zero)
  have hu : (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) ≠ 0 := mul_ne_zero h2 (pow_ne_zero _ hl')
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [dpE_eq] at hb
  generalize (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) = u at hb hu
  refine h.gr j hj a (u⁻¹ • b) ?_
  rw [mul_smul_comm, mul_comm (f ξ ^ (j + 1)), hb, mul_smul_comm, smul_smul, inv_mul_cancel₀ hu, one_smul]


variable {f ξ l} in
theorem exists_coeff {m : ℕ} (h : Lat.Hyp f ξ l m) {x : B} (hx : x ∈ Lat.sub f ξ l M) {r : ℕ}
    (hr : x ∈ Ideal.span {f ξ ^ r}) (j : ℕ) (hj : j ≤ r) :
    ∃ c : ℕ → W, (∀ i < j, c i = 0) ∧ x = ∑ i ∈ Finset.range m, f (c i) * Lat.dpE f ξ l M i := by
  induction j with
  | zero =>
    obtain ⟨n, c, hc⟩ := (GlobalTheory.T.mem_lattice_sub_iff_sum f ξ l M x).1 hx
    refine ⟨fun i => if hi : i < n then c ⟨i, hi⟩ else 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    set g : ℕ → B := fun i => f (if hi : i < n then c ⟨i, hi⟩ else 0) * Lat.dpE f ξ l M i with hg
    have h1 : x = ∑ i ∈ Finset.range n, g i := by
      rw [hc, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hg]
    have h2 : ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range (max n m), g i :=
      Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun i _ hi => by
        have : ¬ i < n := by simpa using hi
        simp [hg, this]
    have h3 : ∑ i ∈ Finset.range m, g i = ∑ i ∈ Finset.range (max n m), g i :=
      Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun i _ hi => by
        have : m ≤ i := by simpa using hi
        simp [hg, dpE_eq_zero l M h.nil this]
    rw [h1, h2, ← h3]
  | succ j ih =>
    obtain ⟨c, hc, hxc⟩ := ih (by omega)
    set c' : ℕ → W := c - Pi.single j (c j) with hc'
    have hsum : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i =
        x - f (c j) * Lat.dpE f ξ l M j := by
      rw [← sum_single h.nil j (c j), hxc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc', Pi.sub_apply, map_sub, sub_mul]
    have hz : ∀ i ≤ j, c' i = 0 := by
      intro i hi
      rcases hi.lt_or_eq with hi | rfl
      · rw [hc', Pi.sub_apply, hc i hi, Pi.single_eq_of_ne hi.ne, sub_zero]
      · rw [hc', Pi.sub_apply, Pi.single_eq_same, sub_self]
    have hrest : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)} := by
      refine Ideal.sum_mem _ fun i _ => ?_
      by_cases hi : i ≤ j
      · rw [hz i hi, map_zero, zero_mul]
        exact Ideal.zero_mem _
      · exact Ideal.mul_mem_left _ _ (dpE_mem f ξ l M (by omega))
    have hx1 : x ∈ Ideal.span {f ξ ^ (j + 1)} :=
      (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hj)) hr
    have hterm : f (c j) * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)} := by
      have := Ideal.sub_mem _ hx1 hrest
      rwa [hsum, sub_sub_cancel] at this
    obtain ⟨e, he⟩ : ∃ e : W, f (c j) * Lat.dpE f ξ l M j = f e * Lat.dpE f ξ l M (j + 1) := by
      by_cases hjm : j < m
      · obtain ⟨d, hd⟩ := dvd_of_mem M h hjm hterm
        refine ⟨d * ((l ^ M * (j + 1) : ℕ) : W), ?_⟩
        rw [hd, map_mul, map_mul, map_natCast, mul_comm (f ξ), mul_assoc, mul_dpE f ξ M (l_ne h), mul_assoc]
      · refine ⟨0, ?_⟩
        rw [dpE_eq_zero l M h.nil (not_lt.1 hjm), map_zero, zero_mul, mul_zero]
    refine ⟨c' + Pi.single (j + 1) e, fun i hi => ?_, ?_⟩
    · rw [Pi.add_apply, hz i (by omega), Pi.single_eq_of_ne (by omega), add_zero]
    · simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      rw [hsum, sum_single h.nil, ← he, sub_add_cancel]

end

theorem dividedPowerFiltration_fg : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ,
      (pdP (Lat.γ f ξ l M hc) r).FG := by
  intro W B _ _ _ f ξ l M m h hc r
  have key : pdP (Lat.γ f ξ l M hc) r =
      Ideal.span (Lat.dpA f ξ l M '' (↑(Finset.Ico r m) : Set ℕ)) := by
    rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc r]
    apply le_antisymm
    · intro x hx
      have hxs : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := x.2
      obtain ⟨c, hc0, hxc⟩ := exists_coeff M h hxs (Ideal.mem_comap.1 hx) r le_rfl
      have hx' : x = ∑ i ∈ Finset.range m, Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i := by
        apply Lat.ι_injective f ξ l M

        rw [hxc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, Lat.ι_ofW, Lat.ι_dpA]
      rw [hx']
      refine Ideal.sum_mem _ fun i hi => ?_
      by_cases hir : i < r
      · rw [hc0 i hir, map_zero, zero_mul]
        exact Ideal.zero_mem _
      · refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, ?_, rfl⟩)
        simp only [Finset.coe_Ico, Set.mem_Ico]
        exact ⟨not_lt.1 hir, Finset.mem_range.1 hi⟩
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi
      exact Ideal.mem_comap.2 (dpE_mem f ξ l M hi.1)
  rw [key]
  exact Submodule.fg_span ((Finset.finite_toSet _).image _)

end GlobalTheory.CompanionTheory.LatFG
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.MassTest

theorem exists_bump {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W] [MeasurableSpace W]
    [BorelSpace W] (ν : Measure W) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {U : Set W}
    (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ φ : W → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧ tsupport φ ⊆ U ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ 0 ∧ ∫⁻ X, ENNReal.ofReal (φ X) ∂ν ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨f, hf1, hf0, hfc, hfr⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x))
    (isOpen_interior (s := K)).isClosed_compl (by simpa using hxK)
  have hsupp : Function.support f ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hf0 (fun h => hyK (interior_subset h)))
  have hg : Continuous fun X => ENNReal.ofReal (f X) := ENNReal.continuous_ofReal.comp f.continuous
  refine ⟨f, f.continuous, hfc, fun X => (hfr X).1, ?_, ?_, ?_⟩
  · exact (closure_minimal hsupp hK.isClosed).trans hKU
  · intro h0
    have hpos : 0 < ν {X | ENNReal.ofReal (f X) ≠ 0} := by
      refine IsOpen.measure_pos ν (isOpen_ne_fun hg continuous_const) ⟨x, ?_⟩
      have : f x = 1 := hf1 (Set.mem_singleton x)
      simp [this]
    exact hpos.ne' (ae_iff.1 ((lintegral_eq_zero_iff hg.measurable).1 h0))
  · exact (f.continuous.integrable_of_hasCompactSupport hfc).lintegral_lt_top.ne

theorem exists_compactOpen {W : Type} [TopologicalSpace W] [T2Space W] [LocallyCompactSpace W]
    [TotallyDisconnectedSpace W] [MeasurableSpace W] (ν : Measure W) [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {U : Set W} (hU : IsOpen U) {x : W} (hx : x ∈ U) :
    ∃ A : Set W, IsCompact A ∧ IsOpen A ∧ A ⊆ U ∧ ν A ≠ 0 ∧ ν A ≠ ⊤ := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (X := W)).exists_subset_of_mem_open hxK
    isOpen_interior
  have hCc : IsCompact C := hK.of_isClosed_subset hC.1 (hCK.trans interior_subset)
  exact ⟨C, hCc, hC.2, (hCK.trans interior_subset).trans hKU, (hC.2.measure_pos ν ⟨x, hxC⟩).ne',
    hCc.measure_lt_top.ne⟩

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem gramR_ratTup_apply (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) (a c : Fin n) :
    gramR R σ J (ratTup R Y) a c = inclR R (gramE σ J Y a c) := by

  simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, map_sum, map_mul]

theorem exists_unit_vector (R : Type) [CommRing R] [Algebra F R] {J : Matrix (Fin 2) (Fin 2) E}
    (hA : Aniso σ J) : ∃ X : Fin 1 → Fin 2 → R ⊗[F] E, IsUnit (gramR R σ J X).det := by
  have hx : hE σ J (fun _ => 1) (fun _ => 1) ≠ 0 := fun h => one_ne_zero (congrFun (hA _ h) 0)
  refine ⟨ratTup R fun _ _ => 1, ?_⟩
  rw [Matrix.det_fin_one, gramR_ratTup_apply]
  exact (IsUnit.mk0 _ hx).map (inclR R)

end Alg

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isOpen_unit (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hloc : IsLocR R) (J : Matrix (Fin 2) (Fin 2) E) :
    IsOpen {X : Fin 1 → Fin 2 → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hu, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨-, -, -, -, -, -, -, -, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have hO : IsOpen {r : R | IsUnit r} := hu.isOpen_range
  exact (PI.VolStabS.isOpen_isUnit_det R hO 1).preimage (t10 1 2 J)

theorem exists_test_fun (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hl : lam.IsAddHaarMeasure) :
    ∃ φ : (Fin 1 → Fin 2 → R ⊗[F] E) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧
      tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det} ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ 0 ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 2) ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_bump _ (isOpen_unit hcm R hloc J) hX

theorem exists_test_set (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    [TotallyDisconnectedSpace R] (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hl : lam.IsAddHaarMeasure) :
    ∃ A : Set (Fin 1 → Fin 2 → R ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR R σ J X).det} ∧ coordW R b lam 1 2 A ≠ 0 ∧ coordW R b lam 1 2 A ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  haveI : TotallyDisconnectedSpace (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.totallyDisconnectedSpace
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_compactOpen _ (isOpen_unit hcm R hloc J) hX

end Loc

theorem testEx : TestEx := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam _ _ _ _ S
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨φ, h1, h2, h3, h4, h5, h6⟩ := exists_test_fun hcm hA (Ainf F) hLi b li hli.1
  have hA' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} ∧ coordW (Fv F v) b (lam v) 1 2 A ≠ 0 ∧
      coordW (Fv F v) b (lam v) 1 2 A ≠ ⊤ := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact exists_test_set hcm hA (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1
  choose A0 hc ho hs hn ht using hA'
  classical
  have hv : vol b li lam S φ (fun v => if v ∈ S then A0 v else latV b v) =
      (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 2 (A0 v) := by
    unfold vol
    congr 1
    exact Finset.prod_congr rfl fun v hvS => by simp [hvS]
  refine ⟨φ, fun v => if v ∈ S then A0 v else latV b v, ⟨h1, h2, h3, h4, ?_, ?_⟩, ?_, ?_⟩
  · intro v hvS
    simp only [hvS, if_true]
    exact ⟨hc v, ho v, hs v⟩
  · intro v hvS
    simp [hvS]
  · rw [hv]
    exact mul_ne_zero h5 (Finset.prod_ne_zero_iff.2 fun v _ => hn v)
  · rw [hv]
    exact ENNReal.mul_ne_top h6 (ENNReal.prod_ne_top fun v _ => ht v)

end GlobalTheory.CompanionTheory.SW.MassTest
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_order_quadratic_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ (ι : v.adicCompletionIntegers F →+* O) (δ : O) (D : v.adicCompletionIntegers F), (δ * δ = ι D) ∧ (∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ) ∧ (∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) ∧ IsUnit D ∧ IsUnit (2 : v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadRing.quad_ring | exact GlobalTheory.CompanionTheory.SW.QuadRing.quad_ring | (intros; apply GlobalTheory.CompanionTheory.SW.QuadRing.quad_ring <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem _root_.GlobalTheory.T.chart_lattice_le_span_norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ), chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem exists_fin_span_eq_of_unit_coeff {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (t : Fin (n + 1) → R)
    (ht : Ideal.span (Set.range t) = I) (x : Fin (n + 1) → R)
    (hx : ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I) (l : Fin (n + 1))
    (hu : IsUnit (x l)) : ∃ s : Fin n → R, Ideal.span (Set.range s) = I := by
  refine ⟨fun j => t (l.succAbove j), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← ht]
    exact Ideal.subset_span ⟨_, rfl⟩
  set N : Ideal R := Ideal.span (Set.range fun j => t (l.succAbove j)) with hN
  have hmem : ∀ j, t (l.succAbove j) ∈ N := fun j => Ideal.subset_span ⟨j, rfl⟩
  have htl : t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I := by
    obtain ⟨u, hu⟩ := hu
    have hsum : x l * t l = ∑ i, x i * t i - ∑ j, x (l.succAbove j) * t (l.succAbove j) := by
      rw [Fin.sum_univ_succAbove _ l]
      ring
    have h1 : x l * t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I := by
      rw [hsum]
      refine Ideal.sub_mem _ (Ideal.mem_sup_right (by simpa [smul_eq_mul] using hx)) ?_
      exact Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmem j))
    have h2 : t l = (↑u⁻¹ : R) * (x l * t l) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
  have hle : I ≤ N ⊔ IsLocalRing.maximalIdeal R • I := by
    conv_lhs => rw [← ht]
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove l i with h | ⟨j, h⟩
    · rw [h]; exact htl
    · rw [h]; exact Ideal.mem_sup_left (hmem j)
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle

theorem exists_minimal_generators : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R),
    ∃ (r : ℕ) (t : Fin r → R), Ideal.span (Set.range t) = I ∧
      ∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R := by
  intro R _ _ _ I
  classical
  have hex : ∃ r : ℕ, ∃ t : Fin r → R, Ideal.span (Set.range t) = I :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  obtain ⟨t, ht⟩ := Nat.find_spec hex
  refine ⟨_, t, ht, fun x hx l => ?_⟩
  by_contra hl
  have hu : IsUnit (x l) := by
    by_contra h
    exact hl ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have hmin : ∀ m : ℕ, (∃ s : Fin m → R, Ideal.span (Set.range s) = I) → Nat.find hex ≤ m :=
    fun m h => Nat.find_min' hex h
  generalize Nat.find hex = r at t ht x hx l hu hmin
  cases r with
  | zero => exact l.elim0
  | succ n =>
    have := hmin n (exists_fin_span_eq_of_unit_coeff I t ht x hx l hu)
    omega

end GlobalTheory.CompanionTheory.FewEq
end
