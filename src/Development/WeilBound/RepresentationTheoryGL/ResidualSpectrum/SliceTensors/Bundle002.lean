module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LsProps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Corner

variable {R S : Type} [CommRing R] [CommRing S]

theorem cc_cornerGL_leviEmb {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (s : R →ₙ+* S)
    (l : ∀ i, GL (Fin (n i)) R) :
    cornerGL N s (leviEmb R (stdBlocks n h) l) = leviEmb S (stdBlocks n h) (fun i => cornerGL (n i) s (l i)) := by
  have leviEmb_apply_same (T : Type) [CommRing T] (g : ∀ i, GL (Fin (n i)) T)
      (a : Fin c) (i j : Fin (n a)) :
      (leviEmb T (stdBlocks n h) g : Matrix (Fin N) (Fin N) T)
        (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨a, j⟩) = (g a : Matrix _ _ T) i j := by
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  have leviEmb_apply_ne (T : Type) [CommRing T] (g : ∀ i, GL (Fin (n i)) T)
      {a b : Fin c} (hab : a ≠ b) (i : Fin (n a)) (j : Fin (n b)) :
      (leviEmb T (stdBlocks n h) g : Matrix (Fin N) (Fin N) T)
        (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) = 0 := by
    classical
    simp [leviEmb]
    letI : DecidableEq (Fin c) := Classical.typeDecidableEq _
    exact Matrix.blockDiagonal'_apply_ne _ _ _ hab
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective q
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_same, GlobalTheory.IwasawaAdelic.cornerGL_entry_same, leviEmb_apply_same]
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he =>
        hij (by simpa using (stdBlocks n h).injective he)
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hij,
        leviEmb_apply_same]
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he =>
      hab (congrArg Sigma.fst ((stdBlocks n h).injective he))
    rw [leviEmb_apply_ne _ _ hab, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ hab, map_zero]

theorem cc_cornerGL_mem_unipRad {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (s : R →ₙ+* S) {u : GL (Fin N) R}
    (hu : u ∈ unipRad R (stdBlocks n h)) : cornerGL N s u ∈ unipRad S (stdBlocks n h) := by
  rw [mem_unipRad] at hu ⊢
  obtain ⟨hP, hD⟩ := hu
  refine ⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he => by
      have := congrArg Sigma.fst ((stdBlocks n h).injective he)
      exact (ne_of_gt hlt) this
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_same, hD a i i]; simp
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he => by
        exact hij (by simpa using (stdBlocks n h).injective he)
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij,
        map_zero]

end Corner

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem iwasawa_inf {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N) :
    ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GL (Fin (n i)) (Cinf E)) (k : Kinf E N),
      x = u * leviEmb (Ad E) (stdBlocks n h) (fun i => infGL E (n i) (m i)) *
        (infGL E N (Unitary.toUnits k) * finGL E N (Matrix.GeneralLinearGroup.map (pFin E) x)) := by
  obtain ⟨b, hb, k, hy⟩ :=
    GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)
  have hbP := GlobalTheory.IwasawaAdelic.mem_parab_of_upper n h b hb
  have hLmem (g : ∀ i, GL (Fin (n i)) (Cinf E)) :
      leviEmb (Cinf E) (stdBlocks n h) g ∈ parab (Cinf E) (stdBlocks n h) := by
    apply mem_parab_iff.2
    intro a b i j hab
    classical
    simp [leviEmb]
    letI : DecidableEq (Fin c) := Classical.typeDecidableEq _
    exact Matrix.blockDiagonal'_apply_ne _ _ _ (ne_of_gt hab)
  have hproj (g : ∀ i, GL (Fin (n i)) (Cinf E)) :
      leviProj (Cinf E) (stdBlocks n h) ⟨leviEmb (Cinf E) (stdBlocks n h) g, hLmem g⟩ = g := by
    funext a
    ext i j
    simp [leviProj_apply, leviEmb, Matrix.blockDiagonal'_apply_eq]
  have hdec : ∃ u ∈ unipRad (Cinf E) (stdBlocks n h),
      b = leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩) * u := by
    let L : parab (Cinf E) (stdBlocks n h) :=
      ⟨leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩),
        hLmem _⟩
    refine ⟨((L⁻¹ * ⟨b, hbP⟩ : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E)), ?_, ?_⟩
    · change ((L⁻¹ * ⟨b, hbP⟩ : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E)) ∈ _
      apply (coe_mem_unipRad (Cinf E) _).2
      change leviProj (Cinf E) (stdBlocks n h) (L⁻¹ * ⟨b, hbP⟩) = 1
      rw [map_mul, map_inv, hproj, inv_mul_cancel]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mul_inv_cancel_left _ _).symm
  obtain ⟨u, hu, hbu⟩ := hdec
  set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩) with hL
  have hN := parab_le_normalizer (Cinf E) (stdBlocks n h) (hLmem (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩))
  have hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h) := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
  refine ⟨infGL E N (L * u * L⁻¹), GlobalTheory.IwasawaAdelic.infGL_mem_unipRad E n h _ hu',
    fun i => leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩ i, k, ?_⟩
  rw [← GlobalTheory.IwasawaAdelic.infGL_leviEmb, ← hL]
  conv_lhs => rw [← infGL_mul_finGL x, hy]
  rw [hbu]
  simp only [map_mul, map_inv]
  group

theorem finGL_locGL_leviEmb {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (w : HeightOneSpectrum (𝓞 E))
    (μ : ∀ i, GL (Fin (n i)) (w.adicCompletion E)) :
    finGL E N (locGL E N w (leviEmb (w.adicCompletion E) (stdBlocks n h) μ)) =
      leviEmb (Ad E) (stdBlocks n h) (fun i => finGL E (n i) (locGL E (n i) w (μ i))) := by
  rw [locGL, cc_cornerGL_leviEmb, finGL, cc_cornerGL_leviEmb]
  rfl

theorem finGL_locGL_mem_unipRad {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (w : HeightOneSpectrum (𝓞 E))
    {u : GL (Fin N) (w.adicCompletion E)} (hu : u ∈ unipRad (w.adicCompletion E) (stdBlocks n h)) :
    finGL E N (locGL E N w u) ∈ unipRad (Ad E) (stdBlocks n h) := by
  exact cc_cornerGL_mem_unipRad n h _ (cc_cornerGL_mem_unipRad n h _ hu)

theorem commute_finGL_locGL {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {y : GA E N}
    (hy : Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y) = 1)
    (g : GL (Fin N) (w.adicCompletion E)) :
    y * finGL E N (locGL E N w g) = finGL E N (locGL E N w g) * y := by
  have hc := LocSph.comm_locGL w _ hy g
  conv_lhs => rw [← infGL_mul_finGL y]
  conv_rhs => rw [← infGL_mul_finGL y]
  rw [mul_assoc, ← (finGL E N).map_mul, hc, (finGL E N).map_mul, ← mul_assoc, infGL_comm, mul_assoc]

theorem exists_split_at {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) (y : GA E N) :
    ∃ (y₀ : GA E N) (g : GL (Fin N) (w.adicCompletion E)),
      Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y₀) = 1 ∧
        y = y₀ * finGL E N (locGL E N w g) := by
  set g := Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y)
  refine ⟨y * (finGL E N (locGL E N w g))⁻¹, g, ?_, by group⟩
  rw [map_mul, map_mul, map_inv, map_inv, pFin_finGL, pLoc_locGL, mul_inv_cancel]

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

namespace PositivityTheory.Rg.Rs.SmoothingSquareIntegrable

theorem sq_lintegral_le {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) {g : Y → ℝ≥0∞} (hg : AEMeasurable g ρ) :
    (∫⁻ y, g y ∂ρ) ^ 2 ≤ ρ Set.univ * ∫⁻ y, g y ^ 2 ∂ρ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞))
    aemeasurable_const hg
  simp only [ENNReal.one_rpow, lintegral_const] at h
  calc (∫⁻ y, g y ∂ρ) ^ 2 ≤ (ρ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ y, g y ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        simpa [Pi.mul_apply] using h
    _ = ρ Set.univ * ∫⁻ y, g y ^ 2 ∂ρ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem lintegral_sq_lt_top {μ : Measure (GA E N)} [μ.IsHaarMeasure] {φ : GA E N → ℂ}
    (h : MemL2Quotient (latticeGL E N) μ φ) : ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ < ⊤ := by
  have hm := ((memL2_iff_fundamental_domain (isFundamentalDomain_stdDom (latticeGL E N) μ)).1 h).2
  have := hm
  change eLpNorm _ _ _ < ⊤ at this
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hm.aestronglyMeasurable] at this
  simpa using this

theorem lintegral_mul_right {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ : GA E N → ℂ}
    (h : MemL2Quotient (latticeGL E N) μ φ) (g : GA E N) :
    ∫⁻ x in stdDom (latticeGL E N), ‖φ (x * g)‖ₑ ^ 2 ∂μ = ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ := by
  have hd := isFundamentalDomain_stdDom (latticeGL E N) μ
  have hm : AEMeasurable (fun q => ‖descend (latticeGL E N) φ q‖ₑ ^ 2) (quotMeasure (latticeGL E N) μ) :=
    h.2.aestronglyMeasurable.enorm.pow_const 2
  have e1 := lintegral_quotMeasure hd (fun q => ‖descend (latticeGL E N) φ q‖ₑ ^ 2)
  have e2 := lintegral_quotMeasure hd (fun q => ‖descend (latticeGL E N) φ (rmul (latticeGL E N) g q)‖ₑ ^ 2)
  simp only [rmul_mk, h.1.descend_mk] at e1 e2
  rw [← e1, ← e2]
  have hp := measurePreserving_rmul (Γ := latticeGL E N) (μ := μ) g
  conv_rhs => rw [← hp.map_eq]
  rw [lintegral_map' (by rwa [hp.map_eq]) (measurable_rmul g).aemeasurable]

theorem memL2_of_smoothing (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ν : Measure (Lie E N))
    [ν.IsAddHaarMeasure] {α : Lie E N → ℂ} (hα : GlobalTheory.CuspQuot.IsTest (invSet E N) α) {φ : GA E N → ℂ}
    (hc : Continuous φ) (h : MemL2Quotient (latticeGL E N) μ φ) :
    MemL2Quotient (latticeGL E N) μ (GlobalTheory.CuspQuot.smoothing ν α φ) := by
  have hd := isFundamentalDomain_stdDom (latticeGL E N) μ
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  have : ProperSpace (Lie E N) := FiniteDimensional.proper ℝ _
  have : SigmaFinite ν := Measure.IsAddHaarMeasure.sigmaFinite ν
  have hl : LeftInv (latticeGL E N) φ := h.1
  have hlS : LeftInv (latticeGL E N) (GlobalTheory.CuspQuot.smoothing ν α φ) := fun γ hγ g => by
    simp only [GlobalTheory.CuspQuot.smoothing, chart, mul_assoc, hl γ hγ]
  have hH : Continuous fun p : GA E N × Lie E N => α p.2 * chart φ p.1 p.2 :=
    GlobalTheory.CuspQuot.continuous_integrand hα hc
  have hmS : AEStronglyMeasurable (GlobalTheory.CuspQuot.smoothing ν α φ) (μ.restrict (stdDom (latticeGL E N))) :=
    (hH.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
  set K := tsupport α with hKdef
  have hKν : ν K < ⊤ := hα.2.1.isCompact.measure_lt_top
  have hpt : ∀ x, ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ^ 2 ≤ ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := by
    intro x
    have h1 : ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ≤ ∫⁻ y in K, ‖α y * chart φ x y‖ₑ ∂ν := by
      rw [setLIntegral_eq_of_support_subset]
      · exact enorm_integral_le_lintegral_enorm _
      · intro y hy
        by_contra hyK
        apply hy
        simp [image_eq_zero_of_notMem_tsupport hyK]
    have hx : Continuous fun y => α y * chart φ x y := hH.comp (continuous_const.prodMk continuous_id)
    have h2 := sq_lintegral_le (ν.restrict K) (g := fun y => ‖α y * chart φ x y‖ₑ) hx.enorm.aemeasurable
    rw [Measure.restrict_apply_univ] at h2
    calc _ ≤ (∫⁻ y in K, ‖α y * chart φ x y‖ₑ ∂ν) ^ 2 := by gcongr
      _ ≤ ν K * ∫⁻ y in K, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := h2
      _ ≤ ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := by gcongr; exact Measure.restrict_le_self
  set I := ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ with hIdef
  have hI : I < ⊤ := lintegral_sq_lt_top h
  have hin : ∀ y, ∫⁻ x in stdDom (latticeGL E N), ‖α y * chart φ x y‖ₑ ^ 2 ∂μ = ‖α y‖ₑ ^ 2 * I := by
    intro y
    by_cases hy : IsUnit (Matrix.of y)
    · simp_rw [chart, dite_eq_left hy, enorm_mul, mul_pow]
      rw [lintegral_const_mul' _ _ (by simp), lintegral_mul_right h]
    · have : α y = 0 := image_eq_zero_of_notMem_tsupport fun h' => hy (hα.2.2 h')
      simp [this]
  have hα2 : ∫⁻ y, ‖α y‖ₑ ^ 2 ∂ν < ⊤ := by
    have hmα := hα.1.continuous.memLp_of_hasCompactSupport (p := 2) (μ := ν) hα.2.1
    have := hmα
    change eLpNorm _ _ _ < ⊤ at this
    rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmα.aestronglyMeasurable] at this
    simpa using this
  have hmeas : AEMeasurable (Function.uncurry fun x y => ‖α y * chart φ x y‖ₑ ^ 2)
      ((μ.restrict (stdDom (latticeGL E N))).prod ν) :=
    ((ENNReal.continuous_pow 2).comp hH.enorm).measurable.aemeasurable
  refine (memL2_iff_fundamental_domain hd).2 ⟨hlS, ?_⟩
  change eLpNorm _ _ _ < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmS]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc ∫⁻ x in stdDom (latticeGL E N), ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in stdDom (latticeGL E N), ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν ∂μ := lintegral_mono hpt
    _ = ν K * ∫⁻ x in stdDom (latticeGL E N), ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν ∂μ :=
        lintegral_const_mul' _ _ hKν.ne
    _ = ν K * ∫⁻ y, ∫⁻ x in stdDom (latticeGL E N), ‖α y * chart φ x y‖ₑ ^ 2 ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ν K * ((∫⁻ y, ‖α y‖ₑ ^ 2 ∂ν) * I) := by
        simp_rw [hin]
        rw [lintegral_mul_const' _ _ hI.ne]
    _ < ⊤ := ENNReal.mul_lt_top hKν (ENNReal.mul_lt_top hα2 hI)

end PositivityTheory.Rg.Rs.SmoothingSquareIntegrable

end
end

section

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs

namespace SliceFrobeniusReciprocity

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {n : Fin c → ℕ} {h : ∑ i, n i = N} {σ' : SmIrr (GL (Fin N) k)} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (∀ i, GL (Fin (n i)) k) W} {ℓ : σ'.V →ₗ[ℂ] W}

def frobFun (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) :
    IndSp (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹) :=
  ⟨⟨fun g => ℓ (σ'.ρ g v), fun p g => by
      show ℓ (σ'.ρ ((p : GL (Fin N) k) * g) v) = _
      rw [map_mul, Module.End.mul_apply, hℓ p]
      simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, smul_smul, ← Units.val_mul,
        MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((σ'.smooth v).mem_nhds (by simp)) fun g hg => by
      have hg' : σ'.ρ g v = v := hg
      show _ = _
      apply Subtype.ext
      funext x
      show ℓ (σ'.ρ (x * g) v) = ℓ (σ'.ρ x v)
      rw [map_mul, Module.End.mul_apply, hg'])⟩

theorem frobFun_apply (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) (g : GL (Fin N) k) :
    (frobFun hℓ v).1.1 g = ℓ (σ'.ρ g v) := rfl

def frobMap (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) :
    σ'.ρ.IntertwiningMap (parInd (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹)) where
  toLinearMap :=
    { toFun := frobFun hℓ
      map_add' := fun v v' => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (v + v')) = ℓ (σ'.ρ g v) + ℓ (σ'.ρ g v')
        simp))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (a • v)) = a • ℓ (σ'.ρ g v)
        simp)) }
  isIntertwining' g := by
    ext v x
    show ℓ (σ'.ρ x (σ'.ρ g v)) = ℓ (σ'.ρ (x * g) v)
    rw [map_mul, Module.End.mul_apply]

end SliceFrobeniusReciprocity

open SliceFrobeniusReciprocity in
theorem frobRecip_holds : PositivityTheory.RSHS.LS.FrobRecip := by
  intro k _ _ _ _ N c n h σ' W _ _ ρ ℓ hℓ0 hℓ
  refine ⟨frobMap hℓ, fun h0 => hℓ0 (LinearMap.ext fun v => ?_)⟩
  have h1 := congrArg (fun f : _ →ₗ[ℂ] _ => (f v).1.1 1) h0
  simpa [frobMap, frobFun_apply] using h1

end PositivityTheory.Rg.Rs

end
end
