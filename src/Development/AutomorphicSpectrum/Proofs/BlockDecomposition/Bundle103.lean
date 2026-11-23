module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle085
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle086
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle087
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Topology.Instances.RealVectorSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace

@[expose] public section

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.contour_shift_gaussian_decay : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] (f : ℂ → Y) (a b M : ℝ), a ≤ b → DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b} → (∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) → ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line | exact GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line <;> assumption)
end

section

open scoped Matrix SchwartzMap ComplexConjugate

namespace GlobalTheory.CompanionTheory.QuadChirp

theorem ofReal_re_trace {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (((Matrix.trace (b * (Aᴴ * A))).re : ℝ) : ℂ) = Matrix.trace (b * (Aᴴ * A)) := by
  have h : (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = Matrix.trace (b * (Aᴴ * A)) := by
    rw [show (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = star (Matrix.trace (b * (Aᴴ * A))) from rfl,
      ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hb, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

theorem coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u l i) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth

theorem conj_coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u l i)) :=
  ((Complex.conjCLE.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth

theorem trace_hasTemperateGrowth {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) := by
  have heq : (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) =
      fun u => ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m, b i j * (star (u l j) * u l i) := by
    funext u
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Finset.mul_sum]
  rw [heq]
  refine Function.HasTemperateGrowth.sum fun i _ => Function.HasTemperateGrowth.sum fun j _ =>
    Function.HasTemperateGrowth.sum fun l _ => ?_
  exact (Function.HasTemperateGrowth.const (b i j)).mul
    ((GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth l j).mul (GlobalTheory.CompanionTheory.QuadChirp.coord_hasTemperateGrowth l i))

theorem chirp_hasTemperateGrowth {m n : ℕ} (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
        Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) := by
  have hre : Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      k * (Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))).re) :=
    (Function.HasTemperateGrowth.const k).mul
      (Complex.reCLM.hasTemperateGrowth.comp (GlobalTheory.CompanionTheory.QuadChirp.trace_hasTemperateGrowth b))
  have hcomp := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hre
  convert hcomp using 1
  funext u
  rw [Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]
  congr 1
  have hT := GlobalTheory.CompanionTheory.QuadChirp.ofReal_re_trace b hb (Matrix.of u)
  rw [Complex.ofReal_mul]
  conv_lhs => rw [← hT]
  ring

theorem exists_schwartz_chirp_mul :
    ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
        ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
          Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  intro m n k b hb φ
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi *
    Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) φ, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.QuadChirp.chirp_hasTemperateGrowth k b hb), smul_eq_mul]

end GlobalTheory.CompanionTheory.QuadChirp
end

section

open ValuativeRel MeasureTheory Matrix

theorem _root_.GlobalTheory.T.character_annihilator_integer_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (b : k), b ≠ 0 → IsCompact {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} ∧ IsOpen {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator | exact GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator | (intros; apply GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator <;> assumption)
end

section

open ValuativeRel MeasureTheory Matrix

theorem _root_.GlobalTheory.T.exists_scaled_nontrivial_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k), valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧ ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | exact GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | (intros; apply GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.isOpen_character_annihilator : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact | exact GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Arch

theorem continuous_biadditive_bounded :
    ∀ (N₁ N₂ N₃ : ℕ) (β : (Fin N₁ → ℝ) → (Fin N₂ → ℝ) → (Fin N₃ → ℝ)),
      (∀ u u' v, β (u + u') v = β u v + β u' v) →
      (∀ u v v', β u (v + v') = β u v + β u v') →
      Continuous (fun p : (Fin N₁ → ℝ) × (Fin N₂ → ℝ) => β p.1 p.2) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, ‖β u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  intro N₁ N₂ N₃ β h₁ h₂ hβ
  have smul₁ : ∀ (c : ℝ) u v, β (c • u) v = c • β u v := by
    intro c u v
    exact map_real_smul (AddMonoidHom.mk' (fun u => β u v) fun u u' => h₁ u u' v)
      (hβ.comp (continuous_id.prodMk continuous_const)) c u
  have smul₂ : ∀ (c : ℝ) u v, β u (c • v) = c • β u v := by
    intro c u v
    exact map_real_smul (AddMonoidHom.mk' (fun v => β u v) fun v v' => h₂ u v v')
      (hβ.comp (continuous_const.prodMk continuous_id)) c v
  have zero₁ : ∀ v, β 0 v = 0 := fun v => by simpa using smul₁ 0 0 v
  have zero₂ : ∀ u, β u 0 = 0 := fun u => by simpa using smul₂ 0 u 0
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuous_iff.mp hβ 0 1 one_pos
  have key : ∀ u v, ‖u‖ < δ → ‖v‖ < δ → ‖β u v‖ < 1 := by
    intro u v hu hv
    have h := hsmall (u, v) (by rw [dist_zero_right, Prod.norm_def]; exact max_lt hu hv)
    simpa [zero₁, dist_zero_right] using h
  obtain ⟨s, rfl⟩ : ∃ s, δ = 2 * s := ⟨δ / 2, by ring⟩
  have hs0 : 0 < s := by linarith
  have hsδ : s < 2 * s := by linarith
  refine ⟨4 / (2 * s) ^ 2, by positivity, fun u v => ?_⟩
  by_cases hu : u = 0
  · simp [hu, zero₁]
  by_cases hv : v = 0
  · simp [hv, zero₂]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnu : ‖(s / ‖u‖) • u‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (div_pos hs0 hu').le]
    field_simp
  have hnv : ‖(s / ‖v‖) • v‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg (div_pos hs0 hv').le]
    field_simp
  have hb := key ((s / ‖u‖) • u) ((s / ‖v‖) • v) (by rw [hnu]; exact hsδ) (by rw [hnv]; exact hsδ)
  rw [smul₁, smul₂, smul_smul, norm_smul,
    Real.norm_of_nonneg (mul_pos (div_pos hs0 hu') (div_pos hs0 hv')).le] at hb
  have e : s / ‖u‖ * (s / ‖v‖) * ‖β u v‖ = (‖β u v‖ * (s * s)) / (‖u‖ * ‖v‖) := by ring
  rw [e, div_lt_one (mul_pos hu' hv')] at hb
  rw [show 4 / (2 * s) ^ 2 * ‖u‖ * ‖v‖ = (‖u‖ * ‖v‖) / (s * s) by ring,
    le_div_iff₀ (mul_pos hs0 hs0)]
  exact hb.le

end GlobalTheory.CompanionTheory.Arch
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink

theorem exists_ne_zero_mem_absNorm_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ →
      ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  intro E _ _
  refine ⟨(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      ((Module.finrank ℚ E).factorial : ℝ) / (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E *
      Real.sqrt |(discr E : ℝ)|, ?_, ?_⟩
  · have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
    have h1 : (0 : ℝ) < (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E :=
      pow_pos (div_pos (by norm_num) Real.pi_pos) _
    have h2 : (0 : ℝ) < ((Module.finrank ℚ E).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h3 : (0 : ℝ) < (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E :=
      pow_pos (Nat.cast_pos.mpr hn) _
    exact mul_pos (div_pos (mul_pos h1 h2) h3) (Real.sqrt_pos.mpr hd)
  · intro 𝔞 h𝔞
    have hmem : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    obtain ⟨a, ha, ha0, hle⟩ :=
      exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr E (Units.mk0 _ hmem)
    rw [Units.val_mk0] at ha
    obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    refine ⟨t, ht, ?_, ?_⟩
    · rintro rfl
      simp at ha0
    · have key : ((Ideal.absNorm (Ideal.span {t}) : ℚ)) =
          |Algebra.norm ℚ (algebraMap (𝓞 E) E t)| := by
        rw [← FractionalIdeal.coeIdeal_absNorm (K := E), FractionalIdeal.coeIdeal_span_singleton,
          FractionalIdeal.absNorm_span_singleton]
      have key' : (Ideal.absNorm (Ideal.span {t}) : ℝ) =
          ((|Algebra.norm ℚ (algebraMap (𝓞 E) E t)| : ℚ) : ℝ) := by
        rw [← key, Rat.cast_natCast]
      rw [key']
      refine hle.trans (le_of_eq ?_)
      simp only [Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.lintegral_linear_change_variables_complex : ∀ (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ), Matrix.det D ≠ 0 →
    ∀ g : (Fin n → ℂ) → ENNReal, Measurable g →
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec <;> assumption)
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.lintegral_complex_power_finite : ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.torus_jacobian_det : ∀ {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  first | exact @GlobalTheory.CompanionTheory.Cone.dlog_ratio_det | exact GlobalTheory.CompanionTheory.Cone.dlog_ratio_det | (intros; apply GlobalTheory.CompanionTheory.Cone.dlog_ratio_det <;> assumption)
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.RowTrans

theorem exists_linearEquiv_apply_eq_of_ne_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ e : V ≃ₗ[K] V, e x = y := by
  have hx1 : (LinearEquiv.toSpanNonzeroSingleton K V x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton K V x hx).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton K V y hy))
  refine ⟨g, ?_⟩
  have h := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [LinearEquiv.trans_apply, hx1, LinearEquiv.toSpanNonzeroSingleton_one] at h
  exact h.symm

theorem gl_transitive_rows : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by
  intro K _ _ _ j r r' hr hr'
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.TyFin.RowTrans.exists_linearEquiv_apply_eq_of_ne_zero (K := K) hr hr'
  have h1 : (e.symm : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  have h2 : (e : (Fin j → K) →ₗ[K] Fin j → K) ∘ₗ (e.symm : (Fin j → K) →ₗ[K] Fin j → K) =
      LinearMap.id := LinearMap.ext fun v => by simp
  refine ⟨⟨(LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose,
    (LinearMap.toMatrix' (e.symm : (Fin j → K) →ₗ[K] Fin j → K)).transpose, ?_, ?_⟩, ?_⟩
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id,
      Matrix.transpose_one]
  · change Matrix.vecMul r (LinearMap.toMatrix' (e : (Fin j → K) →ₗ[K] Fin j → K)).transpose = r'
    rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    exact he

end GlobalTheory.CompanionTheory.TyFin.RowTrans
end

section

open MeasureTheory
open scoped NNReal ENNReal

theorem _root_.GlobalTheory.T.haar_measure_iwasawa_modular_character : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law | exact GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law | (intros; apply GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law <;> assumption)
end
