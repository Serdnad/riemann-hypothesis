module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle027
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle012
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle011
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityUnique
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ProperActionOrbitMeasure
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
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.KUnits

theorem continuousOn_ringInverse {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (h : IsOpenEmbedding (Units.val : Rˣ → R)) :
    ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  refine (h.continuousAt_iff).1 ?_
  have : (Ring.inverse ∘ (Units.val : Rˣ → R)) = fun u : Rˣ => ((u⁻¹ : Rˣ) : R) := by
    funext v
    simp
  rw [this]
  exact (Units.continuous_val.comp continuous_inv).continuousAt

theorem units_val_isOpenEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R →
    IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR
  obtain ⟨hTR, hLC, hSC, hT2, hArt, hRd, hUo, -⟩ := hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hArt
  haveI := hRd
  obtain ⟨-, -, -, hinv, -, hfix, hunit⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hσ R
  obtain ⟨hTK, -, -, -, hsc, htr, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hTK
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have hfin : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfin
  let N : R ⊗[F] E → R := fun y =>
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (y * sigR R σ y)
  have hNc : Continuous N :=
    continuous_const.mul (htr.comp (continuous_id.mul hsc))
  have hhalf : algebraMap F R (1 / 2) * (2 : R) = 1 := by
    have : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul]
      norm_num
    rwa [map_ofNat] at this
  have hnorm : ∀ y : R ⊗[F] E, y * sigR R σ y = N y ⊗ₜ[F] (1 : E) := by
    intro y
    obtain ⟨r, hr⟩ := hfix (y * sigR R σ y) (by rw [map_mul, hinv, mul_comm])
    have htrace : Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = 2 * r := by
      have h1 : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [h1, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) r]
      simp [two_mul, two_nsmul]
    have hNr : N y = r := by
      show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (y * sigR R σ y) = r
      rw [hr, htrace, ← mul_assoc, hhalf, one_mul]
    rw [hNr, hr]
  have hiff : ∀ y : R ⊗[F] E, IsUnit y ↔ IsUnit (N y) := by
    intro y
    constructor
    · intro hy
      have h1 : IsUnit (y * sigR R σ y) := hy.mul (hy.map (sigR R σ))
      rw [hnorm y] at h1
      exact (hunit _).1 h1
    · intro hy
      have h1 : IsUnit (y * sigR R σ y) := by
        rw [hnorm y]
        exact (hunit _).2 hy
      exact isUnit_of_mul_isUnit_left h1
  have hone : Continuous fun r : R => (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) := by
    have h1 : (fun r : R => (r ⊗ₜ[F] (1 : E) : R ⊗[F] E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [h1]
    exact Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id continuous_const
  let f : R ⊗[F] E → R ⊗[F] E := fun y => sigR R σ y * (Ring.inverse (N y) ⊗ₜ[F] (1 : E))
  have hfc : ContinuousOn f {y | IsUnit y} := by
    have h1 : ContinuousOn (fun y => Ring.inverse (N y)) {y : R ⊗[F] E | IsUnit y} :=
      (continuousOn_ringInverse hUo).comp hNc.continuousOn (fun y hy => (hiff y).1 hy)
    exact hsc.continuousOn.mul (hone.comp_continuousOn h1)
  have hfu : ∀ u : (R ⊗[F] E)ˣ, f u.1 = ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) := by
    intro u
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    have hu : IsUnit (N u.1) := (hiff _).1 u.isUnit
    show u.1 * (sigR R σ u.1 * (Ring.inverse (N u.1) ⊗ₜ[F] (1 : E))) = 1
    rw [← mul_assoc, hnorm, Algebra.TensorProduct.tmul_mul_tmul, Ring.mul_inverse_cancel _ hu,
      mul_one]
    rfl
  refine ⟨Units.isEmbedding_val_mk' hfc hfu, ?_⟩
  have hrange : Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) =
      N ⁻¹' Set.range (Units.val : Rˣ → R) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact (hiff _).1 u.isUnit
    · intro hy
      exact (hiff y).2 hy
  rw [hrange]
  exact hUo.isOpen_range.preimage hNc

end GlobalTheory.CompanionTheory.SW.KUnits
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW.GaussFlat

def swapCurry (α β : Type) : (α × β → ℝ) ≃ᵐ (β → α → ℝ) where
  toFun x := fun b a => x (a, b)
  invFun z := fun p => z p.2 p.1
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    refine measurable_pi_iff.2 fun b => measurable_pi_iff.2 fun a => measurable_pi_apply _
  measurable_invFun := by
    refine measurable_pi_iff.2 fun p => ?_
    exact (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)

theorem swapCurry_measurePreserving (α β : Type) [Fintype α] [Fintype β] :
    MeasurePreserving (swapCurry α β) volume volume := by
  have h : (volume : Measure (α × β → ℝ)) =
      (volume : Measure (β → α → ℝ)).map (swapCurry α β).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (swapCurry α β).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun b => Set.univ.pi (fun a => s (a, b))) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      exact ⟨fun H b a => H (a, b), fun H p => H p.2 p.1⟩
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type_right]
  refine ⟨(swapCurry α β).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem integral_cur (f : (InfinitePlace F → ι → ℝ) → ℂ) :
    ∫ x : ι × InfinitePlace F → ℝ, f (cur x) = ∫ z, f z :=
  (swapCurry_measurePreserving ι (InfinitePlace F)).integral_comp' f

theorem dot_DM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (x y : ι × InfinitePlace F → ℝ) :
    x ⬝ᵥ (DM B ρ *ᵥ y) = ∑ w, cur x w ⬝ᵥ (B.map (ρ w) *ᵥ cur y w) := by
  have h : ∀ i w, (DM B ρ *ᵥ y) (i, w) = (B.map (ρ w) *ᵥ cur y w) i := by
    intro i w
    simp only [mulVec, dotProduct, DM, Fintype.sum_prod_type_right, blockDiagonal_apply, cur]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      simp [hv.symm]
    · simp
  rw [dotProduct, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dotProduct, h, cur]

theorem gauss_fourier_flat : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ y : ι × InfinitePlace F → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (DM B ρ *ᵥ y) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) (cur y) := by
  intro F _ _ ι _ _ _ M B ρ P hQ τ hτ y
  have h := (GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier F ι M B ρ P hQ τ hτ).2.2.2 (cur y)
  rw [← h, ← integral_cur (F := F) (ι := ι) (fun z => gauss B ρ P τ z *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((∑ w, z w ⬝ᵥ (B.map (ρ w) *ᵥ cur y w) : ℝ) : ℂ)))]
  simp only [dot_DM]

end GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.infinite_component_coordinates_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (ω : HA (AF F) σ J) (x : Fin M × Fin d → F), (∀ w, xw e b (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x)))) w = ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ∧ cv (Af F) b (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x))) 0) = gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup | exact GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup | (intros; apply GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.coordinate_homeomorph_rank_one_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ M : ℕ, IsHomeomorph (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ MeasurableEmbedding (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ (coordW R b lam 1 M).map (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) = Measure.pi fun _ : Fin M × Fin d => lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.coordMap_one | exact GlobalTheory.CompanionTheory.SW.BB.coordMap_one | (intros; apply GlobalTheory.CompanionTheory.SW.BB.coordMap_one <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.GaussReg

theorem exists_lower_sup {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  have hpos : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x) := fun x hx => by
    simpa using hP.dotProduct_mulVec_pos hx
  have hcont : Continuous fun x : n → ℝ => x ⬝ᵥ (P *ᵥ x) := by fun_prop
  obtain ⟨c, hc, hmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : n → ℝ) 1, c ≤ u ⬝ᵥ (P *ᵥ u) := by
    rcases (Metric.sphere (0 : n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨u, hu, hm⟩ := (isCompact_sphere (0 : n → ℝ) 1).exists_isMinOn h hcont.continuousOn
      refine ⟨_, hpos u ?_, fun v hv => hm hv⟩
      rintro rfl
      simp at hu
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [norm_smul, hn]
  have h1 := hmin _ hu
  have h2 : (‖x‖⁻¹ • x) ⬝ᵥ (P *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (P *ᵥ x)) := by
    simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, sq, mul_assoc]
  rw [h2] at h1
  have h3 : 0 < ‖x‖ ^ 2 := by positivity
  calc c * ‖x‖ ^ 2 ≤ ((‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (P *ᵥ x))) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h3.le
    _ = x ⬝ᵥ (P *ᵥ x) := by field_simp

theorem posdef_quadratic_lower_bound_l1 {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * (∑ p, |x p|) ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  obtain ⟨c, hc, h⟩ := exists_lower_sup hP
  set N : ℝ := (Fintype.card n : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨c / (N ^ 2 + 1), by positivity, fun x => (?_ : _ ≤ _).trans (h x)⟩
  have h1 : ∑ p, |x p| ≤ N * ‖x‖ := by
    calc ∑ p, |x p| ≤ ∑ _p : n, ‖x‖ := Finset.sum_le_sum fun p _ => norm_le_pi_norm x p
      _ = N * ‖x‖ := by simp [N]
  have h0 : 0 ≤ ∑ p, |x p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : (∑ p, |x p|) ^ 2 ≤ (N ^ 2 + 1) * ‖x‖ ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_nonneg ‖x‖]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem exists_lower_family {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {P : ι → Matrix n n ℝ} (hP : ∀ i, (P i).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → n → ℝ,
      c * (∑ i, ∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
  choose c hc h using fun i => posdef_quadratic_lower_bound_l1 (hP i)
  obtain ⟨c0, hc0, hle⟩ : ∃ c0 : ℝ, 0 < c0 ∧ ∀ i, c0 ≤ c i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
    · obtain ⟨i, hi⟩ := Finite.exists_min c
      exact ⟨c i, hc i, hi⟩
  set W : ℝ := (Fintype.card ι : ℝ)
  have hW : 0 ≤ W := Nat.cast_nonneg _
  refine ⟨c0 / (W + 1), by positivity, fun y => ?_⟩
  have h1 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ W * ∑ i, (∑ p, |y i p|) ^ 2 := by
    simpa [W] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ∑ p, |y i p|)
  have hS : 0 ≤ ∑ i, (∑ p, |y i p|) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : c0 * ∑ i, (∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)).trans (h i (y i))
  refine le_trans ?_ h2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h3 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ (W + 1) * ∑ i, (∑ p, |y i p|) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hc0.le]

theorem exp_mul_pow_le {a : ℝ} (ha : 0 < a) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) {q : ℝ} (hq : a * s ^ 2 ≤ q) :
    Real.exp (-q) * (1 + s) ^ N ≤ Real.exp ((N : ℝ) ^ 2 / (4 * a)) := by
  have h1 : (1 + s) ^ N ≤ Real.exp ((N : ℝ) * s) := by
    rw [mul_comm, Real.exp_mul, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp s]) N
  calc Real.exp (-q) * (1 + s) ^ N ≤ Real.exp (-q) * Real.exp ((N : ℝ) * s) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-q + (N : ℝ) * s) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have h2 : (N : ℝ) * s ≤ a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) := by
        have : 0 ≤ (2 * a * s - N) ^ 2 / (4 * a) := by positivity
        have e : (2 * a * s - N) ^ 2 / (4 * a) = a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) - N * s := by
          field_simp
          ring
        linarith
      linarith

end GlobalTheory.CompanionTheory.SW.BB.GaussReg

namespace GlobalTheory.CompanionTheory.SW.BB

open GaussReg

theorem sizeTup_eq_sum_xw {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) :
    sizeTup b X = ∑ w, ∑ p, |xw e b X w p| := by
  simp only [sizeTup, sizeInf, xw, cv, he, Fintype.sum_prod_type, Fin.sum_univ_one]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem gaussQ_continuous_rapidDecay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ y w, |e y w| = ‖y w‖) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ), Continuous (gaussQ e b Pm) ∧ ((∀ w, (Pm w).PosDef) → RapidDecay b (fun X => (gaussQ e b Pm X : ℂ))) := by
  intro F E _ _ _ _ _ σ hCM M d b e hom he Pm
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, -, -, -, hco, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  have hxw : ∀ w p, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w p := by
    intro w p
    have h := (hco d b).continuous
    exact (continuous_apply w).comp (hom.continuous.comp ((continuous_apply p.2).comp
      (h.comp ((continuous_apply p.1).comp (continuous_apply 0)))))
  have hxw' : ∀ w, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w := fun w =>
    continuous_pi (hxw w)
  refine ⟨?_, fun hP N => ?_⟩
  · unfold gaussQ
    refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
    exact (hxw' w).dotProduct (Continuous.matrix_mulVec continuous_const (hxw' w))
  · obtain ⟨c, hc, hlow⟩ := exists_lower_family hP
    refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * (Real.pi * c))), fun X => ?_⟩
    have hs := sizeTup_eq_sum_xw b e he X
    have hs0 : 0 ≤ sizeTup b X := by
      rw [hs]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hq := hlow fun w => xw e b X w
    rw [← hs] at hq
    have hn : ‖((gaussQ e b Pm X : ℝ) : ℂ)‖ = gaussQ e b Pm X := by
      rw [Complex.norm_real, gaussQ, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hn]
    have key := exp_mul_pow_le (a := Real.pi * c) (mul_pos Real.pi_pos hc) N hs0
      (q := Real.pi * ∑ w, xw e b X w ⬝ᵥ (Pm w *ᵥ xw e b X w))
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq Real.pi_pos.le)
    simpa [gaussQ, neg_mul] using key

end GlobalTheory.CompanionTheory.SW.BB
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_block_one_first_vector_formula : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] (u : R) (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 0 = (u ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E) ∧ (∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 j.succ = (u ⊗ₜ[F] (algebraMap F E t)) * c j) ∧ ∀ i j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) i.succ j.succ = sigR R σ (c i) * inclR R (algebraMap F E t) * c j + gramR R σ J X i j := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.isUnit_det_of_mem_Bset' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit.isUnit_det_of_mem_Bset | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit.isUnit_det_of_mem_Bset | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit.isUnit_det_of_mem_Bset <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_cons_at_block_one_eq_map_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ∧ fibS σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageValue.family_at_block | exact GlobalTheory.CompanionTheory.SW.StageValue.family_at_block | (intros; apply GlobalTheory.CompanionTheory.SW.StageValue.family_at_block <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem hermR_unit_diagonalisable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (d : Fin n → Rˣ), IsUnit g.det ∧ (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * g := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ n S hS
  obtain ⟨hart, -, h2, hinv, hδ, hfix, hunit⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hσ R
  haveI : IsArtinianRing (R ⊗[F] E) := hart
  haveI : Finite (MaximalSpectrum (R ⊗[F] E)) := inferInstance
  have hrep := GlobalTheory.T.hermitian_unit_form_represents_unit (R ⊗[F] E) (sigR R σ) hinv h2 hδ
  obtain ⟨g, d, hg, hd, hgd⟩ :=
    GlobalTheory.T.hermitian_unit_form_diagonalizes (R ⊗[F] E) (sigR R σ) hinv hrep n (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S.2 hS
  choose r hr using fun i => hfix (d i) (hd i).2
  have hru : ∀ i, IsUnit (r i) := fun i => (hunit (r i)).1 (hr i ▸ (hd i).1)
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hdiag : Matrix.diagonal (fun i => (((hru i).unit : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) = Matrix.diagonal d := by
    congr 1
    funext i
    simp [hr i]
  refine ⟨g⁻¹, fun i => (hru i).unit, Matrix.isUnit_nonsing_inv_det g hg, ?_⟩
  rw [hdiag, ← hgd]
  have hc : cT (sigR R σ) g⁻¹ * cT (sigR R σ) g = 1 := by
    rw [← cT_mul, hgi, cT_one]
  calc (S : Matrix (Fin n) (Fin n) (R ⊗[F] E))
      = (cT (sigR R σ) g⁻¹ * cT (sigR R σ) g) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g * g⁻¹) := by
        rw [hc, hgi, one_mul, mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SW
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.fibre_family_integral_isContDensityOn : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → ∀ φ : V → ℂ, Continuous φ → HasCompactSupport φ → HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B φ (fun b => ∫ v, φ v ∂(fib b)) ∧ ∀ b, Integrable φ (fib b) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral | exact GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral | (intros; apply GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.proper_action_orbit_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (V : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (act : G → V → V), (Continuous fun p : G × V => act p.1 p.2) → (∀ x, act 1 x = x) → (∀ g h x, act (g * h) x = act g (act h x)) → ∀ Z : Set V, IsClosed Z → (∀ g, ∀ x ∈ Z, act g x ∈ Z) → (∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) → ∀ (μ ν : Measure V), IsLocallyFiniteMeasure μ → IsLocallyFiniteMeasure ν → μ Zᶜ = 0 → ν Zᶜ = 0 → (∀ g, μ.map (act g) = μ) → (∀ g, ν.map (act g) = ν) → ν ≠ 0 → ∃ c : ℝ≥0, μ = c • ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique | exact GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique | (intros; apply GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique <;> assumption)
end
