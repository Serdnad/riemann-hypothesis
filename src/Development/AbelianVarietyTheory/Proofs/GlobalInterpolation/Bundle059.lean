module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Mathlib.NumberTheory.Modular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle058
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentMeasureNormLeOneIffLatticeIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealQuotProd

variable {P Q P' Q' : ℕ}

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem act_mul_inv {a : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (ha : ActionCoordinates.act a x = x) (g : UpqT P Q) :
    ActionCoordinates.act (a * g)⁻¹ x = ActionCoordinates.act g⁻¹ x := by
  have : ActionCoordinates.act a⁻¹ x = x := by
    conv_lhs => rw [← ha]
    rw [← act_mul, inv_mul_cancel, act_one]
  rw [_root_.mul_inv_rev, act_mul, this]

theorem measurable_act_inv (x : ActionCoordinates.Wsp P Q) :
    Measurable fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  exact ((GlobalTheory.UpqTopology.continuous_mat.comp continuous_inv).matrix_mulVec
    continuous_const).measurable

theorem sigmaFinite_cd (c : CDHaar) (P Q : ℕ) : SigmaFinite (c.cd P Q) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI : (c.cd P Q).IsHaarMeasure := c.haar P Q
  infer_instance

theorem one_place (H : ActionCoordinates.QuotientMeasure) (c : CDHaar) {β : ℝ} (hβ : β = 1 ∨ β = -1)
    {x : ActionCoordinates.Wsp P Q} (hx : ActionCoordinates.qf x = β) {k : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q}
    {ι : UpqT P' Q' → UpqT P Q} (hk : ActionCoordinates.IsPerpFrame x k ι) {u : UpqT P Q → ℝ≥0∞}
    (hu : Measurable u) (hu' : ∀ g, Measurable (fun h => u (ι h * g)) ∧
      ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1)
    {fib : ℝ → Measure (ActionCoordinates.Wsp P Q)} (hfib : ActionCoordinates.IsDxDq β fib)
    {φ : ActionCoordinates.Wsp P Q → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ (ActionCoordinates.act g⁻¹ x) * u g ∂(c.cd P Q) =
      (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ y ∂(fib β) := by
  classical
  obtain ⟨h1, -, h3⟩ := H P Q β hβ x hx
  choose! s hs using h1
  have hae : ∀ᵐ y ∂(fib β), ActionCoordinates.qf y = β := by
    obtain ⟨U, B, -, -, -, hF⟩ := hfib
    have h1 : ∀ᵐ y ∂(fib β), y ∈ ActionCoordinates.qf ⁻¹' {id β} ∩ U := hF.1 β
    filter_upwards [h1] with y hy using hy.1
  rw [(h3 P' Q' k ι hk).2 c fib hfib s hs (fun g => φ (ActionCoordinates.act g⁻¹ x) * u g)
    ((hφ.comp (measurable_act_inv x)).mul hu),
    Measure.restrict_eq_self_of_ae_mem (s := {y | ActionCoordinates.qf y = β}) hae]
  congr 1
  refine lintegral_congr_ae (hae.mono fun y hy => ?_)
  have e : ∀ h, φ (ActionCoordinates.act (ι h * s y)⁻¹ x) = φ y := fun h => by
    rw [act_mul_inv (hk.2.2 h).1, hs y hy]
  simp only [e]
  rw [lintegral_const_mul _ (hu' _).1, (hu' _).2, mul_one]

theorem quot_integral_prod : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  intro H c T _ P Q P' Q' β hβ x hx k ι hk u hu j hj ν hν fib hfib φ hφ
  haveI := sigmaFinite_cd c P Q
  haveI := sigmaFinite_cd c P' Q'
  let f : T → UpqT P Q → ℝ≥0∞ := fun ρ g => φ ρ (ActionCoordinates.act g⁻¹ (x ρ)) * u ρ g
  have hf : ∀ ρ, Measurable (f ρ) := fun ρ =>
    ((hφ ρ).comp (measurable_act_inv (x ρ))).mul (hu ρ).1
  have key := hν (fun g => ∏ ρ, f ρ (g ρ))
    (Finset.measurable_prod _ fun ρ _ => (hf ρ).comp (measurable_pi_apply ρ))
  rw [GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf] at key
  rw [← Finset.prod_congr rfl fun ρ _ =>
    one_place H c hβ (hx ρ) (hk ρ) (hu ρ).1 (hu ρ).2 hfib (hφ ρ)]
  refine Eq.trans (lintegral_congr fun s => ?_) key.symm
  have e : ∀ h : T → UpqT P' Q', ∏ ρ, f ρ ((j h * s.out) ρ) =
      ∏ ρ, (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ)) ρ (h ρ) :=
    fun h => Finset.prod_congr rfl fun ρ _ => by
      simp only [f, Pi.mul_apply, hj]
      rw [act_mul_inv ((hk ρ).2.2 _).1]
  rw [lintegral_congr e, GlobalTheory.SnMass.Push.lintegral_fintype_prod
    (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ))
    (fun ρ => (((hu ρ).2 _).1).const_mul _)]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [lintegral_const_mul _ ((hu ρ).2 _).1, ((hu ρ).2 _).2, mul_one]

end GlobalTheory.RealQuotProd
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.IdealLattice

open scoped MatrixGroups UpperHalfPlane

theorem wK_mul_mem (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    ∀ z ∈ lamOf D c x, ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * z ∈ lamOf D c x := by
  intro z hz
  obtain ⟨o, ho⟩ := (GlobalTheory.MomDict.inOK_iff D ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2)).1
    ⟨0, 1, by simp [GlobalTheory.MomOne.wK]⟩
  obtain ⟨a, ha, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D c x z).1 hz
  refine (GlobalTheory.CurveLattice.mem_lamOf D c x _).2 ⟨o * a, c.mul_mem_left o ha, ?_⟩
  rw [ho]; simp; ring

theorem exists_reduced {Λ : AddSubgroup ℂ} {b : ℂ} {τ₀ : ℍ} (hb : b ≠ 0)
    (h : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, b * (m * (τ₀ : ℂ) + n) = z) :
    ∃ ω₁ : ℂ, ∃ τ : ℍ, ω₁ ≠ 0 ∧ τ ∈ ModularGroup.fd ∧ JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ τ := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ₀
  set A : ℤ := g 0 0 with hA
  set B : ℤ := g 0 1 with hB
  set C : ℤ := g 1 0 with hC
  set E : ℤ := g 1 1 with hE
  have hdet : A * E - B * C = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hdetC : (A : ℂ) * E - B * C = 1 := by exact_mod_cast hdet
  have hco : ((g • τ₀ : ℍ) : ℂ) = (A * τ₀ + B) / (C * τ₀ + E) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [A, B, C, E]
  have hden : (C * (τ₀ : ℂ) + E) ≠ 0 := by
    intro h0
    have := (g • τ₀).im_pos
    rw [← UpperHalfPlane.coe_im, hco, h0, div_zero] at this
    simp at this
  refine ⟨b * (C * τ₀ + E), g • τ₀, mul_ne_zero hb hden, hg, fun z => ?_⟩
  rw [h, hco]
  have key : ∀ m n : ℂ, (C * (τ₀ : ℂ) + E) * (m + n * ((A * τ₀ + B) / (C * τ₀ + E))) =
      m * (C * τ₀ + E) + n * (A * τ₀ + B) := fun m n => by
    field_simp
  constructor
  · rintro ⟨M, N, rfl⟩
    refine ⟨N * A - M * B, M * E - N * C, ?_⟩
    rw [mul_assoc, key]
    push_cast
    linear_combination (-b * (M * (τ₀ : ℂ) + N)) * hdetC
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * C + n * A, m * E + n * B, ?_⟩
    rw [mul_assoc, key]
    push_cast
    ring

theorem main : ∀ (D : D7) (c : Ideal (𝓞 D.host.K)), c ≠ ⊥ → ∀ x : ℂ, x ≠ 0 →
    (∀ z ∈ lamOf D c x, ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * z ∈ lamOf D c x) ∧
    ∃ ω₁ τ : ℂ, ω₁ ≠ 0 ∧ 0 < τ.im ∧ JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D c x) ω₁ τ ∧
      1 / 2 ≤ τ.im ∧ 2 * τ.im ≤ Real.sqrt D.host.d := by
  intro D c hc x hx
  have hst := wK_mul_mem D c x
  refine ⟨hst, ?_⟩
  obtain ⟨a, τ₀, ha, -, hlat⟩ := GlobalTheory.CurveLattice.exists_tau D c hc
  obtain ⟨ω₁, τ, hω, hfd, hper⟩ := exists_reduced (Λ := lamOf D c x) (b := x * a) (τ₀ := τ₀)
    (mul_ne_zero hx ha) (hlat x)
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have him' : 0 < τ.im := τ.im_pos
  have hci : (τ : ℂ).im = τ.im := rfl
  refine ⟨ω₁, τ, hω, him, hper, ?_, ?_⟩
  · have h1 := hfd.1
    have h2 := hfd.2
    rw [Complex.normSq_apply] at h1
    have hre : ((τ : ℂ).re) ^ 2 ≤ 1 / 4 := by
      have := abs_le.1 h2
      simp only [UpperHalfPlane.re] at this
      nlinarith [this.1, this.2]
    nlinarith
  · have hmem : ω₁ ∈ lamOf D c x := (hper ω₁).2 ⟨1, 0, by simp⟩
    obtain ⟨m, n, hmn⟩ := (hper _).1 (hst ω₁ hmem)
    have hw : (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = (m : ℂ) + n * τ := by
      have := hmn
      rw [mul_comm] at this
      exact mul_left_cancel₀ hω (by rw [← this])
    have him2 := congrArg Complex.im hw
    simp at him2
    have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    have hn : (0 : ℝ) < n := by
      by_contra hn
      have hn' : (n : ℝ) ≤ 0 := le_of_not_gt hn
      nlinarith
    have hn1 : (1 : ℝ) ≤ n := by
      have : (0 : ℤ) < n := by exact_mod_cast hn
      exact_mod_cast this
    rw [hci]
    nlinarith

end GlobalTheory.IdealLattice
end
end

section

noncomputable section

namespace GlobalTheory.Proof.StabilizerGroupMap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

theorem bc_inclE_injective (D : D7) :
    Function.Injective
      (bc (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
        GL (Fin D.R.k) D.host.E →*
          GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    exact (evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) := inferInstance
  intro a b hab
  refine Units.ext (Matrix.ext fun i j => ?_)
  apply (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).injective
  have h2 := congrArg (fun g : GL (Fin D.R.k) _ => g.val i j) hab
  simpa [bc] using h2

theorem stabGroup_eq_map (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y =
      (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y).map
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.map_colStab D Lv u y).symm

theorem stabGroup_eq_bot_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥ ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y = ⊥ := by
  rw [stabGroup_eq_map, Subgroup.map_eq_bot_iff_of_injective _ (bc_inclE_injective D)]

theorem at_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    (GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D, GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥) ↔
      GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivialAt D Lv u := by
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact ⟨fun h y => (stabGroup_eq_bot_iff D Lv u y).1 (h y.1 y.2),
    fun h y hy => (stabGroup_eq_bot_iff D Lv u ⟨y, hy⟩).2 (h ⟨y, hy⟩)⟩

theorem columnStabilisersTrivial_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.ColumnStabilisersTrivial ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivial :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => at_iff D Lv u

end GlobalTheory.Proof.StabilizerGroupMap

end
end

section

open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

namespace GlobalTheory

theorem exists_unfoldingKernel_levelSubgroup_bruhat : ∀ (G G' T T' : Type) [Group G] [Group G'] [Group T] [Group T'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableSpace T] [MeasurableSpace T'] [MeasurableMul G'] [MeasurableMul T] [MeasurableInv T'] (μ : Measure G) (μ' : Measure G') [μ'.IsMulLeftInvariant] (m : Measure T) (m' : Measure T') [m'.IsInvInvariant] (K : Subgroup G) (K' : Subgroup G'), MeasurableSet (K : Set G) → MeasurableSet (K' : Set G') → ∀ (φ : G' →* G) (ψ : G →* T) (ψ' : G' →* T') (j : T' →* T), Measurable ψ → Measurable ψ' → Measurable j → (∀ g, φ g ∈ K ↔ g ∈ K') → (∀ g, ψ (φ g) = j (ψ' g)) → (μ.restrict K).map ψ = m → (μ'.restrict K').map ψ' = m' → ∀ (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∀ (f : T → ℝ≥0∞), Measurable f → (∀ s t, f (j s * t) = f t) → ∀ ν, IsQuotientMeasure j m' m ν → ∃ u : G → ℝ≥0∞, Measurable u ∧ ∫⁻ h, u h ∂μ = ∫⁻ c, f (Quotient.out c) ∂ν ∧ ∀ h, ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ' = {h | ∃ g, (φ g)⁻¹ * h ∈ K}.indicator 1 h * f (ψ h) := by
  intro G G' T T' _ _ _ _ _ _ _ _ _ _ _ μ μ' _ m m' _ K K' hK hK' φ ψ ψ' j hψ hψ' hj hφK hcomm
    hm hm' b hb hb1 f hf hfinv ν hν
  have hbf : Measurable fun t => b t * f t := hb.mul hf
  refine ⟨(K : Set G).indicator (fun h => b (ψ h) * f (ψ h)), (hbf.comp hψ).indicator hK, ?_, ?_⟩
  · rw [lintegral_indicator hK, ← lintegral_map hbf hψ, hm, hν _ hbf]
    refine lintegral_congr fun c => ?_
    simp only [hfinv]
    rw [lintegral_mul_const _ (f := fun s => b (j s * Quotient.out c))
      (hb.comp (hj.mul_const _)), hb1, one_mul]
  · intro h
    by_cases hh : ∃ g, (φ g)⁻¹ * h ∈ K
    · obtain ⟨g₀, hk⟩ := hh
      have hmem : h ∈ {h | ∃ g, (φ g)⁻¹ * h ∈ K} := ⟨g₀, hk⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
      obtain ⟨k, rfl⟩ : ∃ k, h = φ g₀ * k := ⟨(φ g₀)⁻¹ * h, by simp⟩
      rw [inv_mul_cancel_left] at hk
      rw [← lintegral_mul_left_eq_self _ g₀]
      have hF : Measurable fun s : T' => b (j s⁻¹ * ψ k) :=
        hb.comp ((hj.comp measurable_inv).mul_const _)
      have key : ∀ g, (K : Set G).indicator (fun h => b (ψ h) * f (ψ h))
          ((φ (g₀ * g))⁻¹ * (φ g₀ * k)) =
          (K' : Set G').indicator (fun g => b (j (ψ' g)⁻¹ * ψ k) * f (ψ k)) g := by
        intro g
        have e : (φ (g₀ * g))⁻¹ * (φ g₀ * k) = (φ g)⁻¹ * k := by
          rw [map_mul]; group
        have e2 : ψ ((φ g)⁻¹ * k) = j (ψ' g)⁻¹ * ψ k := by
          rw [map_mul, map_inv, hcomm, map_inv]
        rw [e]
        by_cases hg : g ∈ K'
        · have : (φ g)⁻¹ * k ∈ (K : Set G) := K.mul_mem (K.inv_mem ((hφK g).2 hg)) hk
          rw [Set.indicator_of_mem this, Set.indicator_of_mem (show g ∈ (K' : Set G') from hg),
            e2, hfinv]
        · have : (φ g)⁻¹ * k ∉ (K : Set G) := fun hx =>
            hg ((hφK g).1 (K.inv_mem_iff.1 ((K.mul_mem_cancel_right hk).1 hx)))
          rw [Set.indicator_of_notMem this,
            Set.indicator_of_notMem (show g ∉ (K' : Set G') from hg)]
      simp only [key]
      rw [lintegral_indicator hK',
        ← lintegral_map (f := fun s : T' => b (j s⁻¹ * ψ k) * f (ψ k)) (hF.mul_const _) hψ', hm',
        lintegral_mul_const _ hF, lintegral_inv_eq_self (fun s => b (j s * ψ k)), hb1, one_mul,
        map_mul, hcomm, hfinv]
    · have hmem : h ∉ {h | ∃ g, (φ g)⁻¹ * h ∈ K} := hh
      rw [Set.indicator_of_notMem hmem, zero_mul]
      have : ∀ g, (K : Set G).indicator (fun h => b (ψ h) * f (ψ h)) ((φ g)⁻¹ * h) = 0 :=
        fun g => Set.indicator_of_notMem (fun hx => hh ⟨g, hx⟩) _
      simp only [this, lintegral_zero]

end GlobalTheory
end

section

open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

namespace GlobalTheory


open MeasureTheory Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction :
    ∀ (T T' : Type) [Group T] [MeasurableSpace T] [MeasurableMul₂ T] [Group T'] [MeasurableSpace T']
      [MeasurableMul T'] [MeasurableInv T'] (j : T' →* T), Measurable j →
      ∀ (m : Measure T) [SFinite m] [m.IsMulLeftInvariant] (m' : Measure T') [SFinite m']
        [m'.IsMulRightInvariant] [m'.IsInvInvariant] (b : T → ℝ≥0∞), Measurable b →
        (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∃ ν, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.IsQuotientMeasure j m' m ν := by
  intro T T' _ _ _ _ _ _ _ j hj m _ _ m' _ _ _ b hb hint
  refine ⟨(m.withDensity b).map (Quotient.mk'' : T → _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j), ?_⟩
  intro f hf
  set F : T → ℝ≥0∞ := fun t => ∫⁻ s, f (j s * t) ∂m' with hFdef
  have hF : Measurable F := by
    have hprod : Measurable fun p : T × T' => f (j p.2 * p.1) :=
      hf.comp ((hj.comp measurable_snd).mul measurable_fst)
    exact hprod.lintegral_prod_right'
  have hG : ∀ t : T,
      ∫⁻ s, f (j s * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j)) ∂m' = F t := by
    intro t
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel j.range) t
    obtain ⟨u, hu⟩ := QuotientGroup.rightRel_apply.mp hrel
    have ht : t = j u * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j) := by
      change t = j u * Quotient.out (Quotient.mk (QuotientGroup.rightRel j.range) t)
      rw [hu, inv_mul_cancel_right]
    simp only [hFdef]
    conv_rhs => rw [ht]
    simp_rw [← mul_assoc, ← map_mul]
    exact (lintegral_mul_right_eq_self
      (fun s => f (j s * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j))) u).symm
  set G : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j → ℝ≥0∞ := fun c => ∫⁻ s, f (j s * Quotient.out c) ∂m' with hGdef
  have hGmeas : Measurable G := by
    refine (measurable_from_quotient (s := QuotientGroup.rightRel j.range)).mpr ?_
    convert hF using 1
    funext t
    exact hG t
  have key : ∫⁻ t, f t ∂m = ∫⁻ t, b t * F t ∂m := by
    calc ∫⁻ t, f t ∂m = ∫⁻ t, (∫⁻ s, b (j s * t) ∂m') * f t ∂m :=
          lintegral_congr fun t => by rw [hint t, one_mul]
      _ = ∫⁻ t, ∫⁻ s, b (j s * t) * f t ∂m' ∂m :=
          lintegral_congr fun t => (lintegral_mul_const _ (hb.comp (hj.mul_const t))).symm
      _ = ∫⁻ s, ∫⁻ t, b (j s * t) * f t ∂m ∂m' :=
          lintegral_lintegral_swap
            ((hb.comp ((hj.comp measurable_snd).mul measurable_fst)).mul
              (hf.comp measurable_fst)).aemeasurable
      _ = ∫⁻ s, ∫⁻ t, b t * f (j s⁻¹ * t) ∂m ∂m' := lintegral_congr fun s => by
          have h := lintegral_mul_left_eq_self (μ := m) (fun t => b t * f (j s⁻¹ * t)) (j s)
          simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h
          exact h
      _ = ∫⁻ t, ∫⁻ s, b t * f (j s⁻¹ * t) ∂m' ∂m :=
          lintegral_lintegral_swap
            ((hb.comp measurable_snd).mul
              (hf.comp ((hj.comp measurable_fst.inv).mul measurable_snd))).aemeasurable
      _ = ∫⁻ t, b t * F t ∂m := lintegral_congr fun t => by
          have hmeas : Measurable fun s : T' => f (j s⁻¹ * t) :=
            hf.comp ((hj.comp measurable_inv).mul_const t)
          rw [lintegral_const_mul _ hmeas]
          congr 1
          exact lintegral_inv_eq_self (fun s => f (j s * t))
  calc ∫⁻ t, f t ∂m = ∫⁻ t, b t * F t ∂m := key
    _ = ∫⁻ t, b t * G (Quotient.mk'' t) ∂m := lintegral_congr fun t => by rw [← hG t]
    _ = ∫⁻ t, G (Quotient.mk'' t) ∂(m.withDensity b) :=
        (lintegral_withDensity_eq_lintegral_mul _ hb (hGmeas.comp measurable_quotient_mk'')).symm
    _ = ∫⁻ c, G c ∂((m.withDensity b).map (Quotient.mk'' : T → _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j)) :=
        (lintegral_map hGmeas measurable_quotient_mk'').symm

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Proof.StabilizerIndex

lemma index_field (F : Type) [Field F] [Finite F] (k : ℕ) (φ : Fin k → F) (hφ : φ ≠ 0) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index = Nat.card F ^ k - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := Formalism.LogVandermondeBounds.StandardLattice.cardStabilizerVector F k φ hφ
  have hcm := (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).card_mul_index
  have hc : Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ) =
      Nat.card {A : GL (Fin k) F // Matrix.vecMul φ (A : Matrix (Fin k) (Fin k) F) = φ} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun A => Iff.rfl))
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← hc, ← hcm] at h
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h).symm

theorem index_stabRow : ∀ (κ : Type) [CommRing κ] (T k : ℕ), T.Prime → Nat.card κ = T →
    ∀ φ : Fin k → κ, φ ≠ 0 →
      (((GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index : ℕ) : ℝ) = (T : ℝ) ^ k - 1 := by
  intro κ _ T k hT hcard φ hφ
  haveI : Fact T.Prime := ⟨hT⟩
  haveI : Finite κ := Nat.finite_of_card_ne_zero (hcard ▸ hT.ne_zero)
  letI : Fintype κ := Fintype.ofFinite κ
  have e : ZMod T ≃+* κ := ZMod.ringEquivOfPrime κ hT (by rw [← Nat.card_eq_fintype_card, hcard])
  have hF : IsField κ := MulEquiv.isField (Field.toIsField (ZMod T)) e.symm.toMulEquiv
  have h := @index_field κ hF.toField _ k φ hφ
  have h' : (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index = T ^ k - 1 := by
    rw [← hcard]; exact h
  rw [h', Nat.cast_sub (Nat.one_le_pow _ _ hT.pos)]
  push_cast
  rfl

end GlobalTheory.Proof.StabilizerIndex
end

section

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (δ₀ : ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (t : Fin g → ℂ) (G : (Fin g → ℂ) → ℂ) (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]), (∀ z : Qbar, ι (z : ℂ) = lam z) → δ₀ ≠ 0 → ‖Ω‖ = 1 → S.Ok → GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.PrimeTo q t → ContDiff ℂ ⊤ G → MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G → (‖μ‖ ≤ 1 ↔ LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup G) := by
  first | exact @GlobalTheory.MomN.norm_le_one_iff_latInt | exact GlobalTheory.MomN.norm_le_one_iff_latInt | (intros; apply GlobalTheory.MomN.norm_le_one_iff_latInt <;> assumption)
end
