module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle397
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

@[expose] public section

section

noncomputable section

open Matrix Module PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.IwaDecomp

section Isometry

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

def isoOfFinrank (h : finrank ℂ F = finrank ℂ G) : F ≃ₗᵢ[ℂ] G :=
  (stdOrthonormalBasis ℂ F).equiv (stdOrthonormalBasis ℂ G) (finCongr h)

theorem exists_extend (h : finrank ℂ F = finrank ℂ G) (S : Submodule ℂ F) (φ : S →ₗᵢ[ℂ] G) :
    ∃ ψ : F →ₗᵢ[ℂ] G, ∀ s : S, ψ s = φ s := by
  let e := isoOfFinrank h
  let L : S →ₗᵢ[ℂ] F := e.symm.toLinearIsometry.comp φ
  refine ⟨e.toLinearIsometry.comp L.extend, fun s => ?_⟩
  simp [L, LinearIsometry.extend_apply]

theorem finrank_map_isometry (K : E →ₗᵢ[ℂ] E) (A : Submodule ℂ E) :
    finrank ℂ (A.map K.toLinearMap) = finrank ℂ A :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective K.toLinearMap K.injective A)).symm

theorem exists_isometry_flag {A₁ A₂ B₁ B₂ : Submodule ℂ E} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, A₁.map K.toLinearMap = B₁ ∧ A₂.map K.toLinearMap = B₂ := by
  let φ : A₁ ≃ₗᵢ[ℂ] B₁ := isoOfFinrank h₁
  let S : Submodule ℂ A₂ := A₁.comap A₂.subtype
  let ι : S →ₗᵢ[ℂ] A₁ :=
    ⟨LinearMap.codRestrict A₁ (A₂.subtype ∘ₗ S.subtype) (fun x => x.2), fun x => rfl⟩
  let j : B₁ →ₗᵢ[ℂ] B₂ := ⟨Submodule.inclusion hB, fun x => rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_extend h₂ S (j.comp (φ.toLinearIsometry.comp ι))
  let L : A₂ →ₗᵢ[ℂ] E := B₂.subtypeₗᵢ.comp ψ
  have hK : ∀ a : A₂, L.extend a = ψ a := fun a => by
    simpa [L] using LinearIsometry.extend_apply L a
  refine ⟨L.extend, ?_, ?_⟩
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₁)
    rintro _ ⟨a, ha, rfl⟩
    have h := hK ⟨a, hA ha⟩
    have h2 := hψ ⟨⟨a, hA ha⟩, ha⟩
    change L.extend a ∈ B₁
    rw [show L.extend a = ((ψ ⟨a, hA ha⟩ : B₂) : E) from h, show ψ ⟨a, hA ha⟩ = _ from h2]
    exact (φ (ι ⟨⟨a, hA ha⟩, ha⟩)).2
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₂)
    rintro _ ⟨a, ha, rfl⟩
    change L.extend a ∈ B₂
    rw [show L.extend a = ((ψ ⟨a, ha⟩ : B₂) : E) from hK ⟨a, ha⟩]
    exact (ψ ⟨a, ha⟩).2

theorem exists_isometry_flag_of_equiv {V : Type*} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] E)
    {A₁ A₂ B₁ B₂ : Submodule ℂ V} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, (A₁.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₁.map (e : V →ₗ[ℂ] E) ∧
      (A₂.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₂.map (e : V →ₗ[ℂ] E) := by
  have hT : ∀ W : Submodule ℂ V, finrank ℂ (W.map (e : V →ₗ[ℂ] E)) = finrank ℂ W :=
    fun W => LinearEquiv.finrank_map_eq e W
  exact exists_isometry_flag (Submodule.map_mono hA) (Submodule.map_mono hB)
    (by rw [hT, hT, h₁]) (by rw [hT, hT, h₂])

end Isometry

variable {n : ℕ}

theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  simp [img]

theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img (a * b) W = img a (img b W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem img_mono (a : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') : img a W ≤ img a W' :=
  Submodule.map_mono h

def linEquiv (g : GL (Fin n) ℂ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.toLin'OfInv (M := (g⁻¹ : GL (Fin n) ℂ).val) (M' := g.val) (by simp) (by simp)

theorem img_eq_map_linEquiv (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img g W = W.map (linEquiv g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  rfl

theorem finrank_img (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : finrank ℂ (img g W) = finrank ℂ W := by
  rw [img_eq_map_linEquiv]
  exact LinearEquiv.finrank_map_eq (linEquiv g) W

theorem thetaR_eq_self_iff (k : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n k = k ↔ k.val.conjTranspose = (k⁻¹ : GL (Fin n) ℂ).val := by
  have h : (thetaR (starRingEnd ℂ) n k).val = (k⁻¹ : GL (Fin n) ℂ).val.conjTranspose := by
    rw [thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]
  constructor
  · intro e
    have h' := congrArg Units.val e
    rw [h] at h'
    rw [← h', Matrix.conjTranspose_conjTranspose]
  · intro e
    refine Units.ext ?_
    rw [h, ← e, Matrix.conjTranspose_conjTranspose]

abbrev eu (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm

theorem unitary_of_isometry (K : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧
      ∀ W : Submodule ℂ (Fin n → ℂ), (img k W).map (eu n : (Fin n → ℂ) →ₗ[ℂ] _) =
        (W.map (eu n : (Fin n → ℂ) →ₗ[ℂ] _)).map K.toLinearMap := by
  let f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    ((eu n).symm : _ →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ K.toLinearMap ∘ₗ (eu n : (Fin n → ℂ) →ₗ[ℂ] _)
  let M : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' f
  have hM : Matrix.toLin' M = f := Matrix.toLin'_toMatrix' f
  have key : ∀ x y : Fin n → ℂ, f y ⬝ᵥ star (f x) = y ⬝ᵥ star x := fun x y => by
    have := K.inner_map_map (eu n x) (eu n y)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    exact this
  have hc : ∀ i l, M l i = f (Pi.single i 1) l := fun i l => by
    rw [← hM, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  have h1 : M.conjTranspose * M = 1 := by
    ext i j
    have h := key (Pi.single i 1) (Pi.single j 1)
    have e : (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ star (Pi.single i 1 : Fin n → ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      rw [single_one_dotProduct]
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [← e, ← h]
    simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, hc, Pi.star_apply, mul_comm]
  have h2 : M * M.conjTranspose = 1 := mul_eq_one_comm.1 h1
  let k : GL (Fin n) ℂ := ⟨M, M.conjTranspose, h2, h1⟩
  refine ⟨k, (thetaR_eq_self_iff k).2 rfl, fun W => ?_⟩
  have : (k.val : Matrix (Fin n) (Fin n) ℂ) = M := rfl
  change Submodule.map _ (Submodule.map (Matrix.toLin' M) W) = _
  rw [hM, ← Submodule.map_comp, ← Submodule.map_comp]
  refine congrArg (fun t => Submodule.map t W) (LinearMap.ext fun x => ?_)
  simp [f]

theorem img_mul_inv_eq {g k : GL (Fin n) ℂ} {W : Submodule ℂ (Fin n → ℂ)} (h : img k (img g⁻¹ W) = W) :
    img (g * k⁻¹) W = W := by
  conv_lhs => rw [← h]
  rw [← img_mul, ← img_mul, show g * k⁻¹ * k * g⁻¹ = 1 by group, img_one]

theorem exists_flag_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧ img k (img g⁻¹ W₁) = W₁ ∧ img k (img g⁻¹ W₂) = W₂ := by
  obtain ⟨K, hK₁, hK₂⟩ := exists_isometry_flag_of_equiv (eu n) (img_mono g⁻¹ h) h
    (finrank_img g⁻¹ W₁) (finrank_img g⁻¹ W₂)
  obtain ⟨k, hk, hkK⟩ := unitary_of_isometry K
  have hinj : Function.Injective (eu n : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := (eu n).injective
  have inj := Submodule.map_injective_of_injective hinj
  exact ⟨k, hk, inj ((hkK _).trans hK₁), inj ((hkK _).trans hK₂)⟩

theorem exists_eq_mul_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ q k : GL (Fin n) ℂ, g = q * k ∧ thetaR (starRingEnd ℂ) n k = k ∧ img q W₁ = W₁ ∧ img q W₂ = W₂ := by
  obtain ⟨k, hk, h₁, h₂⟩ := exists_flag_unitary W₁ W₂ h g
  exact ⟨g * k⁻¹, k, by group, hk, img_mul_inv_eq h₁, img_mul_inv_eq h₂⟩

theorem iwaFlag : PositivityTheory.Rg.BcB.D4.IwaFlag := fun _ W₁ W₂ h g => by
  obtain ⟨q, k, e, hk, h₁, h₂⟩ := exists_eq_mul_unitary W₁ W₂ h g
  exact ⟨q, ⟨h₁, h₂⟩, k, hk, e⟩

end GlobalTheory.CompanionTheory.IwaDecomp
end
end

section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotNorm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
  {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]

theorem ae_lt_top_of_normaliser {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    ∀ᵐ g ∂μG, ρ g < ∞ := by
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  set E : Set G := {g | ρ g = ∞} with hEdef
  have hE : MeasurableSet E := hρ.1 (measurableSet_singleton ∞)
  have hind : Measurable (E.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hE
  have hzero : ∀ g : G, ∫⁻ h : H, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μH = 0 := by
    intro g
    have hm : Measurable fun h : H => ρ ((h : G) * g) :=
      hρ.1.comp (measurable_subtype_coe.mul_const g)
    have hfin : ∀ᵐ h : H ∂μH, ρ ((h : G) * g) < ∞ :=
      ae_lt_top hm (by rw [hρ.2 g]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hfin] with h hh
    simp [hEdef, Set.indicator, hh.ne]
  have key : ∫⁻ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG ∂μH = 0 := by
    rw [lintegral_lintegral_swap]
    · simp [hzero]
    · exact (hind.comp hmulH).aemeasurable
  have h2 : ∀ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG = μG E := fun h => by
    rw [lintegral_mul_left_eq_self (E.indicator (1 : G → ℝ≥0∞)) (h : G),
      lintegral_indicator_one hE]
  simp only [h2, lintegral_const] at key
  have hne : μH Set.univ ≠ 0 := by
    intro h0
    have h1 := hρ.2 1
    rw [Measure.measure_univ_eq_zero.1 h0] at h1
    simp at h1
  have hE0 : μG E = 0 := (mul_eq_zero.1 key).resolve_right hne
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE0] with g hg
  exact lt_top_iff_ne_top.2 hg

theorem integral_nonneg_normaliser_eq {f : G → ℝ} (hf : Measurable f) (hf0 : ∀ g, 0 ≤ f g)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫ g, f g * (σ g).toReal ∂μG = (∫⁻ g, ENNReal.ofReal (f g) * σ g ∂μG).toReal := by
    intro σ hσ
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun g => mul_nonneg (hf0 g) ENNReal.toReal_nonneg)
      (hf.mul hσ.1.ennreal_toReal).aestronglyMeasurable]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [ENNReal.ofReal_mul (hf0 g), ENNReal.ofReal_toReal hg.ne]
  rw [aux hρ, aux hρ', lintegral_normaliser_eq (F := fun g => ENNReal.ofReal (f g))
    hf.ennreal_ofReal (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integrable_normaliser_iff {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG ↔
      Integrable (fun g => F g * ((ρ' g).toReal : ℂ)) μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫⁻ g, ‖F g * ((σ g).toReal : ℂ)‖ₑ ∂μG = ∫⁻ g, ‖F g‖ₑ * σ g ∂μG := by
    intro σ hσ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((σ g).toReal : ℂ), Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hg.ne]
  have hm : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      AEStronglyMeasurable (fun g => F g * ((σ g).toReal : ℂ)) μG := fun hσ =>
    (hF.mul (Complex.measurable_ofReal.comp hσ.1.ennreal_toReal)).aestronglyMeasurable
  have heq := lintegral_normaliser_eq (μG := μG) (F := fun g => ‖F g‖ₑ) hF.enorm
    (fun h hh g => by simp only [hFH h hh g]) hρ hρ'
  simp only [Integrable, hm hρ, hm hρ', true_and, hasFiniteIntegral_iff_enorm, aux hρ, aux hρ', heq]

theorem integral_real_normaliser_eq {f : G → ℝ} (hf : Measurable f)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ')
    (hi : Integrable (fun g => f g * (ρ g).toReal) μG)
    (hi' : Integrable (fun g => f g * (ρ' g).toReal) μG) :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have part : ∀ {σ : G → ℝ≥0∞} {u : G → ℝ}, IsQuotNormaliser H μH σ → Measurable u →
      (∀ g, |u g| ≤ |f g|) → Integrable (fun g => f g * (σ g).toReal) μG →
      Integrable (fun g => u g * (σ g).toReal) μG := by
    intro σ u hσ hu hle h
    refine h.mono (hu.mul hσ.1.ennreal_toReal).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle g) (abs_nonneg _)
  have hp : Measurable fun g => max (f g) 0 := hf.max measurable_const
  have hn : Measurable fun g => max (-f g) 0 := hf.neg.max measurable_const
  have hpl : ∀ g, |max (f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnl : ∀ g, |max (-f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have dec : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      Integrable (fun g => f g * (σ g).toReal) μG →
      ∫ g, f g * (σ g).toReal ∂μG =
        ∫ g, max (f g) 0 * (σ g).toReal ∂μG - ∫ g, max (-f g) 0 * (σ g).toReal ∂μG := by
    intro σ hσ h
    rw [← integral_sub (part hσ hp hpl h) (part hσ hn hnl h)]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    have : f g = max (f g) 0 - max (-f g) 0 := (max_zero_sub_max_neg_zero_eq_self (f g)).symm
    simp only
    rw [← sub_mul, ← this]
  rw [dec hρ hi, dec hρ' hi',
    integral_nonneg_normaliser_eq hp (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ',
    integral_nonneg_normaliser_eq hn (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integral_normaliser_eq_of {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μG := by
  have hiff := integrable_normaliser_iff (μG := μG) hF hFH hρ hρ'
  by_cases hi : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG
  · have hi' := hiff.1 hi
    have ere : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).re * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).re = ∫ g, (F g).re * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.reCLM.integrable_comp h
      have h2 := Complex.reCLM.integral_comp_comm h
      simp only [Complex.reCLM_apply, Complex.re_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    have eim : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).im * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).im = ∫ g, (F g).im * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.imCLM.integrable_comp h
      have h2 := Complex.imCLM.integral_comp_comm h
      simp only [Complex.imCLM_apply, Complex.im_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    apply Complex.ext
    · rw [(ere hi).2, (ere hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_re.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (ere hi).1 (ere hi').1
    · rw [(eim hi).2, (eim hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_im.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (eim hi).1 (eim hi').1
  · rw [integral_undef hi, integral_undef (fun h => hi (hiff.2 h))]

theorem quotIntegral_eq {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    quotIntegral μG H μH F = ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG := by
  have hex : ∃ ρ, IsQuotNormaliser H μH ρ := ⟨ρ, hρ⟩
  rw [quotIntegral, dite_eq_left hex]
  exact integral_normaliser_eq_of hF hFH hex.choose_spec hρ

theorem integral_normaliser_eq : PositivityTheory.Rg.BcB.D4.NormEq := by
  intro G _ _ _ _ _ _ _ μ _ H μH _ _ F ρ₁ ρ₂ hF hFH hρ₁ hρ₂
  exact integral_normaliser_eq_of (μG := μ) hF hFH hρ₁ hρ₂

end GlobalTheory.CompanionTheory.QuotNorm
end
end

section

open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelPoint

open Matrix PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem block_relations (A B D : Matrix (Fin n) (Fin n) ℂ)
    (h : InG (fromBlocks A B 0 D : M2 n)) : Aᴴ * D = 1 ∧ Bᴴ * D = Dᴴ * B := by
  unfold InG JJ at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.mp h
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero] at h12 h22
  exact ⟨h12, (neg_add_eq_zero.mp h22).symm⟩

theorem levi_inG (a D : Matrix (Fin n) (Fin n) ℂ) (h : aᴴ * D = 1) :
    InG (fromBlocks a 0 0 D : M2 n) := by
  have h' : Dᴴ * a = 1 := by
    have h2 := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h2
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, h, h', neg_zero]

theorem siegel_point :
    ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 →
      ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧
        PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧
        p = nb * ma ∧
        ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) *
            ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ =
          b + Complex.I • (a * aᴴ) := by
  intro n p hp
  set A := (mR p).toBlocks₁₁ with hA
  set B := (mR p).toBlocks₁₂ with hB
  set D := (mR p).toBlocks₂₂ with hD
  have hpm : mR p = fromBlocks A B 0 D := by
    rw [← hp]
    exact (fromBlocks_toBlocks (mR p)).symm
  have hG : InG (mR p) := p.2
  rw [hpm] at hG
  obtain ⟨h1, h2⟩ := block_relations A B D hG
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hADh : A * Dᴴ = 1 := by
    have h3 := congrArg conjTranspose hDA
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h3
  have hinv : (Aᴴ)⁻¹ = D := Matrix.inv_eq_right_inv h1
  have hDinv : D⁻¹ = Aᴴ := Matrix.inv_eq_right_inv hDA
  set b := B * Aᴴ with hb
  have hbh : bᴴ = b := by
    rw [hb, conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * Bᴴ * (D * Aᴴ) := by rw [hDA, Matrix.mul_one]
      _ = A * (Bᴴ * D) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h2]
      _ = A * Dᴴ * B * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = B * Aᴴ := by rw [hADh, Matrix.one_mul]
  have hnbG : InG (nU b : M2 n) := by
    unfold InG JJ nU
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_zero, conjTranspose_one, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, hbh,
      neg_add_cancel, neg_zero]
  have hdet1 : IsUnit (nU b : M2 n).det := by
    unfold nU
    rw [det_fromBlocks_zero₂₁, det_one, mul_one]
    exact isUnit_one
  have hmaG : InG (fromBlocks A 0 0 D : M2 n) := levi_inG A D h1
  have hM : (fromBlocks A 0 0 D : M2 n) * fromBlocks Dᴴ 0 0 Aᴴ = 1 := by
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hADh, hDA, fromBlocks_one]
  have hdet2 : IsUnit (fromBlocks A 0 0 D : M2 n).det := Matrix.isUnit_det_of_right_inverse hM
  refine ⟨⟨Matrix.nonsingInvUnit _ hdet1, hnbG⟩, ⟨Matrix.nonsingInvUnit _ hdet2, hmaG⟩, b, A, hbh,
    Matrix.isUnit_det_of_right_inverse hADh, rfl, ?_, ?_, ?_⟩
  · show (fromBlocks A 0 0 D : M2 n) = fromBlocks A 0 0 (Aᴴ)⁻¹
    rw [hinv]
  · apply Subtype.ext
    apply Units.ext
    show mR p = nU b * fromBlocks A 0 0 D
    rw [hpm]
    unfold nU
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add]
    rw [hb, Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [hp, Matrix.zero_mul, zero_add, hDinv, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hb, add_comm]

end GlobalTheory.CompanionTheory.SiegelPoint
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.roots_eq_of_distinct_valuations : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ u u' : Fin n → L, (∀ i, ordL (u i) = y i) → (∀ i, ordL (u' i) = y i) → ∏ i, (X - C (u i)) = ∏ i, (X - C (u' i)) → u = u' := by
  first | exact @GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord | exact GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord | (intros; apply GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord <;> assumption)
end
