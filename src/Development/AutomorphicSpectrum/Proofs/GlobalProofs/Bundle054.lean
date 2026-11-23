module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralSelfDualEqAdelicFourier
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import GroundTheory.AutomorphicForms.Bundle012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle018

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.DilU

open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Dil

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulHomeo (t : R) (ht : IsUnit t) : R ≃ₜ R where
  toFun y := t * y
  invFun y := (ht.unit⁻¹ : Rˣ) * y
  left_inv y := by
    change ((ht.unit⁻¹ : Rˣ) : R) * (t * y) = y
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  right_inv y := by
    change t * (((ht.unit⁻¹ : Rˣ) : R) * y) = y
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def mulPiU (ι : Type) (t : R) (ht : IsUnit t) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ => (mulHomeo R t ht).toMeasurableEquiv

theorem map_mulPiU {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (t : R) (ht : IsUnit t)
    (c : ℝ≥0) (h : lam.map (fun y => t * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPiU R ι t ht) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => t * y) (continuous_const.mul continuous_id).measurable c h

omit [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
  [T2Space R] [MeasurableSpace R] [BorelSpace R] in
theorem half_trace_tmul (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (s : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s := by
  have e : s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← (map_ofNat (algebraMap F R) 2), ← map_mul]
    norm_num
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hc : Fintype.card (Fin (Module.finrank F E)) = 2 := by
    rw [Fintype.card_fin, hσ.2.2.1]
  rw [e, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R (Module.finBasis F E)), hc,
    two_nsmul, ← two_mul, ← mul_assoc, h2, one_mul]

theorem coordHerm_map_unit (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] (t : R) (ht : IsUnit t) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) (τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1 → HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j) :
    (coordHerm R σ b lam 1).map τ = c • coordHerm R σ b lam 1 := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam ‹_›
  haveI := hK
  haveI := hH 1
  set φ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1 → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun S => ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
    with hφ
  set Q : Measure ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) := Measure.pi fun _ => coordK R b lam with hQ
  set P := (Measure.pi fun _ : Fin 1 => lam).prod Q with hP
  have hν : coordHerm R σ b lam 1 = Measure.comap φ P := rfl
  have hemp : ∀ p : {p : Fin 1 × Fin 1 // p.1 < p.2}, False := fun p =>
    absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)
  have hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P := by
    by_contra hc
    have h0 : coordHerm R σ b lam 1 = 0 := by
      rw [hν, Measure.comap, dite_eq_right hc]
    have := isOpen_univ.measure_pos (coordHerm R σ b lam 1) Set.univ_nonempty
    simp [h0] at this
  have hs : Function.Surjective φ := by
    rintro ⟨y, w⟩
    refine ⟨hermScal R σ (y 0), Prod.ext ?_ ?_⟩
    · funext i
      rw [Subsingleton.elim i 0]
      exact half_trace_tmul R σ hσ (y 0)
    · funext p
      exact (hemp p).elim
  have hD : P.map ((mulPiU R (Fin 1) t ht).prodCongr (MeasurableEquiv.refl _)) = c • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin 1 => lam) Q (mulPiU R (Fin 1) t ht).measurable
      (measurable_id)
    rw [map_mulPiU R lam t ht c h, Measure.map_id] at e
    simp only [Fintype.card_fin, pow_one] at e
    rw [Measure.prod_smul_left] at e
    exact e.symm
  rw [hν]
  refine map_comap_scale φ P τ hτm _ c hs hcond.1 hcond.2 ?_ hD
  intro S
  refine Prod.ext ?_ ?_
  · funext i
    change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _ =
      t * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _)
    rw [hτ, ← Algebra.smul_def t, map_smul, smul_eq_mul]
    ring
  · funext p
    exact (hemp p).elim

end H

theorem coordHerm_map_ainf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → ∀ τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1, Measurable τ → (∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1).map τ = c • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1 := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam t ht c h τ hτm hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact coordHerm_map_unit (Ainf F) σ hσ b lam t ht c h τ hτm hτ

end GlobalTheory.CompanionTheory.SW.DilU
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

section U
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulPiU (ι : Type) (u : Rˣ) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := Units.mulLeft u
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem mulPiU_apply (ι : Type) (u : Rˣ) (x : ι → R) (i : ι) :
    mulPiU R ι u x i = (u : R) * x i := rfl

theorem map_mulPiU {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPiU R ι u) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => (u : R) * y) (continuous_const.mul continuous_id).measurable c h

theorem coordK_map_unit (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (GlobalTheory.CompanionTheory.SW.coordK R b lam).map (fun y => algebraMap R (R ⊗[F] E) (u : R) * y) =
      (c ^ d) • GlobalTheory.CompanionTheory.SW.coordK R b lam := by
  obtain ⟨hr, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hb := hh d b
  have hemb : MeasurableEmbedding (fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k) :=
    hb.homeomorph.toMeasurableEquiv.measurableEmbedding
  have := map_mulPiU (ι := Fin d) R lam u c h
  rw [Fintype.card_fin] at this
  refine map_comap_scale _ _ _ ?_ (mulPiU R (Fin d) u) _ hb.surjective hb.injective
    (fun s hs => (hemb.measurableSet_image' hs).nullMeasurableSet) ?_ this
  · exact (continuous_const.mul continuous_id).measurable
  · intro y
    funext k
    rw [mulPiU_apply, ← Algebra.smul_def, map_smul]
    rfl

end U

theorem coordW_map_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) = (c ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M := by
  intro F E _ _ _ _ _ σ hσ M d b lam hlam t ht c h
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  obtain ⟨u, rfl⟩ := ht
  set f : Ainf F ⊗[F] E → Ainf F ⊗[F] E := fun y => algebraMap (Ainf F) (Ainf F ⊗[F] E) (u : Ainf F) * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := coordK_map_unit (Ainf F) σ hσ b lam u c h
  have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) f hfm _ hk
  have hk2 := pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one, ← pow_mul] at hk2
  exact hk2

end GlobalTheory.CompanionTheory.SW.Dil
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord GroundTheory.Automorphic.GJMatrix
open scoped NNReal

theorem continuous_integrable_of_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Continuous Φ ∧ Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M dx hdx Φ hΦ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor 1 M
  have hf := (isSchwartzBruhat_iff b Φ).1 hΦ
  let e := crd (AF F) b M
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  have hcont : Continuous Φ := by
    have h : Continuous ((Φ ∘ e.symm) ∘ e) :=
      (continuous_of_mem_schwartzBruhatPi hf).comp e.continuous
    rwa [hcomp] at h
  refine ⟨hcont, ?_⟩
  haveI : LocallyCompactSpace (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.secondCountableTopology
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, dx = c • mu0 e := ⟨_, Measure.isAddLeftInvariant_eq_smul dx (mu0 e)⟩
  have hI : Integrable Φ (mu0 e) := by
    rw [mu0, (measurableEmbedding_symm e).integrable_map_iff]
    exact integrable_of_mem_schwartzBruhatPi hf
  rw [hc]
  exact hI.smul_measure_nnreal

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Topology

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport

section Group

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem invariant_mem_nhds {f : V → ℂ} (h1 : IsLocallyConstant f) (h2 : HasCompactSupport f) :
    {u : V | ∀ x, f (x + u) = f x} ∈ 𝓝 (0 : V) := by
  have hg : IsLocallyConstant fun p : V × V => f (p.1 + p.2) - f p.1 :=
    (h1.comp_continuous (f := fun p : V × V => p.1 + p.2) (by fun_prop)).sub
      (h1.comp_continuous (f := fun p : V × V => p.1) (by fun_prop))
  have hn := hg.isOpen_fiber 0
  obtain ⟨u, v, _, hv, hCu, h0, huv⟩ := generalized_tube_lemma h2.isCompact
    (isCompact_singleton (x := (0 : V))) hn (by
      rintro ⟨c, x⟩ ⟨_, hx⟩
      have hx' : x = 0 := hx
      subst hx'
      simp)
  have hv0 : v ∈ 𝓝 (0 : V) := hv.mem_nhds (h0 rfl)
  have hv1 : (fun x : V => -x) ⁻¹' v ∈ 𝓝 (0 : V) := by
    have hc : ContinuousAt (fun x : V => -x) 0 := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hv0)
  refine Filter.mem_of_superset (Filter.inter_mem hv0 hv1) fun w hw x => ?_
  by_cases hx : x ∈ tsupport f
  · have := huv (Set.mk_mem_prod (hCu hx) hw.1)
    simpa [sub_eq_zero] using this
  · by_cases hx' : x + w ∈ tsupport f
    · have h : f (x + w + -w) - f (x + w) = 0 := huv (Set.mk_mem_prod (hCu hx') hw.2)
      rw [add_neg_cancel_right, sub_eq_zero] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem eq_sum_cosets {φ : V → ℂ} (hφ : HasCompactSupport φ) (L : AddSubgroup V) (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) :
    ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x := by
  classical
  obtain ⟨t, ht⟩ := hφ.isCompact.elim_finite_subcover (fun a : V => {y | y - a ∈ L})
    (fun a => hL.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [L.zero_mem]⟩)
  let T : Finset (V ⧸ L) := t.image (QuotientAddGroup.mk : V → V ⧸ L)
  refine ⟨T.image Quotient.out, fun x => ?_⟩
  rw [Finset.sum_image (fun a _ b _ hab => Quotient.out_injective hab)]
  have key : ∀ q : V ⧸ L, x - q.out ∈ L ↔ q = (x : V ⧸ L) := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
  have hval : φ ((x : V ⧸ L).out) = φ x := by
    have hm : x - ((x : V ⧸ L)).out ∈ L := (key _).2 rfl
    have := hinv ((x : V ⧸ L)).out _ hm
    rw [← this]
    congr 1
    abel
  have hterm : ∀ q : V ⧸ L, φ q.out * Set.indicator {y | y - q.out ∈ L} (fun _ => (1 : ℂ)) x
      = if q = (x : V ⧸ L) then φ x else 0 := by
    intro q
    by_cases hq : q = (x : V ⧸ L)
    · subst hq
      rw [if_pos rfl, Set.indicator_of_mem (show x ∈ {y | y - ((x : V ⧸ L)).out ∈ L} from (key _).2 rfl),
        hval, mul_one]
    · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {y | y - q.out ∈ L} from fun hx => hq ((key _).1 hx)),
        mul_zero]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ hne
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hx
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hxa

end Group

theorem exists_nhds_of_pi {ι X : Type} [Finite ι] [TopologicalSpace X] {x : X} {U : Set (ι → X)}
    (hU : U ∈ 𝓝 (fun _ => x)) : ∃ W ∈ 𝓝 x, ∀ c : ι → X, (∀ i, c i ∈ W) → c ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  exact ⟨⋂ i ∈ I, t i, (Filter.biInter_mem hI).2 fun i _ => ht i, fun c hc =>
    hsub fun i hi => Set.mem_iInter₂.1 (hc i) i hi⟩

variable {F : Type} [Field F] [NumberField F]

def intSub (v : HeightOneSpectrum (𝓞 F)) : OpenAddSubgroup (Fv F v) :=
  ⟨(v.adicCompletionIntegers F).toSubring.toAddSubgroup, ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v⟩

theorem mem_intSub (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    x ∈ intSub v ↔ x ∈ v.adicCompletionIntegers F := Iff.rfl

theorem exists_box_subset {W : Set (Af F)} (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (P : ∀ v : HeightOneSpectrum (𝓞 F), OpenAddSubgroup (Fv F v)),
      (∀ v, P v ≤ intSub v) ∧ (∀ v, v ∉ T → P v = intSub v) ∧ {y : Af F | ∀ v, y v ∈ P v} ⊆ W := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hc : Continuous (RestrictedProduct.structureMap R A Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' W ∈ 𝓝 (fun v => (0 : A v)) :=
    hc.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi] at hp
  obtain ⟨I, hI, t, ht, hsub⟩ := hp
  have hQ : ∀ v : HeightOneSpectrum (𝓞 F), ∃ Q : OpenAddSubgroup (Fv F v), Q ≤ intSub v ∧
      ∀ x : A v, (x : Fv F v) ∈ Q → x ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := mem_nhds_subtype _ _ _ |>.1 (ht v)
    have h0 : u ∩ (intSub v : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) :=
      Filter.inter_mem hu ((intSub v).isOpen.mem_nhds (intSub v).zero_mem)
    obtain ⟨Q, hQ⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    exact ⟨Q, fun x hx => (hQ hx).2, fun x hx => hut (hQ hx).1⟩
  choose Q hQ1 hQ2 using hQ
  refine ⟨hI.toFinset, fun v => if v ∈ I then Q v else intSub v, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ I
    · simpa [hv] using hQ1 v
    · simp [hv]
  · intro v hv
    have : v ∉ I := by simpa using hv
    simp [this]
  · intro y hy
    have hint : ∀ v, y v ∈ A v := by
      intro v
      by_cases hv : v ∈ I
      · have := hy v
        simp only [hv, if_true] at this
        exact hQ1 v this
      · have := hy v
        simp only [hv, if_false] at this
        exact this
    have : (fun v => (⟨y v, hint v⟩ : A v)) ∈ (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' W := by
      refine hsub fun v hv => hQ2 v _ ?_
      have := hy v
      simp only [hv, if_true] at this
      exact this
    exact this

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem crd_add {R : Type} [CommRing R] [Algebra F R] (x y : R ⊗[F] E) (k : Fin d) :
    crd b R (x + y) k = crd b R x k + crd b R y k := by
  simp [crd]

theorem crd_neg {R : Type} [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin d) :
    crd b R (-x) k = - crd b R x k := by
  simp [crd]

theorem crd_zero {R : Type} [CommRing R] [Algebra F R] (k : Fin d) :
    crd b R (0 : R ⊗[F] E) k = 0 := by
  simp [crd]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

open Dec

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxF {M : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin 1 → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def intF (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Af F) :=
  {y | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

def boxA (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (Af F) :=
  {y | (∀ v ∈ S, y v ∈ U v) ∧ ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

def testT (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : ℂ :=
  (ρ (fstA F y) : ℂ) * (boxA S U).indicator (fun _ => (1 : ℂ)) (sndA F y)

def fouA (ψ : AddChar (AF F) ℂ) (db : Measure (AF F)) (T : AF F → ℂ) (b : AF F) : ℂ :=
  ∫ y, T y * ψ (y * b) ∂db

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end
