module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle194
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitude
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle185
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BaseSimil

open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def g1 (x : E) (hx : x ≠ 0) : GL (Fin 1) E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => x) (by rw [Matrix.det_fin_one]; exact hx)

theorem scalar_matrix_apply (x : E) (hx : x ≠ 0) (i j : Fin 1) :
    ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) i j = x := rfl

theorem tuple_action_scalar_eq_mul (R : Type) [CommRing R] [Algebra F R] (x : E) (hx : x ≠ 0) :
    actTup R (bc (inclR R) (g1 x hx)) =
      fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => inclR R x * X a i := by
  funext X a i
  have hi : ∀ j : Fin 1, j = i := fun j => Subsingleton.elim _ _
  have h1 : ((bc (inclR R) (g1 x hx) : GL (Fin 1) (R ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i 0 = inclR R x := rfl
  change ∑ j, ((bc (inclR R) (g1 x hx) : GL (Fin 1) (R ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j * X a j = _
  rw [Fin.sum_univ_one, h1, Subsingleton.elim i 0]

end Alg

theorem map_fib (hS : Scal) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Nontrivial R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hL : IsLocR R) (μ : Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (ν : Measure (HermR R σ 1))
    (m : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hm : IsGramFib R σ J 1 μ ν m) (x : E) (hx : x ≠ 0) (l β : F) (hl : σ x * x = algebraMap F E l) (hβ : β ≠ 0) :
    (m (hermScal R σ (algebraMap F R β))).map (actTup R (bc (inclR R) (g1 x hx))) =
      m (hermScal R σ (algebraMap F R (l * β))) := by
  have hn : algebraMap F R l ⊗ₜ[F] (1 : E) =
      sigR R σ ((Units.map (inclR (F := F) (E := E) R : E →* R ⊗[F] E) (Units.mk0 x hx) : (R ⊗[F] E)ˣ) : R ⊗[F] E) *
        ((Units.map (inclR (F := F) (E := E) R : E →* R ⊗[F] E) (Units.mk0 x hx) : (R ⊗[F] E)ˣ) : R ⊗[F] E) := by
    change _ = sigR R σ (inclR R x) * inclR R x
    have h1 : sigR R σ (inclR R x) = inclR R (σ x) := by simp [sigR, inclR]
    rw [h1, ← map_mul, hl]
    have := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
    change _ = (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) (algebraMap F E l)
    rw [this]
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hu : IsUnit (algebraMap F R β) := (IsUnit.mk0 _ hβ).map _
  have := hS F E σ hcm J hJ R hL μ ν m hμ hν hm _ _ _ hn hu
  rw [tuple_action_scalar_eq_mul, map_mul]
  exact this

theorem hermitian_similitude_scalar {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E)
    (x : E) (hx : x ≠ 0) (l : F) (hl : σ x * x = algebraMap F E l) :
    cT (σ : E →+* E) ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) * J *
        ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) = (algebraMap F E l) • J := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul, cT, Matrix.transpose_apply,
    Matrix.map_apply, scalar_matrix_apply]
  rw [← hl]
  change σ x * J 0 0 * x = σ x * x * J 0 0
  ring

theorem exists_norm {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (β β' : F) (hβ : β ≠ 0)
    (hs : (sph σ J β).Nonempty) (hs' : (sph σ J β').Nonempty) (hβ' : β' ≠ 0) :
    ∃ x : E, x ≠ 0 ∧ σ x * x = algebraMap F E (β' / β) := by
  obtain ⟨X, hX⟩ := hs
  obtain ⟨Y, hY⟩ := hs'
  have hJ0 : J 0 0 ≠ 0 := by
    have := hJ.2
    rwa [Matrix.det_fin_one] at this
  have e : ∀ (Z : Fin 1 → Fin 1 → E) (t : F), Z ∈ sph σ J t → σ (Z 0 0) * J 0 0 * Z 0 0 = algebraMap F E t := by
    intro Z t hZ
    have h0 := congrFun (congrFun hZ 0) 0
    simpa [gramE, hE, hform] using h0
  have eX := e X β hX
  have eY := e Y β' hY
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hx : X 0 0 ≠ 0 := by
    intro h
    rw [h] at eX
    exact hb (by simpa using eX.symm)
  have hsx : σ (X 0 0) ≠ 0 := by simpa using hx
  refine ⟨Y 0 0 / X 0 0, ?_, ?_⟩
  · refine div_ne_zero ?_ hx
    intro h
    rw [h] at eY
    exact (by simpa using hβ' : algebraMap F E β' ≠ 0) (by simpa using eY.symm)
  · rw [map_div₀, map_div₀, ← eX, ← eY]
    field_simp

theorem simil : Scal → Simil := by
  intro hScal F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β β' hβ hβ' hs hs' c hc
  have hl0 : β' / β ≠ 0 := div_ne_zero hβ' hβ
  obtain ⟨x, hx, hxl⟩ := exists_norm σ J hJ β β' hβ hs hs' hβ'
  have hγ := hermitian_similitude_scalar σ J x hx (β' / β) hxl
  obtain ⟨μ', 𝓕', hμ', h𝓕', hth⟩ := GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 (g1 x hx) (β' / β) hl0 hγ
  have hT : (fun _ _ => algebraMap F E β' : Matrix (Fin 1) (Fin 1) E) =
      (algebraMap F E (β' / β)) • (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) := by
    funext a b'
    change algebraMap F E β' = algebraMap F E (β' / β) * algebraMap F E β
    rw [← map_mul, div_mul_cancel₀ _ hβ]
  have hth1 := hth 1 _ _ hT
  have hind := GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep F E σ hcm 1 J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕' 1 (fun _ _ => algebraMap F E β)
  change (thetaMeas σ J μ' 𝓕' (sph σ J β)).map _ = thetaMeas σ J μ 𝓕 (sph σ J β') at hth1
  change thetaMeas σ J μ 𝓕 (sph σ J β) = thetaMeas σ J μ' 𝓕' (sph σ J β) at hind
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := SWIsom.haar_of_loc σ hcm (Ainf F) hLi b li hli.1 1 1
  have hWv := fun v => SWIsom.haar_of_loc σ hcm (Fv F v) (hLv v) b (lam v) (hlam v).1 1 1
  have hβ'' : β' / β * β = β' := div_mul_cancel₀ _ hβ
  have sInf := map_fib hScal σ hcm J hJ (Ainf F) hLi _ _ mi hWi.1 hWi.2 hmi x hx (β' / β) β hxl hβ
  have sV := fun v => map_fib hScal σ hcm J hJ (Fv F v) (hLv v) _ _ (m v) (hWv v).1 (hWv v).2 (hm v) x hx (β' / β) β hxl hβ
  rw [hβ''] at sInf
  simp only [hβ''] at sV
  have hproj : ∀ X : Fin 1 → Fin 1 → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) (g1 x hx)) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) (g1 x hx)) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact SWIsom.map_actTup (fstA F) (g1 x hx) X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X) =
          actTup (Af F) (bc (inclR (Af F)) (g1 x hx)) (projFin X) := by
        funext a i
        exact SWIsom.map_actTup (sndA F) (g1 x hx) X a i
      rw [h1]
      funext a i
      exact SWIsom.map_actTup (evalV F v) (g1 x hx) (projFin X) a i
  have hfin : ∀ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β'))) (latV b v) < ⊤ := by
    intro v
    have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 1 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β'))).1
    have h2 := ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1).2.2.2.1 v).1.measure_lt_top
      (μ := m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top h2
  have hu : IsUnitProd (1 : ℝ≥0) (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℝ≥0)) :=
    ⟨Filter.Eventually.of_forall fun _ => rfl, by simp⟩
  have key := GlobalTheory.CompanionTheory.SW.MassSimil.euler_move_c F E σ hcm d b 1 1 (thetaMeas σ J μ' 𝓕' (sph σ J β))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β')))
    (fun v => cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β)))
    (fun v => cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)))
    (actTup (Ainf F) (bc (inclR (Ainf F)) (g1 x hx))) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) (g1 x hx)))
    (SWIsom.measurable_actTup σ hcm (AF F) _) (SWIsom.measurable_of_loc σ hcm (Ainf F) hLi _)
    (fun v => SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 1).2.1 (g1 x hx)) 1 (fun _ => 1) hu
    (by rw [sInf, one_smul]) (fun v => by
      rw [Measure.map_smul, sV v, one_smul]
      exact (SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _).aemeasurable) hfin c
  unfold EP at hc ⊢
  rw [hind] at hc
  rw [← hth1]
  exact key hc

end GlobalTheory.CompanionTheory.SW.BaseSimil
end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BaseTest

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_unit_vector (R : Type) [CommRing R] [Algebra F R] {J : Matrix (Fin 1) (Fin 1) E}
    (hJ : IsHermND σ J) : ∃ X : Fin 1 → Fin 1 → R ⊗[F] E, IsUnit (gramR R σ J X).det := by
  have hx : hE σ J (fun _ => 1) (fun _ => 1) ≠ 0 := by
    have h := hJ.2
    rw [Matrix.det_fin_one] at h
    simpa [hE, hform] using h
  refine ⟨ratTup R fun _ _ => 1, ?_⟩
  rw [Matrix.det_fin_one, GlobalTheory.CompanionTheory.SW.MassTest.gramR_ratTup_apply]
  exact (IsUnit.mk0 _ hx).map (inclR R)

end Alg

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isOpen_unit (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hloc : IsLocR R) (J : Matrix (Fin 1) (Fin 1) E) :
    IsOpen {X : Fin 1 → Fin 1 → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hu, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨-, -, -, -, -, -, -, -, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have hO : IsOpen {r : R | IsUnit r} := hu.isOpen_range
  exact (PI.VolStabS.isOpen_isUnit_det R hO 1).preimage (t10 1 1 J)

theorem exists_test_fun (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hl : lam.IsAddHaarMeasure) :
    ∃ φ : (Fin 1 → Fin 1 → R ⊗[F] E) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧
      tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det} ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 1) ≠ 0 ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 1) ≠ ⊤ := by
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
  haveI := t8 1 1
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 1
  obtain ⟨X, hX⟩ := exists_unit_vector R hJ
  exact GlobalTheory.CompanionTheory.SW.MassTest.exists_bump _ (isOpen_unit hcm R hloc J) hX

theorem exists_test_set (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    [TotallyDisconnectedSpace R] (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hl : lam.IsAddHaarMeasure) :
    ∃ A : Set (Fin 1 → Fin 1 → R ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR R σ J X).det} ∧ coordW R b lam 1 1 A ≠ 0 ∧ coordW R b lam 1 1 A ≠ ⊤ := by
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
  haveI := t8 1 1
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 1
  haveI : TotallyDisconnectedSpace (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.totallyDisconnectedSpace
  obtain ⟨X, hX⟩ := exists_unit_vector R hJ
  exact GlobalTheory.CompanionTheory.SW.MassTest.exists_compactOpen _ (isOpen_unit hcm R hloc J) hX

end Loc

theorem testEx : TestEx := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam _ _ _ _ S
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨φ, h1, h2, h3, h4, h5, h6⟩ := exists_test_fun hcm hJ (Ainf F) hLi b li hli.1
  have hA' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ A : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} ∧ coordW (Fv F v) b (lam v) 1 1 A ≠ 0 ∧
      coordW (Fv F v) b (lam v) 1 1 A ≠ ⊤ := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact exists_test_set hcm hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1
  choose A0 hc ho hs hn ht using hA'
  classical
  have hv : vol b li lam S φ (fun v => if v ∈ S then A0 v else latV b v) =
      (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 1 (A0 v) := by
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

end GlobalTheory.CompanionTheory.SW.BaseTest
end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgBase

open PositivityTheory.Rg.Base1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_tmul_one {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : AF F ⊗[F] E) :
    (Algebra.norm (AF F) x) ⊗ₜ[F] (1 : E) = sigR (AF F) σ x * x := by
  have e := GlobalTheory.Doubling.algebraMap_norm_eq h (R := AF F) x
  rw [Algebra.TensorProduct.algebraMap_apply] at e
  rw [mul_comm]
  exact e

theorem isNm_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : (AF F ⊗[F] E)ˣ) (a : (AF F)ˣ) :
    IsNm σ x a ↔ Algebra.norm (AF F) (x : AF F ⊗[F] E) = a := by
  have hinj : Function.Injective (fun r : AF F => r ⊗ₜ[F] (1 : E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  unfold IsNm
  rw [← norm_tmul_one h]
  exact ⟨fun e => (hinj e).symm, fun e => by rw [e]⟩

theorem hEx : HEx := by
  intro F E _ _ _ _ _ σ h
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  refine ⟨(GlobalTheory.IdeleNormChar.normSign (K := F) E).ker, ?_, ?_, ?_⟩
  · intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      obtain ⟨t, x, hx⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 ha
      refine ⟨t, x, a / GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t, ?_, ?_⟩
      · exact (isNm_iff h x _).2 (congrArg Units.val hx)
      · exact (mul_div_cancel (GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t) a).symm
    · rintro ⟨t, x, n, hn, rfl⟩
      have h1 : GlobalTheory.IdeleNormChar.normSign E (pr t) = 1 := GlobalTheory.IdeleNormChar.normSign_toUnits E t
      have h2 : GlobalTheory.IdeleNormChar.normSign E n = 1 :=
        GlobalTheory.IdeleNormChar.normSign_of_mem E ⟨x, Units.ext ((isNm_iff h x n).1 hn)⟩
      rw [map_mul, h1, h2, one_mul]
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.IdeleNormChar.eventually_normSign (K := F) E] with a ha
    exact ha
  · obtain ⟨b, hb⟩ := GlobalTheory.IdeleNormChar.exists_normSign_ne_one (K := F) E
    have hr : (GlobalTheory.IdeleNormChar.normSign (K := F) E).range = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨b, (Int.units_eq_one_or _).resolve_left hb⟩
    rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

end GlobalTheory.CompanionTheory.RgBase

end
end
