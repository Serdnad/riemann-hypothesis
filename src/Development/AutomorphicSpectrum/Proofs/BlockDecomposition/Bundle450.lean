module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarMeasureNonunitsNull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle401
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree

theorem linearIndependent_of_isUnit_qR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (R : Type) [Field R] [Algebra F R] (X : Fin 1 → Fin M → R ⊗[F] E)
    (hu : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))) : LinearIndependent (R ⊗[F] E) X := by
  classical
  have hfix : HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0) :=
    GlobalTheory.CompanionTheory.SW.FibreRatio.sigR_hR_self R hσ hJ (X 0)
  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.SW.FibreRatio.fixed_tmul R hσ _ hfix
  have hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = r := by
    unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR
    rw [hr]
    exact GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul R hσ r
  have hr0 : r ≠ 0 := by
    rw [← hq]
    exact hu.ne_zero
  have hunit : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0)) := by
    rw [hr]
    exact GlobalTheory.CompanionTheory.SW.FibreRatio.isUnit_tmul R hr0
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  set a := g 0 with ha_def
  have ha' : a • X 0 = 0 := by simpa [Fin.sum_univ_one] using hg
  have hlin : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (a • X 0) =
      a * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (X 0) := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hzero : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J (X 0) (0 : Fin M → R ⊗[F] E) = 0 := by
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [ha', hzero] at hlin
  exact (hunit.mul_left_eq_zero).1 hlin.symm

theorem null_nonfree : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → coordW (Fv F v) b lam 1 M {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}ᶜ = 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lam hlam
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hh := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  have h0 := (NullV.null_nonunits F E σ hσ M J hJ hM v (coordW (Fv F v) b lam 1 M) lam (hh.2.1 1 M) hlam.1).2
  refine measure_mono_null ?_ h0
  intro X hX hu
  exact hX (linearIndependent_of_isUnit_qR hσ hJ (Fv F v) X hu)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl Formalism.L2.Host

namespace GlobalTheory.CompanionTheory.CuspTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def conjChi (a : ℕ) (χ : HChar E) : Module.End ℂ (Sm E a) ≃ₐ[ℂ] Module.End ℂ (Sm E a) :=
  LinearEquiv.conjAlgEquiv ℂ (mulChi a χ)

theorem conjChi_apply (χ : HChar E) (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjChi a χ z (mulChi a χ φ) = mulChi a χ (z φ) := by
  simp [conjChi, LinearEquiv.conjAlgEquiv_apply]

theorem conjChi_cap (χ : HChar E) (τ : E →+* ℂ) (u : ℂ) :
    conjChi a χ (cap τ (u + expo χ τ)) = cap τ u := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨φ, rfl⟩ := (mulChi a χ).surjective ψ
  rw [conjChi_apply, cap_mulChi]

theorem map_Zalg (χ : HChar E) : (Zalg E a).map (conjChi a χ : _ →ₐ[ℂ] _) = Zalg E a := by
  rw [Zalg, AlgHom.map_adjoin]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨τ, u, rfl⟩, rfl⟩
    exact ⟨τ, u - expo χ τ, by
      have := conjChi_cap (a := a) χ τ (u - expo χ τ)
      rw [sub_add_cancel] at this
      exact this⟩
  · rintro ⟨τ, u, rfl⟩
    exact ⟨_, ⟨τ, u + expo χ τ, rfl⟩, conjChi_cap χ τ u⟩

theorem cofin_conj (χ : HChar E) {J : Set (Module.End ℂ (Sm E a))} (hJ : Cofin J) :
    Cofin (conjChi a χ '' J) := by
  obtain ⟨hsub, V, hV, hz⟩ := hJ
  have hm : ∀ z ∈ Zalg E a, conjChi a χ z ∈ Zalg E a := fun z h => by
    rw [← map_Zalg (a := a) χ]
    exact ⟨z, h, rfl⟩
  refine ⟨?_, V.map (conjChi a χ).toLinearMap, inferInstance, fun z h => ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact hm _ (hsub hj)
  · rw [← map_Zalg (a := a) χ] at h
    obtain ⟨w, hw, rfl⟩ := h
    have h1 := Submodule.mem_map_of_mem (f := (conjChi a χ).toLinearMap) (hz w hw)
    rw [Submodule.map_sup, Submodule.map_span] at h1
    obtain ⟨y, hy, y', hy', e⟩ := Submodule.mem_sup.1 h1
    refine Submodule.mem_sup.2 ⟨y, hy, y', Submodule.span_mono ?_ hy', e⟩
    rintro _ ⟨_, ⟨x, hx, j, hj, rfl⟩, rfl⟩
    exact ⟨conjChi a χ x, hm _ hx, conjChi a χ j, ⟨j, hj, rfl⟩, map_mul (conjChi a χ) x j⟩

theorem chiDet_absC_cpt (s : ℂ) (k : Kinf E a) :
    chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) = 1 := by
  have h1 : chiDet a (Model.absC E s) (infGL E a (Unitary.toUnits k)) =
      (Model.absC E s).1 (infId E (Matrix.GeneralLinearGroup.det (Unitary.toUnits k))) :=
    congrArg (Model.absC E s).1 (det_infGL _)
  rw [h1]
  refine Units.ext ?_
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E _)) = 1
  rw [Model.logNorm_infId]
  have hd : star (k.1.det) * k.1.det = 1 := (Matrix.det_of_mem_unitary k.2).1
  have hn : ∀ w, ‖(k.1.det : Cinf E) w‖ = 1 := fun w => by
    have := congrFun hd w
    have h2 : ‖(k.1.det : Cinf E) w‖ * ‖(k.1.det : Cinf E) w‖ = 1 := by
      have h3 := congrArg norm this
      simpa using h3
    nlinarith [norm_nonneg ((k.1.det : Cinf E) w)]
  have e : ∀ w, ‖((Matrix.GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) w‖ = 1 := hn
  simp [hn]

theorem dchi_absC_trace (s : ℂ) :
    dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = s * (a * (2 * Fintype.card (InfinitePlace E))) := by
  have e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E) := by
    change Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _
    simp
  rw [e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one]
  simp
  ring

theorem twist_central : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ c : ℂ,
    ∃ (χ : Formalism.L2.Host.HChar E) (L' : Subgroup (GL (Fin a) (Af E))) (J' : Set (Module.End ℂ (Sm E a))),
      IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ Cofin J' ∧ ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 →
        lie E a (oneL E a) φ = c • φ →
        mulChi a χ φ ∈ genSpace L' ρ J' ∧ IsCuspidal (mulChi a χ φ).1 ∧ lie E a (oneL E a) (mulChi a χ φ) = 0 := by
  intro E _ _ _ a ha L hL W _ _ _ ρ _ J hJ c
  have hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set s : ℂ := -c / (a * (2 * Fintype.card (InfinitePlace E))) with hs
  have hd : dchi (Model.absC E s) (Matrix.of (oneL E a)).trace = -c := by
    rw [dchi_absC_trace, hs]
    field_simp
  refine ⟨Model.absC E s, L ⊓ GlobalTheory.Published.AutFinGL.Model.kerL a (Model.absC E s), conjChi a (Model.absC E s) '' J,
    ?_, cofin_conj _ hJ, fun φ hφ hc he => ⟨⟨(IsCuspForm.mulChi (⟨hφ.1, hc⟩ : IsCuspForm φ) _).1, fun k hk => ?_, fun g => ?_, ?_⟩, ?_, ?_⟩⟩
  · exact hL.inter (GlobalTheory.Published.AutFinGL.Model.isOpen_kerL _)
  · have h2 : chiDet a (Model.absC E s) (finGL E a k) = 1 := hk.2
    change rt E a (finGL E a k) _ = _
    rw [rt_mulChi, h2, Units.val_one, one_smul]
    exact congrArg (mulChi a (Model.absC E s)) (hφ.2.1 k hk.1)
  · have h3 := hφ.2.2.1 g
    have e : (fun k : Kinf E a => (cptRep E a k (mulChi a (Model.absC E s) φ)).1 g) =
        ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) • fun k : Kinf E a => (cptRep E a k φ).1 g := by
      funext k
      change (mulChi a (Model.absC E s) φ).1 (g * infGL E a (Unitary.toUnits k)) =
        ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) * φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mulChi_apply, map_mul, chiDet_absC_cpt, mul_one, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ _ h3
  · rintro _ ⟨j, hj, rfl⟩
    rw [conjChi_apply, hφ.2.2.2 j hj, map_zero]
  · exact (IsCuspForm.mulChi (⟨hφ.1, hc⟩ : IsCuspForm φ) _).2
  · rw [lie_mulChi, he, hd, neg_smul, add_neg_cancel, map_zero]

end GlobalTheory.CompanionTheory.CuspTwist

end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.IrredMod

theorem exists_finiteDimensional_zalg_lie_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (W : Submodule ℂ (Sm E a)), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ) → ∀ φ ∈ W, ∃ Y : Submodule ℂ (Sm E a),
      FiniteDimensional ℂ Y ∧ Y ≤ W ∧ φ ∈ Y ∧ (∀ z ∈ Zalg E a, ∀ y ∈ Y, z y ∈ Y) ∧
      ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ y ∈ Y, lie E a X y ∈ Y := by
  intro E _ _ _ a W hW hA φ hφ

  let S₀ : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  have hS₀fd : FiniteDimensional ℂ S₀ := (hA φ hφ).kfin
  have hS₀W : S₀ ≤ W := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact hW (.cpt k) φ hφ)
  have hS₀K : ∀ k, ∀ ψ ∈ S₀, cptRep E a k ψ ∈ S₀ := by
    intro k ψ hψ
    have hle : S₀ ≤ S₀.comap (cptRep E a k) := Submodule.span_le.2 (by
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      simp only [map_mul, Module.End.mul_apply])
    exact hle hψ
  have hS₀L : ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ ψ ∈ S₀, lie E a X ψ ∈ S₀ :=
    fun X hX ψ hψ => GlobalTheory.T.skew_hermitian_lie_preserves_stable E a S₀ hS₀fd hS₀K X hX ψ hψ
  have hφS₀ : φ ∈ S₀ := Submodule.subset_span ⟨1, by simp⟩

  let Y : Submodule ℂ (Sm E a) := Submodule.span ℂ
    (Set.image2 (fun (z : Module.End ℂ (Sm E a)) (s : Sm E a) => z s) (Zalg E a : Set (Module.End ℂ (Sm E a))) S₀)
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S₀).2 hS₀fd
  let Zs : Sm E a → Submodule ℂ (Sm E a) := fun s =>
    Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z s) '' Zalg E a)
  have hts : ∀ s ∈ t, s ∈ S₀ := fun s hs => ht ▸ Submodule.subset_span hs
  have hZfd : ∀ s : t, FiniteDimensional ℂ (Zs s.1) := fun s => (hA s.1 (hS₀W (hts s.1 s.2))).zfin
  let T : Submodule ℂ (Sm E a) := ⨆ s : t, Zs s.1
  have hTfd : FiniteDimensional ℂ T := Submodule.finiteDimensional_iSup _
  have hYT : Y ≤ T := Submodule.span_le.2 (by
    rintro _ ⟨z, hz, s, hs, rfl⟩
    have hle : S₀ ≤ T.comap z := by
      rw [← ht]
      refine Submodule.span_le.2 fun u hu => ?_
      exact Submodule.mem_iSup_of_mem (⟨u, hu⟩ : t) (Submodule.subset_span ⟨z, hz, rfl⟩)
    exact hle hs)
  have hWlie : ∀ X, ∀ ψ ∈ W, lie E a X ψ ∈ W := fun X ψ hψ => hW (.lie X) ψ hψ
  refine ⟨Y, Submodule.finiteDimensional_of_le hYT, Submodule.span_le.2 ?_, Submodule.subset_span
    ⟨1, (Zalg E a).one_mem, φ, hφS₀, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, s, hs, rfl⟩
    exact Zalg_stable hWlie hz s (hS₀W hs)
  · intro z hz y hy
    have hle : Y ≤ Y.comap z := Submodule.span_le.2 (by
      rintro _ ⟨z', hz', s, hs, rfl⟩
      exact Submodule.subset_span ⟨z * z', (Zalg E a).mul_mem hz hz', s, hs, rfl⟩)
    exact hle hy
  · intro X hX y hy
    have hle : Y ≤ Y.comap (lie E a X) := Submodule.span_le.2 (by
      rintro _ ⟨z, hz, s, hs, rfl⟩
      have e : lie E a X (z s) = z (lie E a X s) :=
        (LinearMap.congr_fun (GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie E a z hz X) s).symm
      change lie E a X (z s) ∈ Y
      rw [e]
      exact Submodule.subset_span ⟨z, hz, _, hS₀L X hX s hs, rfl⟩)
    exact hle hy

end GlobalTheory.CompanionTheory.IrredMod
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

open Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MixZ

theorem isPotential_pullback_locPot : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → IsPotential A (φ.locPot.pullback F hF) := by
  intro k _ X q σ D T _ A F hF hol B φ hφ
  refine ⟨fun x j v hv => ?_, fun x x' y hy => ?_⟩
  · have hv1 : v ∈ (A.chart j).target := hv.1
    have hv2 : F ((A.chart j).symm v) ∈ ptsIn q σ (B.U (pick φ.isLB (F x))) := hv.2
    obtain ⟨W, ι, _, g, Fn, O, h₁, h₂, h₃, h₄, h₅⟩ := hφ _ _ hv2
    have hcs : ContinuousAt (fun w => F ((A.chart j).symm w)) v :=
      hF.continuousAt.comp ((A.chart j).continuousAt_symm hv1)
    have hop : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ W)) :=
      (A.chart j).isOpen_inter_preimage_symm ((isOpen_ptsIn W).preimage hF)
    have hg : ContDiffAt ℝ ∞ (fun w a => ev q σ W (g a) (F ((A.chart j).symm w))) v :=
      contDiffAt_pi.2 fun a =>
        ((hol W (g a) j v ⟨hv1, h₁⟩).restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top
    have hc : ContDiffAt ℝ ∞ (fun w => Fn fun a => ev q σ W (g a) (F ((A.chart j).symm w))) v :=
      (h₄.contDiffAt (h₂.mem_nhds h₃)).comp v hg
    have hc' : ContDiffAt ℝ ∞ (fun w => φ.φ (pick φ.isLB (F x)) (F ((A.chart j).symm w))) v :=
      hc.congr_of_eventuallyEq (hcs.eventually h₅)
    exact (hc'.div_const 2).contDiffWithinAt
  · set i := pick φ.isLB (F x) with hi
    set i' := pick φ.isLB (F x') with hi'
    have hyi : F y ∈ ptsIn q σ (B.U i) := hy.1
    have hyi' : F y ∈ ptsIn q σ (B.U i') := hy.2
    set S : Set T := F ⁻¹' ptsIn q σ (B.U i ⊓ B.U i') with hS
    have hSo : IsOpen S := (isOpen_ptsIn _).preimage hF
    have hyS : y ∈ S := mem_ptsIn_inf.2 ⟨hyi, hyi'⟩
    set g : T → ℂ := ev q σ (B.U i ⊓ B.U i') (B.g i i').val ∘ F with hg
    have hgh : A.HoloOn S g := hol _ _
    have hgc : ContinuousOn g S :=
      (continuousOn_ev (B.g i i').val).comp hF.continuousOn fun _ h => h
    have h0 : g y ≠ 0 := gv_ne_zero hyi hyi'
    refine ⟨S ∩ (fun z => g z * (g y)⁻¹) ⁻¹' Complex.slitPlane,
      (hgc.mul continuousOn_const).isOpen_inter_preimage hSo Complex.isOpen_slitPlane,
      ⟨hyS, ?_⟩, fun z => Complex.log (g z * (g y)⁻¹) + (Real.log ‖g y‖ : ℂ),
      fun j v hv => ?_, fun z hz => ?_⟩
    · simp [mul_inv_cancel₀ h0]
    · have ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v := hgh j v ⟨hv.1, hv.2.1⟩
      exact ((ha.mul analyticAt_const).clog hv.2.2).add analyticAt_const
    · have hzS : F z ∈ ptsIn q σ (B.U i ⊓ B.U i') := hz.1.1.1
      have hz0 : g z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.1.1.2)
      have e := φ.half_eq (mem_ptsIn_inf.1 hzS).1 (mem_ptsIn_inf.1 hzS).2
      have e' : Real.log ‖gv q σ B i i' (F z)‖ = Real.log ‖g z‖ := rfl
      change φ.φ i (F z) / 2 - φ.φ i' (F z) / 2 = _
      rw [e, e', Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
        Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel,
        add_sub_cancel_left]

end GlobalTheory.CompanionTheory.MixZ
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.PullDens


open Filter _root_.Topology in
theorem locDens_pullback_eq : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (c : GlobalTheory.AlgChart q σ D) (j : Fin A.n) (u : Fin D → ℂ),
      u ∈ (A.chart j).target → F ((A.chart j).symm u) ∈ c.e.source →
      AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u ∧
      locDens A (fun _ => φ.locPot.pullback F hF) j u =
        ‖LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (F ((A.chart j).symm u)) := by
  intro k _ X q σ D T _ A F hF hH B φ h c j u hu hsrc
  have hcont : ContinuousAt (F ∘ (A.chart j).symm) u :=
    hF.continuousAt.comp ((A.chart j).continuousAt_symm hu)
  have hN : ∀ᶠ w in 𝓝 u, F ((A.chart j).symm w) ∈ c.e.source :=
    hcont.eventually (c.e.open_source.mem_nhds hsrc)
  have hG : AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u := by
    refine analyticAt_pi_iff.2 fun a => ?_
    refine (hH c.U (c.x a) j u ⟨hu, c.source_subset hsrc⟩).congr ?_
    filter_upwards [hN] with w hw
    exact (c.finChart_eq_ev hw a).symm
  refine ⟨hG, ?_⟩
  set G := c.finChart ∘ F ∘ (A.chart j).symm with hGdef
  set y₀ := F ((A.chart j).symm u) with hy₀
  have hGu : G u = c.finChart y₀ := rfl
  have hsy : c.finChart.symm (G u) = y₀ := c.finChart.left_inv hsrc
  have hz : G u ∈ c.finChart.target := c.finChart.map_source hsrc
  have hma := h.maDens_eq c hz
  rw [hsy] at hma
  have hr : c.e y₀ = GlobalTheory.FinChart.toV D (G u) := rfl
  have hd := h.contDiffAt c hsrc (mem_pick φ.isLB y₀)
  rw [hr] at hd
  have hψ : ContDiffAt ℝ 2 (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) (G u) :=
    (hd.comp (G u) (GlobalTheory.FinChart.toV D).contDiff.contDiffAt).div_const 2
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ w => φ.locPot.φ y₀ (c.finChart.symm w)) G u hG
    (fun _ => hψ)
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hma] at hcomp
  rw [mul_comm, ← hcomp]
  unfold locDens
  refine maDens_congr_hessC _ _ _ fun _ => hessCGerm _ _ _ ?_
  filter_upwards [hN] with w hw
  simp only [LocPot.pullback, Function.comp_apply, hGdef]
  rw [c.finChart.left_inv hw]

end GlobalTheory.CompanionTheory.MixZ.PullDens
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.GenericCoords

theorem exists_etale_coords_int : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), GlobalTheory.IsArithVar p D →
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x).Etale :=
  fun _ _ _ _ h => GlobalTheory.GenericEtale.exists_etale_coords h

end GlobalTheory.CompanionTheory.MixZ.GenericCoords
end
