module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle008
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem gram_form_eq {m n : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ)
    (w : Fin n → ℂ) :
    star w ⬝ᵥ (y.conjTranspose * G * y).mulVec w = star (y.mulVec w) ⬝ᵥ G.mulVec (y.mulVec w) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem exists_posOn_of_gram (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ)
    (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ))
    (h : PosOn ε (y.conjTranspose * G * y) S) :
    ∃ T : Submodule ℂ (Fin m → ℂ), PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  have key : ∀ w ∈ S, w ≠ 0 → 0 < ε * (star (y.mulVec w) ⬝ᵥ G.mulVec (y.mulVec w)).re := by
    intro w hw hw0
    have hpos := h w hw hw0
    rwa [gram_form_eq] at hpos
  have hinj : Function.Injective ((Matrix.mulVecLin y).domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hw0 : (w : Fin n → ℂ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have h1 := key w w.2 hw0
    have h2 : y.mulVec (w : Fin n → ℂ) = 0 := by simpa using hw
    simp [h2] at h1
  refine ⟨S.map (Matrix.mulVecLin y), ?_, ?_⟩
  · intro v hv hv0
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hv0 (map_zero _)
    rw [Matrix.mulVecLin_apply]
    exact key w hw hw0
  · rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.positive_on_subspace_open : ∀ (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε Z S} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem half_trace_eq (σ : E →ₐ[F] E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = (Θ z w).re := by
  have h4 := h.2.2.2 z w
  have h5 : e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = 2 * (Θ z w).re := by
    have := congrArg Complex.re h4
    simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at this
    rw [this]; ring
  rw [map_mul, Pi.mul_apply, he, h5, map_div₀, map_one, map_ofNat]
  ring

def evC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) : Ainf F ⊗[F] E →+* ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace F => ℂ) w).comp (Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ))

theorem evC_apply (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) (z : Ainf F ⊗[F] E) :
    evC Θ w z = Θ z w := rfl

theorem coord_gramR (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    matC Θ (gramR (Ainf F) σ J X) w = gramC (J.map (τ w)) (tupC Θ X w) := by
  ext a c
  change evC Θ w (Formalism.UG.hform (sigR (Ainf F) σ) (JR (Ainf F) J) (X a) (X c)) = _

  simp only [Formalism.UG.hform, map_sum, map_mul, gramC, tupC, evC_apply, h.2.1, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show inclR (Ainf F) (J i j) = (1 : Ainf F) ⊗ₜ[F] (J i j) from rfl, h.2.2.1]

theorem coord_trace_mul (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (B G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) :
    Θ (Matrix.trace (B * G)) w = Matrix.trace (matC Θ B w * matC Θ G w) := by
  change evC Θ w _ = _

  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  rfl

theorem gramC_smul {n M : ℕ} (c : ℂ) (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    gramC (c • J) X = c • gramC J X := by
  ext a b
  simp only [gramC, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem psiInf_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ σ ρ e τ Θ h he a ψ hψ M n J B X
  change ψ (pairA F _ 0) = _
  rw [hψ]
  congr 3
  rw [phaseM]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [half_trace_eq σ ρ e τ Θ h he, coord_trace_mul, coord_gramR σ e τ Θ h, gramC_smul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp [ptCoord]

theorem isMultiProjPrime_ptIdeal (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsMultiProjPrime (ptIdeal x) :=
  ⟨RingHom.ker_isPrime _, GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal (ptCoord x),
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.relevant (ptCoord x) (ptChart x) fun k => by
      rw [ptCoord_ptChart]; exact one_ne_zero⟩

end GlobalTheory.CompanionTheory.MPDict
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Onto

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)

section Coord

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_comp_ringHom {L Ω : Type} [Field L] [Field Ω] (j : L →+* Ω) (w : (Σ k, ι k) → L) :
    Geo.mCoordIdeal (fun p => j (w p)) = Geo.mCoordIdeal w := by
  have key : ∀ f : Geo.MRing ι, Geo.mConeMap (fun p => j (w p)) f = MvPolynomial.map j (Geo.mConeMap w f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [Geo.mConeMap]
  ext f
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective j j.injective)

theorem mCoordIdeal_blockScale {Ω : Type} [Field Ω] (c : K → Ω) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → Ω) :
    Geo.mCoordIdeal (fun p : Σ k, ι k => c p.1 * z p) = Geo.mCoordIdeal z := by
  let φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k) * X k
  let φ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k)⁻¹ * X k
  have hinv : φ'.comp φ = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [φ, φ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hinj : Function.Injective φ := fun a b h => by
    have := congrArg φ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hinv] at this
  have hcomp : ∀ g, Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) g = φ (Geo.mConeMap z g) := by
    intro g
    have : Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) = (φ.restrictScalars ℤ).comp (Geo.mConeMap z) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp only [Geo.mConeMap, aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, φ, map_mul, aeval_C,
        algebraMap_eq]
      ring
    rw [this]; rfl
  ext g
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, hcomp, map_eq_zero_iff φ hinj]

theorem mCoordIdeal_of_ker {Ω : Type} [Field Ω] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (φ : Geo.MRing ι →+* Ω) (hφ : RingHom.ker φ = P) : Geo.mCoordIdeal (fun p => φ (X p)) = P := by
  have hev : ∀ f, aeval (fun p => φ (X p)) f = φ f := by
    intro f
    have : ((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω) = φ :=
      MvPolynomial.ringHom_ext
        (fun r => RingHom.congr_fun (Subsingleton.elim
          (((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω).comp C) (φ.comp C)) r)
        (fun p => by simp)
    exact congrArg (fun ψ => ψ f) this
  apply le_antisymm
  · intro f hf
    rw [Geo.mCoordIdeal, RingHom.mem_ker] at hf
    have e : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp
        (Geo.mConeMap (fun p => φ (X p))) = aeval (fun p => φ (X p)) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp [Geo.mConeMap]
    have := congrArg (fun ψ => ψ f) e
    simp only [AlgHom.comp_apply, hf, map_zero, hev] at this
    rw [← hφ, RingHom.mem_ker]
    exact this.symm
  · have hP' := hP
    obtain ⟨S, hS, hPS⟩ := hP'
    rw [hPS, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h0 : φ f = 0 := by
      rw [← RingHom.mem_ker, hφ, hPS]
      exact Ideal.subset_span hf
    rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, hev, h0, C_0, mul_zero]

end Coord

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem exists_ptIdeal_eq_mCoordIdeal {F : Type} [Field F] (v : (Σ k, Bk n k) → F)
    (hv : ∀ k, ∃ i, v ⟨k, i⟩ ≠ 0) : ∃ x : MP ℤ m n, ptIdeal x = Geo.mCoordIdeal v := by
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => v ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hv k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp F ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
  have ha : ∀ k, a k ≫ ProjSpace.toSpecBase ℤ (n k) = spMap (Int.castRingHom F) := by
    intro k
    dsimp only [a]
    rw [GlobalTheory.ProjSpace.pt, ProjSpace.toSpecBase, ProjPoint.ofHom_toSpecZero_assoc,
      ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C _ _ r
  let g : Sp F ⟶ MP ℤ m n := ProjSpace.lift m n (spMap (Int.castRingHom F)) a ha
  have hg : ∀ k, g ≫ prB n k = a k := fun k => ProjSpace.lift_pr m n _ a ha k
  let p : Sp F := IsLocalRing.closedPoint F
  let x : MP ℤ m n := g p
  let θ : F →+* (Sp F).residueField p :=
    ((Sp F).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp F).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (v ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (v ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp F).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : F, ((Sp F).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp F).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (v ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  refine ⟨x, ?_⟩
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ v,
    ← mCoordIdeal_blockScale (fun k => θ (v ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

theorem exists_ptIdeal_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Geo.MRing (Bk n)))
    (hP : Geo.IsMultiProjPrime P) : ∃ x : MP ℤ m n, ptIdeal x = P := by
  obtain ⟨hp, hh, hr⟩ := hP
  let φ : Geo.MRing (Bk n) →+* FractionRing (Geo.MRing (Bk n) ⧸ P) :=
    (algebraMap (Geo.MRing (Bk n) ⧸ P) _).comp (Ideal.Quotient.mk P)
  have hφ : RingHom.ker φ = P := by
    ext f
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff (algebraMap (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
      (IsFractionRing.injective (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
  have hv : ∀ k, ∃ i, φ (X ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [← hφ, RingHom.mem_ker]
    exact h0
  obtain ⟨x, hx⟩ := exists_ptIdeal_eq_mCoordIdeal (fun p => φ (X p)) hv
  exact ⟨x, hx.trans (mCoordIdeal_of_ker P hh φ hφ)⟩

end GlobalTheory.CompanionTheory.MPDict.Onto
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem ev_unit_inv_mul {m : ℕ} {n : Fin (m + 1) → ℕ} {U : (MP ℤ m n).Opens} (v : Γ(MP ℤ m n, U)ˣ)
    (y : CxPts (mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ U) :
    CxPts.ev (mpStr ℤ m n) σ₀ U (↑v⁻¹ : Γ(MP ℤ m n, U)) y *
      CxPts.ev (mpStr ℤ m n) σ₀ U (v : Γ(MP ℤ m n, U)) y = 1 := by
  unfold CxPts.ev ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  split_ifs with h
  · rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  · exact (h hy).elim

theorem isHermRep_dual : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep M.dual A.inv := by
  intro m n M A hA
  obtain ⟨u, h1, h2, h3⟩ := hA
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_, ?_⟩
  · rintro (i : M.B.ι) (j : M.B.ι) c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (M.B.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv, ← mul_inv]
    exact congrArg (·⁻¹) (h1 i j c)
  · rintro (i : M.B.ι) c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-A.a k)
    rw [map_inv, map_inv]
    have h := congrArg (·⁻¹) (h2 i c c')
    simp only [mul_inv, ← Finset.prod_inv_distrib, ← zpow_neg] at h
    exact h
  · rintro (i : M.B.ι) c y z hz (hyin : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    change (A.h z)⁻¹ = (∏ k, ‖z ⟨k, c k⟩‖ ^ (-A.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y‖ * Real.exp (-(M.φ σ₀).φ i y / 2)
    have e : CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)⁻¹) y =
        (CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (↑(u i c)) y)⁻¹ :=
      eq_inv_of_mul_eq_one_left (ev_unit_inv_mul (u i c) y hyin)
    rw [h3 i c y z hz hyin]
    simp only [zpow_neg, Finset.prod_inv_distrib, neg_div, Real.exp_neg, mul_inv]
    congr 2
    rw [e, norm_inv]

end GlobalTheory.CompanionTheory.MPDict
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.WittLevel

theorem isNoetherianRing_Wm_one :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l],
      IsNoetherianRing (Wc.Wm l k 1) := by
  intro l _ k _ _ _
  unfold Wc.Wm
  infer_instance

end GlobalTheory.CompanionTheory.WittLevel
end
