module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.AutomorphicForms.Reduction
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle420
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle417
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizer
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle401
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

section Gen

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def trM {R : Type} {M n : ℕ} (X : Fin n → Fin M → R) : Matrix (Fin M) (Fin n) R :=
  Matrix.of fun i a => X a i

def framesE (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) :
    Set (Fin n → Fin M → E) :=
  {X | LinearIndependent E X ∧ gramE σ J X = T}

def IsBlockM {n : ℕ} (t : ℕ) (T : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ h : t < n, (∀ i j : Fin n, (t ≤ i.1 ∨ t ≤ j.1) → T i j = 0) ∧
    (T.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0

def IsGramFibFree (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ m

end Gen

section Glob

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def SWFree (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) : Prop :=
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf →
      (∀ v, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) →
      IsEulerProd b (thetaMeas σ J μ 𝓕 (framesE σ J T)) 1 (minf (hermOf (Ainf F) σ T hT))
        (fun v => m v (hermOf (Fv F v) σ T hT))

end Glob

section D

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermE_symm {D : D7} {r : ℕ} (β : PositivityTheory.GramSchwartzFunctions.HermE D r) (a b : Fin r) :
    D.sp.cm.sig (β.1 b a) = β.1 a b := by
  have h := congrFun (congrFun β.2 a) b
  simpa [Matrix.map_apply, Matrix.transpose_apply] using h

theorem trM_mem_framesE_iff {D : D7} (V : HSp D) {r : ℕ} (X : Fin r → Fin V.rank → D.host.E)
    (T : Matrix (Fin r) (Fin r) D.host.E) :
    X ∈ framesE D.sp.cm.sig V.gram T ↔ (trM X).rank = r ∧ PositivityTheory.GramSchwartzFunctions.BC.gramQ V (trM X) = T := by
  have hg : HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = PositivityTheory.GramSchwartzFunctions.BC.gramQ V (trM X) := by
    refine Matrix.ext fun a b => ?_
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, PositivityTheory.GramSchwartzFunctions.BC.gramQ, trM,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_assoc]; rfl
  have hr : LinearIndependent D.host.E X ↔ (trM X).rank = r := by
    have h1 : (trM X).rank = (Matrix.of X).rank := by
      have : trM X = Matrix.transpose (Matrix.of X) := rfl
      rw [this, Matrix.rank_transpose]
    rw [h1, Matrix.rank_eq_finrank_span_row]
    have := linearIndependent_iff_card_eq_finrank_span (R := D.host.E) (b := X)
    refine this.trans ?_
    rw [Fintype.card_fin, eq_comm]
    exact Iff.rfl
  simp only [framesE, Set.mem_ofPred_eq, hr, hg]

end D

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) →
    ∃ s : ℂ, GlobalTheory.DiscSpec.IsNormalised (π.twist (GlobalTheory.CuspRep.Model.absC E s)) := by
  intro E _ _ _ a ha π hm
  choose m hm using hm
  have hN : (Fintype.card (E →+* ℂ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨-(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)), ?_⟩
  set s : ℂ := -(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)) with hs
  intro φ hφ t g
  have hsum : ∀ τ : E →+* ℂ, (∑ i : Fin a, Eop τ i i) φ = ((m τ).sum + a * s) • φ := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at h1
    rw [GlobalTheory.T.trace_operator_eigenvalue_sum E a _ τ _ h1 φ hφ, Multiset.sum_map_add]
    simp [(hm τ).1]
  have hc : ∑ τ : E →+* ℂ, ((m τ).sum + a * s) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
    field_simp
    ring
  have hlie : lie E a (oneL E a) φ = (0 : ℂ) • φ := by
    rw [GlobalTheory.T.lie_central_element_trace E a, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => hsum τ, ← Finset.sum_smul, hc]
  simpa using GlobalTheory.T.central_eigen_exponential E a φ 0 hlie t g

end GlobalTheory.CompanionTheory.Clozel
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem lintegral_image_prod_Ico_of_invariant {X Z : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : X × ℝ ≃ₜ Z) (ν : Measure X) [SFinite ν] {h : Z → ENNReal} (hh : Measurable h)
    {k : X → ENNReal} (hk : ∀ x t, h (e (x, t)) = k x) (D : Set X) :
    ∫⁻ g in e '' (D ×ˢ Set.Ico (0 : ℝ) 1), h g ∂(Measure.map e (ν.prod volume)) =
      ∫⁻ x in D, k x ∂ν := by
  have hemb : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding
  rw [hemb.restrict_map, e.injective.preimage_image, hemb.lintegral_map, ← Measure.prod_restrict,
    lintegral_prod (fun p => h (e p)) (hh.comp e.measurable).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp [hk]

theorem lintegral_productDomain_norm_sq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (c : ENNReal), Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ φ : GA E a → ℂ, Continuous φ → (∀ t g, φ (splitCentre E a t * g) = φ g) → ∫⁻ g in ((fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) '' (RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)) ×ˢ Set.Ico (0 : ℝ) 1)), ‖φ g‖ₑ ^ 2 ∂(c • μ) = ∫⁻ x in RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)), ‖φ (x : GA E a)‖ₑ ^ 2 ∂ν := by
  intro E _ _ _ a ha μ _ ν _ c hmap φ hc hinv
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have hF : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = ⇑e :=
    funext fun p => (he p.1 p.2).symm
  rw [hF] at hmap
  rw [hF, ← hmap]
  set_option synthInstance.maxHeartbeats 200000 in
    refine lintegral_image_prod_Ico_of_invariant e ν
      (h := fun g => ‖φ g‖ₑ ^ 2) (k := fun x => ‖φ (x : GA E a)‖ₑ ^ 2)
      (hc.enorm.measurable.pow_const 2) (fun x t => ?_) _
  simp only [he, hinv]

end GlobalTheory.CompanionTheory.CuspTransfer
end
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
abbrev splitFd : Set (GA E a) :=
  (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) ''
    (RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)) ×ˢ Set.Ico (0 : ℝ) 1)

theorem coe_rationalGLOne_mem_latticeGL (δ : rationalGLOne (K := E) (n := a)) :
    ((δ : normOneGL (K := E) (n := a)) : GA E a) ∈ latticeGL E a := by
  obtain ⟨γ, hγ⟩ : ((δ : normOneGL (K := E) (n := a)) : GA E a) ∈ AdelicGLn.rationalGL E a := δ.2
  rw [← hγ]
  exact ratGL_mem_latticeGL γ

theorem splitCentre_mul_mul_swap (s t : ℝ) (d x : GA E a) :
    splitCentre E a s * splitCentre E a t * (d * x) = d * splitCentre E a s * (splitCentre E a t * x) := by
  simp only [mul_assoc]
  rw [← mul_assoc (splitCentre E a t) d x, splitCentre_comm t d, mul_assoc d, ← mul_assoc (splitCentre E a s) d,
    splitCentre_comm s d, mul_assoc]

theorem exists_lattice_smul_mem_splitFd (ha : 0 < a) (g : GA E a) :
    ∃ l : latticeGL E a, l • g ∈ splitFd E a := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  obtain ⟨⟨x, t⟩, rfl⟩ := e.surjective g
  rw [he]
  obtain ⟨δ, hδ, -⟩ := RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (rationalGLOne (K := E) (n := a)) x
  have hn : splitCentre E a ((-⌊t⌋ : ℤ) : ℝ) ∈ latticeGL E a := by
    rw [splitCentre_intCast]
    exact zpow_mem_latticeGL _
  refine ⟨⟨((δ : normOneGL (K := E) (n := a)) : GA E a) * splitCentre E a ((-⌊t⌋ : ℤ) : ℝ),
    mul_mem (coe_rationalGLOne_mem_latticeGL δ) hn⟩, ⟨δ • x, Int.fract t⟩,
    ⟨hδ, Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩
  change splitCentre E a (Int.fract t) * (((δ : normOneGL (K := E) (n := a)) : GA E a) * (x : GA E a)) =
    ((δ : normOneGL (K := E) (n := a)) : GA E a) * splitCentre E a ((-⌊t⌋ : ℤ) : ℝ) * (splitCentre E a t * (x : GA E a))
  have hf : Int.fract t = ((-⌊t⌋ : ℤ) : ℝ) + t := by
    rw [Int.fract]
    push_cast
    ring
  rw [hf, splitCentre_add, splitCentre_mul_mul_swap]

theorem eq_one_of_mul_mem_splitFd (ha : 0 < a) {l g : GA E a} (hl : l ∈ latticeGL E a) (hg : g ∈ splitFd E a)
    (h : l * g ∈ splitFd E a) : l = 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  obtain ⟨γ, m, rfl⟩ := mem_latticeGL_iff.1 hl
  obtain ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩ := hg
  obtain ⟨⟨y, u⟩, ⟨hy, hu⟩, hyu⟩ := h
  dsimp only at hx hs hy hu hyu
  have hγ : ratGL E a γ ∈ normOneGL (K := E) (n := a) := rationalGL_le_normOneGL ⟨γ, rfl⟩
  have key : e (y, u) = e (⟨ratGL E a γ, hγ⟩ * x, (m : ℝ) + s) := by
    rw [he, he, hyu, splitCentre_add, ← splitCentre_intCast]
    exact (splitCentre_mul_mul_swap (m : ℝ) s (ratGL E a γ) (x : GA E a)).symm
  obtain ⟨h1, h2⟩ := Prod.mk.inj (e.injective key)
  have hm : m = 0 := by
    have h3 : (m : ℝ) < 1 := by linarith [hs.1, hu.2]
    have h4 : (-1 : ℝ) < m := by linarith [hs.2, hu.1]
    have h5 : m < 1 := by exact_mod_cast h3
    have h6 : -1 < m := by exact_mod_cast h4
    omega
  subst hm
  let δ : rationalGLOne (K := E) (n := a) := ⟨⟨ratGL E a γ, hγ⟩, ⟨γ, rfl⟩⟩
  have h7 : δ = 1 := (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (rationalGLOne (K := E) (n := a)) x).unique
    (show δ • x ∈ _ from by
      change ((⟨ratGL E a γ, hγ⟩ : normOneGL (K := E) (n := a)) * x) ∈ _
      rw [← h1]
      exact hy) (by simpa using hx)
  have h8 : ratGL E a γ = 1 := congrArg (fun d : rationalGLOne (K := E) (n := a) => ((d : normOneGL (K := E) (n := a)) : GA E a)) h7
  rw [h8, zpow_zero, mul_one]

theorem measurableSet_splitFd (ha : 0 < a) : MeasurableSet (splitFd E a) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have h : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e :=
    funext fun p => (he p.1 p.2).symm
  rw [splitFd, h]
  exact e.isClosedEmbedding.measurableEmbedding.measurableSet_image.2
    ((RightCosetSpace.measurableSet_fundamentalDomain _).prod measurableSet_Ico)

theorem isFundamentalDomain_splitFd : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure], IsFundamentalDomain (latticeGL E a)
      ((fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) ''
        (RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)) ×ˢ Set.Ico (0 : ℝ) 1)) μ := by
  intro E _ _ _ a ha μ _
  refine IsFundamentalDomain.mk' (measurableSet_splitFd ha).nullMeasurableSet fun g => ?_
  obtain ⟨l, hl⟩ := exists_lattice_smul_mem_splitFd ha g
  refine ⟨l, hl, fun l' hl' => ?_⟩
  have h1 : ((l' : GA E a) * (l : GA E a)⁻¹) * ((l : GA E a) * g) ∈ splitFd E a := by
    have e0 : (l' : GA E a) * (l : GA E a)⁻¹ * ((l : GA E a) * g) = (l' : GA E a) * g := by group
    rw [e0]
    exact hl'
  have h2 := eq_one_of_mul_mem_splitFd ha (mul_mem l'.2 (inv_mem l.2)) hl h1
  exact Subtype.ext (mul_inv_eq_one.1 h2)

end GlobalTheory.CompanionTheory.CuspTransfer
end
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.haar_measure_norm_one_product : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a))) [ν.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ Measure.map (fun p : GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ := by
  first | exact @GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul | exact GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul | (intros; apply GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.local_invariant_cup_uniformizer : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → Submodule.span (ZMod (l ^ r)) {(Submodule.Quotient.mk z : H2 (muLoc F l r A))} = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top | exact GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top | (intros; apply GlobalTheory.CompanionTheory.KummerCup.span_class_eq_top <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatGen

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.Gen

variable {D : D7} {n : ℕ}

abbrev rm (x : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n := x.map (incA D)

theorem rm_mul (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x * y) = rm x * rm y :=
  Matrix.map_mul

theorem rm_add (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x + y) = rm x + rm y :=
  Matrix.map_add _ (map_add _) x y

theorem rm_neg (x : Matrix (Fin n) (Fin n) D.host.E) : rm (-x) = -rm x := by
  ext i j; simp [rm]

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  simp [rm]

theorem blockMatrix_map (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (rm a) (rm b) (rm c) (rm d) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

def ru (u : GL (Fin n) D.host.E) : GL (Fin n) (AE D) := Units.map (incA D).mapMatrix.toMonoidHom u

theorem ru_val (u : GL (Fin n) D.host.E) : (ru u).1 = rm u.1 := rfl

theorem ru_inv_val (u : GL (Fin n) D.host.E) : ((ru u)⁻¹).1 = rm (u⁻¹).1 := rfl

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) (rm b) 0 (rm d))
    (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) (ru u)⁻¹
  have hmm' : mat m = blk4 (rm (u⁻¹).1) 0 0 (adj (rm u.1)) := by
    rw [hmm, ru_inv_val, inv_inv, ru_val]
  have h1 : (adj (rm u.1) : Mx D n n) * rm d = 1 := by simpa using (rel hg).2.1
  have hmS : m ∈ S := hm m u⁻¹ (by rw [hmm', inv_inv])
  rw [← S.mul_mem_cancel_left hmS]
  refine hn _ ((u⁻¹).1 * b) ?_
  have h2 : rm (u⁻¹).1 * rm u.1 = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  rw [mat_mul, hmm', hg, submatrix_fromBlocks_mul]
  simp only [h2, mul_zero, zero_mul, add_zero, zero_add, h1]
  change _ = blk4 1 (rm _) 0 1
  rw [rm_mul]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) 0 (rm c) (rm d))
    (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, rm_neg, rm_neg]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Matrix (Fin n) (Fin n) D.host.E}
    (hg : mat g = blk4 (rm a) (rm b) (rm c) (rm d)) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have h1 : (adj (rm u.1) : Mx D n n) * rm b = adj (rm b) * rm u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h0 : rm u.1 * rm (u⁻¹).1 = 1 := by rw [← rm_mul, Units.mul_inv, rm_one]
  have h0' : rm (u⁻¹).1 * rm u.1 = 1 := by rw [← rm_mul, Units.inv_mul, rm_one]
  have h2 : (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm u.1) = 1 := by rw [← adj_mul, h0, adj_one]
  have h3 : (adj (-(rm b * rm (u⁻¹).1)) : Mx D n n) = -(rm b * rm (u⁻¹).1) := by
    rw [adj_neg, adj_mul]
    congr 1
    calc (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm b) = adj (rm (u⁻¹).1) * (adj (rm b) * rm u.1) * rm (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, h0, mul_one]
      _ = rm b * rm (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  have hxS : x ∈ S := hn x (-(b * (u⁻¹).1)) (by rw [hx]; change _ = blk4 1 (rm _) 0 1; rw [rm_neg, rm_mul])
  rw [← S.mul_mem_cancel_left hxS]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul, rm_add, rm_mul, rm_neg, rm_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, h0', mul_one, add_neg_cancel]

theorem adj_rm {x : Matrix (Fin n) (Fin n) D.host.E} (hx : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) :
    adj (rm x : Mx D n n) = rm x := by
  ext i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg _ (hx j i)

theorem exists_herm_isUnit (c d p q : Matrix (Fin n) (Fin n) D.host.E) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) D.host.E, (∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) ∧
      IsUnit (c * x + d) := by
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_notMem (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (RingHom.id _) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun _ => rfl) c d p q h ⊥ Ideal.bot_isMaximal
  refine ⟨x, hx, ?_⟩
  have e : x.map (RingHom.id D.host.E) = x := by ext i j; rfl
  rw [e] at hu
  refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h0 => hu ?_)
  rw [h0, zero_mul]
  exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.RatGen

namespace GlobalTheory.CompanionTheory

theorem RatGen.GF_le_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (G D n)),
  (∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S) →
  (∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S) →
  (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S) → GF D n ≤ S := by
  intro D n S hm hn hw γ hγ
  have hrat : ∀ {γ : G D n}, γ ∈ GF D n →
      ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
    intro γ h
    obtain ⟨x, -, hx⟩ := h
    exact ⟨x.1, (congrArg Units.val hx).symm⟩
  obtain ⟨M, hM⟩ := hrat hγ
  obtain ⟨M', hM'⟩ := hrat ((GF D n).inv_mem hγ)
  obtain ⟨a, b, c, d, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M
  obtain ⟨p', p, q', q, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M'
  rw [RatGen.blockMatrix_map] at hM hM'
  have h1 : mat γ * mat γ⁻¹ = 1 := by rw [← GlobalTheory.StdUnn.Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hM, hM', Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  have h2 : RatGen.rm (c * p + d * q) = RatGen.rm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
    rw [RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul, RatGen.rm_one]
    exact (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  have h3 : c * p + d * q = 1 := Matrix.map_injective GlobalTheory.MixModel.incA_injective h2
  obtain ⟨x, hx, hu⟩ := RatGen.exists_herm_isUnit c d p q h3
  obtain ⟨y, hy⟩ := (Model.exists_unip (RatGen.rm x)).2 (RatGen.adj_rm hx)
  rw [← S.mul_mem_cancel_right (hn y x hy)]
  refine RatGen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [GlobalTheory.StdUnn.Gen.mat_mul, hM, hy, Model.submatrix_fromBlocks_mul, RatGen.rm_add, RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.CompanionTheory
end
end
