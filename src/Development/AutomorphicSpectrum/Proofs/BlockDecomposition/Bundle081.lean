module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import GroundTheory.LocalFields.Uniqueness
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle049
public import Formalism.RealPlaceAnalysis.Bundle002
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import GroundTheory.GlobalFields.Adele.Bundle002
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle051
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace

@[expose] public section

section

open PositivityTheory.Rg.Tf.Loc GroundTheory.LocalField Topology
open Matrix

namespace GlobalTheory.CompanionTheory.LocTop

section Field

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem secondCountable_field : SecondCountableTopology F := by
  letI N : NontriviallyNormedField F := nontriviallyNormedField F
  have hw : @WeaklyLocallyCompactSpace F N.toUniformSpace.toTopologicalSpace :=
    (inferInstance : WeaklyLocallyCompactSpace F)
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have h : @SecondCountableTopology F N.toUniformSpace.toTopologicalSpace := inferInstance
  exact h

variable (n : ℕ)

def intMat : Set (Matrix (Fin n) (Fin n) F) := {X | ∀ i j, X i j ∈ intO F}

theorem isCompact_intMat : IsCompact (intMat F n) := by
  have hO : IsCompact ((intO F : Subring F) : Set F) :=
    IsNonarchimedeanLocalField.isCompact_closedBall F 1
  have hrow : IsCompact (Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F)) :=
    isCompact_univ_pi fun _ => hO
  have hmat : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F)) :=
    isCompact_univ_pi fun _ => hrow
  have hset : intMat F n = Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => ((intO F : Subring F) : Set F) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [hset]
  exact hmat

theorem isOpen_intMat : IsOpen (intMat F n) := by
  have hO : IsOpen ((intO F : Subring F) : Set F) :=
    Valuation.isOpen_integer (v := ValuativeRel.valuation F)
  have hset : intMat F n =
      ⋂ i : Fin n, ⋂ j : Fin n, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹'
        ((intO F : Subring F) : Set F) := by
    ext X
    simp [intMat]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage ?_
  exact (continuous_apply j).comp (continuous_apply i)

theorem mem_unitGL_iff (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (g : Matrix (Fin n) (Fin n) F) ∈ intMat F n ∧
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∈ intMat F n := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((h : Matrix (Fin n) (Fin n) (intO F)) i j).2
    · rw [← map_inv]
      exact (((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨(g : Matrix (Fin n) (Fin n) F) i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) (intO F) :=
      fun i j => ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, h2 i j⟩
    have hA : A.map (intO F).subtype = (g : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hB : B.map (intO F).subtype = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      ext i j; rfl
    have hinj : Function.Injective
        (fun X : Matrix (Fin n) (Fin n) (intO F) => X.map (intO F).subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
    have hBA : B * A = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

variable [T2Space F]

theorem unitGL_eq_preimage :
    (unitGL (n := Fin n) F : Set (GL (Fin n) F)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) F) ⁻¹'
        (intMat F n ×ˢ (MulOpposite.unop ⁻¹' intMat F n)) := by
  ext g
  exact mem_unitGL_iff F n g

theorem isOpen_unitGL : IsOpen (unitGL (n := Fin n) F : Set (GL (Fin n) F)) := by
  rw [unitGL_eq_preimage]
  exact ((isOpen_intMat F n).prod ((isOpen_intMat F n).preimage MulOpposite.continuous_unop)).preimage
    Units.continuous_embedProduct

theorem isCompact_unitGL : IsCompact (unitGL (n := Fin n) F : Set (GL (Fin n) F)) := by
  rw [unitGL_eq_preimage]
  refine (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).isCompact_preimage
    ((isCompact_intMat F n).prod ?_)
  exact (MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (isCompact_intMat F n)

theorem locallyCompact_GL : LocallyCompactSpace (GL (Fin n) F) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).locallyCompactSpace

theorem secondCountable_GL : SecondCountableTopology (GL (Fin n) F) := by
  haveI := secondCountable_field F
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) F)).secondCountableTopology

end Field

section Twisted

variable {k E : Type} [Field k] [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  [Algebra k E]

theorem continuous_sigmaGL (σ : E ≃ₐ[k] E) (hσ : Continuous σ) (n : ℕ) :
    Continuous (sigmaGL σ : Monoid.End (GL (Fin n) E)) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hσ
  · have : (fun g : GL (Fin n) E => (((sigmaGL σ g : GL (Fin n) E)⁻¹ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E)) =
        fun g : GL (Fin n) E => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map σ := by
      funext g
      rw [← map_inv]
      rfl
    show Continuous (fun g : GL (Fin n) E => (((sigmaGL σ g : GL (Fin n) E)⁻¹ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E))
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_map hσ

theorem isClosed_twCent (σ : E ≃ₐ[k] E) (hσ : Continuous σ) (n : ℕ) (δ : GL (Fin n) E) :
    IsClosed (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) := by
  haveI : T2Space (GL (Fin n) E) :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) E)).t2Space
  have hθ := continuous_sigmaGL σ hσ n
  have : (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) = {g | g⁻¹ * δ * sigmaGL σ g = δ} := rfl
  rw [this]
  exact isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const

end Twisted

theorem t0 : T0 := by
  refine ⟨fun F _ _ _ _ n => ?_, ?_⟩
  · haveI : T2Space F := t2Space_of_isNonarchimedeanLocalField F
    exact ⟨locallyCompact_GL F n, secondCountable_GL F n, isOpen_unitGL F n, isCompact_unitGL F n⟩
  · intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ n δ
    haveI : T2Space E := t2Space_of_isNonarchimedeanLocalField E
    exact isClosed_twCent σ (continuous_algHom σ.toAlgHom) n δ

end GlobalTheory.CompanionTheory.LocTop
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.commutator_coercive_on_annihilator : ∀ {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ), (∀ A : Matrix (Fin m) (Fin m) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0) → ∃ c : ℝ, 0 < c ∧ ∀ A : Matrix (Fin m) (Fin m) ℂ, A *ᵥ v = 0 → Formalism.REAL.hs A ≤ c * Formalism.REAL.hs (A * X - X * A) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator | exact GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator <;> assumption)
end

section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AdjSum

open Matrix Polynomial

theorem det_add_ones_field {K : Type*} [Field K] {n : ℕ} (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) :
    (B + Matrix.of fun _ _ => (1 : K)).det = B.det + ∑ a, ∑ b, B.adjugate a b := by
  have hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin n) (Fin n) K) =
      replicateCol Unit (fun _ => (1 : K)) * replicateRow Unit (fun _ => (1 : K)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hJ, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hB)]
  have hinv : B⁻¹ = (B.det)⁻¹ • B.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have h1 : ∀ C : Matrix Unit Unit K, C.det = C () () := fun C => det_unique C
  rw [h1, hinv]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.smul_apply,
    replicateRow_apply, replicateCol_apply, one_mul, mul_one, smul_eq_mul, Finset.univ_unique,
    Finset.sum_singleton]
  rw [mul_add, mul_one]
  congr 1
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  field_simp

theorem det_add_ones {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) :
    (A + Matrix.of fun _ _ => (1 : R)).det = A.det + ∑ a, ∑ b, A.adjugate a b := by
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have hdet : ∀ C : Matrix (Fin n) (Fin n) R, f C.det = (C.map f).det := fun C =>
    RingHom.map_det f C
  apply hf
  have h := det_add_ones_field (A.map f) (by
    rw [← hdet]
    exact (map_ne_zero_iff f hf).mpr hA)
  have hadj : (A.map f).adjugate = A.adjugate.map f := by
    have := RingHom.map_adjugate f A
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hsum : (A.map f + Matrix.of fun _ _ => (1 : K)) =
      (A + Matrix.of fun _ _ => (1 : R)).map f := by
    ext i j
    simp
  rw [hsum, ← hdet, ← hdet, hadj] at h

  rw [h, map_add (f := _), map_sum]

  simp [map_sum]

theorem entry (n : ℕ) (l : Fin n → ℂ) (a b : Fin n) :
    ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
        (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z)) a b =
      if a = b then Polynomial.X + Polynomial.C (l a)
      else if a < b then -1 else 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem adj_sum : ∀ (n : ℕ) (l : Fin n → ℂ), ∑ a, ∑ b, (Matrix.adjugate ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) + (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z))) a b = ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) - ∏ s, (Polynomial.X + Polynomial.C (l s)) := by
  intro n l
  set M : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
    (Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
      (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z) with hM
  have he : ∀ a b, M a b = if a = b then Polynomial.X + Polynomial.C (l a)
      else if a < b then -1 else 0 := entry n l
  have hdet : M.det = ∏ s, (Polynomial.X + Polynomial.C (l s)) := by
    rw [Matrix.det_of_upperTriangular]
    · exact Finset.prod_congr rfl fun s _ => by rw [he]; simp
    · intro i j hij
      have hij' : j < i := hij
      rw [he, if_neg (ne_of_gt hij'), if_neg (not_lt_of_gt hij')]
  have hdet1 : (M + Matrix.of fun _ _ => (1 : Polynomial ℂ)).det =
      ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) := by
    rw [Matrix.det_of_lowerTriangular]
    · exact Finset.prod_congr rfl fun s _ => by simp [he]
    · intro i j hij
      have hij' : i < j := hij
      simp [he, ne_of_lt hij', hij']
  have hne : M.det ≠ 0 := by
    rw [hdet, Finset.prod_ne_zero_iff]
    intro s _
    exact (Polynomial.monic_X_add_C (l s)).ne_zero
  have h := det_add_ones M hne
  rw [hdet1, hdet] at h
  rw [h]
  ring

end GlobalTheory.CompanionTheory.AdjSum
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

abbrev Idx (n d : ℕ) : Type := Fin n ⊕ (Fin d × {p : Fin n × Fin n // p.1 < p.2})

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hCo (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ}
    (S : HermR R σ n) : Idx n d → R :=
  Sum.elim
    (fun i => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    (fun q => (Algebra.TensorProduct.basis R b).repr
      ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) q.2.1.1 q.2.1.2) q.1)

def coordForm (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) : Matrix (Idx n d) (Idx n d) F :=
  Matrix.fromBlocks 1 0 0
    (Matrix.blockDiagonal fun _ : {p : Fin n × Fin n // p.1 < p.2} =>
      Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l)))

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def starLoc (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : R → ℂ) (dx : Measure (Fin n → Fin M → R ⊗[F] E))
    (Φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (b : HermR R σ n) : ℂ :=
  ∫ X, Φ X * ψR (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J X))) ∂dx

def psiFin (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Ainf F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Af F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsCoord (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) : Prop :=
  IsHomeomorph Θ ∧ (∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) ∧
    (∀ x w, Θ ((1 : Ainf F) ⊗ₜ[F] x) w = τ w x) ∧
    ∀ z w, ((e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w : ℝ) : ℂ) = Θ z w + conj (Θ z w)

def tupC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n M : ℕ} (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    InfinitePlace F → Fin n → Fin M → ℂ :=
  fun w a i => Θ (X a i) w

def matC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) : Matrix (Fin n) (Fin n) ℂ :=
  fun a c => Θ (b a c) w

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

section

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RedCov.Simple

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def boxF (ρ : ℝ) : Set (AF F) :=
  {a | (∀ w : InfinitePlace F, ‖a.1 w‖ ≤ ρ) ∧ a.2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}

def boxE (ρ : ℝ) : Set (AF F ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr x k ∈ boxF F ρ}

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end

section

open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

theorem _root_.GlobalTheory.T.lie_algebra_of_tangent_curve : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G → ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 → (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by
  first | exact @GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg | exact GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg | (intros; apply GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg <;> assumption)
end

section

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

def colGe (d j : ℕ) (i l : Fin d) : Prop := i < l ∧ j ≤ (l : ℕ)

variable (K : Type) [Field K]

def colGeE (d j : ℕ) (i l : Fin d) : K := if (l : ℕ) = i + 1 ∧ j ≤ (l : ℕ) then 1 else 0

def colGeR (d j : ℕ) (r : Fin j → K) (i l : Fin d) : K :=
  colGeE K d (j + 1) i l + if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0

def blkEmb (d j : ℕ) (A : Matrix (Fin j) (Fin j) K) : Matrix (Fin d) (Fin d) K := fun i l =>
  if h : (i : ℕ) < j ∧ (l : ℕ) < j then A ⟨i, h.1⟩ ⟨l, h.2⟩ else if i = l then 1 else 0

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end
