module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} = ⊤ :=
  @GlobalTheory.kfin_span_raising_words_lowK
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CharMulSchA

theorem charMul_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ b : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    (fun x => ψ (x ⬝ᵥ b) * Φ x) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ ψ hψ b Φ hΦ
  have h := GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ (0, b) Φ hΦ
  convert h using 1
  funext x
  simp [GlobalTheory.WeilM.schr]

end GlobalTheory.CharMulSchA
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_periodic_measurable_schwartz_bound : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ (r : (κ → AF F) → ℂ) (K : Set (κ → Fv F v)), @Measurable _ _ (borel _) _ r ∧
      (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r ∈ GlobalTheory.WeilM.schA F κ) ∧
      IsCompact K ∧ (interior K).Nonempty ∧
      ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 ∧
        ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ := by
  first | exact @GlobalTheory.Cofactor.exists_cofactor | exact GlobalTheory.Cofactor.exists_cofactor | (intros; apply GlobalTheory.Cofactor.exists_cofactor <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DblTrace

open Matrix

theorem hTens_dbl {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E)
    (x y : Matrix α (β ⊕ β) E) :
    hTens c JA (dbl JB) x y = hTens c JA JB x.toCols₁ y.toCols₁ + hTens c JA (-JB) x.toCols₂ y.toCols₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, toCols₁, toCols₂,
    of_apply, ← Finset.sum_add_distrib]

theorem rhs_dbl {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m K)
    (X U : Matrix m (n ⊕ n) K) (B : Matrix n n K) :
    ∑ k, ∑ l, (-(A * X * (fromBlocks B 0 0 (-B))ᵀ)) k l * U k l =
      ∑ k, ∑ l, (-(A * X.toCols₁ * Bᵀ)) k l * U.toCols₁ k l +
        ∑ k, ∑ l, (-(A * X.toCols₂ * (-B)ᵀ)) k l * U.toCols₂ k l := by
  have hX : A * X = fromCols (A * X.toCols₁) (A * X.toCols₂) := by
    conv_lhs => rw [← fromCols_toCols X]
    rw [mul_fromCols]
  rw [hX, fromBlocks_transpose, fromCols_mul_fromBlocks]
  simp [Fintype.sum_sum_type, Finset.sum_add_distrib, toCols₁, toCols₂]
  ring

end GlobalTheory.DblTrace

open GlobalTheory.DblTrace in
theorem GlobalTheory.DblTrace.trace_pairing_dbl : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E)
    (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) →
    ∀ (x u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)), x.map (piW τ) = 0 → u.map (piW (τ.comp σ)) = 0 →
    piW τ (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) + piW (τ.comp σ) (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) =
      ∑ k, ∑ l, (-(JA.map τ * x.map (piW (τ.comp σ)) * ((dbl JB).map τ)ᵀ)) k l * u.map (piW τ) k l := by
  intro F E _ _ _ _ _ σ hcm v τ m n JA JB hA hB x u hx hu
  have hneg : incM F (-JB) = -incM F JB := by
    simp [incM, Matrix.map_neg]
  have hB' : ∀ i j, σ ((-JB) j i) = -(-JB) i j := by
    intro i j; simp [hB]
  have h1 : x.toCols₁.map (piW τ) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hx i) (Sum.inl j)
  have h2 : u.toCols₁.map (piW (τ.comp σ)) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hu i) (Sum.inl j)
  have h3 : x.toCols₂.map (piW τ) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hx i) (Sum.inr j)
  have h4 : u.toCols₂.map (piW (τ.comp σ)) = 0 := by
    exact Matrix.ext fun i j => congrFun (congrFun hu i) (Sum.inr j)
  have hd : (dbl JB).map τ = Matrix.fromBlocks (JB.map τ) 0 0 (-(JB.map τ)) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  rw [hTens_dbl, ← hneg, map_add (f := _), map_add (f := _), add_add_add_comm, GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm τ JA JB hA hB _ _ h1 h2,
    GlobalTheory.T.hermitianTensor_skewHermitian_split_symplectic_pair hcm τ JA (-JB) hA hB' _ _ h3 h4, hd, rhs_dbl]
  have hm : (-JB).map τ = -(JB.map τ) := by ext i j; simp
  rw [hm]
  rfl
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LagrCoord

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  intro h0
  apply hD
  rw [← hA, ← Matrix.det_submatrix_equiv_self e.symm,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) e.symm Function.bijective_id,
    Matrix.submatrix_mul _ _ e.symm (id : Fin n → Fin n) id Function.bijective_id,
    Matrix.det_mul, Matrix.det_mul, Matrix.submatrix_id_id, h0, mul_zero, zero_mul]

theorem det_ne_zero_of_hasSig_smul {n r s : ℕ} {c : ℂ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig (c • M) r s) :
    M.det ≠ 0 := by
  intro h0
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, h0, mul_zero]

theorem det_ne_zero_of_map {E : Type} [CommRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) x ∧ x.map (piW t) = 0 ∧ -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = Y := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Y
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hXd : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig (hX.sig w))
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_map W.J (B.emb w).1 (det_ne_zero_of_hasSig_smul (hW.sig w))
  have ht : Function.Injective t := t.toRingHom.injective
  have hXt : IsUnit (X.J.map t).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hXd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom X.J)
  have hWt : IsUnit ((W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hWd
    apply ht
    rw [map_zero, ← h0]
    exact (RingHom.map_det t.toRingHom W.J)
  obtain ⟨x, hxat, hx0, hx1⟩ := GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hB.cm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
    (-((X.J.map t)⁻¹ * Y * ((W.J.map t)ᵀ)⁻¹))
  refine ⟨x, hxat, hx0, ?_⟩
  rw [hx1]
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWt, Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hXt]

end GlobalTheory.LagrCoord
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.schroedinger_preserves_adelic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (p : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ p Φ ∈ schA F κ := by
  first | exact @GlobalTheory.SchrKeepsSchA.schr_mem_schA | exact GlobalTheory.SchrKeepsSchA.schr_mem_schA | (intros; apply GlobalTheory.SchrKeepsSchA.schr_mem_schA <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.character_at_uniformizer_not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  first | exact @GlobalTheory.NuGood.not_root_of_unity | exact GlobalTheory.NuGood.not_root_of_unity | (intros; apply GlobalTheory.NuGood.not_root_of_unity <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK


theorem _root_.GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ f : SInf F κ, Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  first | exact @GlobalTheory.RestPure.rest_evI_finprod | exact GlobalTheory.RestPure.rest_evI_finprod | (intros; apply GlobalTheory.RestPure.rest_evI_finprod <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isConjSelfReciprocal_of_dvd_elliptic_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q := by
  first | exact @GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell | exact GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell | (intros; apply GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem units_identity {G : Type*} [CommGroup G] (u P Q R β γ ε : G) (d t : ℤ) :
    (u * P * β⁻¹) * (u * Q * γ⁻¹) ^ (d * t) * (u * R * ε⁻¹) ^ d =
      u ^ (d * (t + 1) + 1) * (β * (γ ^ d) ^ t * (ε ^ d) ^ (1 : ℤ))⁻¹ * (P * Q ^ (d * t) * R ^ d) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

theorem pw_pw {X : Scheme.{0}} (L : LB X) (a b : ℤ) : pw (pw L a) b = pw L (a * b) := by
  show (⟨L.ι, L.U, fun i j => (L.g i j ^ a) ^ b⟩ : LB X) = ⟨L.ι, L.U, fun i j => L.g i j ^ (a * b)⟩
  congr 1
  funext i j
  exact (zpow_mul _ _ _).symm

theorem lbIso_tw_tw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d t : ℤ) :
    LBIso (tw (tw L (pw L d) t) (pw L d) 1) (pw L (d * (t + 1) + 1)) := by
  refine GlobalTheory.LBAlg.lbIso_of_germs
    (A := tw (tw L (pw L d) t) (pw L d) 1) (B := pw L (d * (t + 1) + 1))
    (fun p => res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.1 from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g p.1 p.2.1.1) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.1.2 from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g p.1 p.2.1.2) ^ (d * t) *
      res (show (pw L (d * (t + 1) + 1)).U p.1 ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U p.2 ≤
          L.U p.1 ⊓ L.U p.2.2 from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g p.1 p.2.2) ^ d) ?_
  rintro x ⟨a, ⟨b, c⟩, e⟩ ⟨a', ⟨b', c'⟩, e'⟩ ha hp ha' hq
  have hb : x ∈ L.U b := hp.1.1
  have hc : x ∈ L.U c := hp.1.2
  have he : x ∈ L.U e := hp.2
  have hb' : x ∈ L.U b' := hq.1.1
  have hc' : x ∈ L.U c' := hq.1.2
  have he' : x ∈ L.U e' := hq.2
  have inv : ∀ {j j' : L.ι}, x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U j' ⊓ L.U j) (L.g j' j) = (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ :=
    fun hj hj' => eq_inv_of_mul_eq_one_right
      ((gm_cocycle hL (𝟙 X) x hj hj' hj).trans (gm_self hL (𝟙 X) x hj))
  have rel : ∀ {i i' j j' : L.ι}, x ∈ L.U i → x ∈ L.U i' → x ∈ L.U j → x ∈ L.U j' →
      gm (𝟙 X) x (L.U i ⊓ L.U j) (L.g i j) = gm (𝟙 X) x (L.U i ⊓ L.U i') (L.g i i') *
        gm (𝟙 X) x (L.U i' ⊓ L.U j') (L.g i' j') * (gm (𝟙 X) x (L.U j ⊓ L.U j') (L.g j j'))⁻¹ := by
    intro i i' j j' hi hi' hj hj'
    rw [← gm_cocycle hL (𝟙 X) x hi hi' hj, ← gm_cocycle hL (𝟙 X) x hi' hj' hj, inv hj hj', mul_assoc]
  have sec : ∀ (a₀ b₀ c₀ e₀ : L.ι) (h : (𝟙 X : X ⟶ X) x ∈ (pw L (d * (t + 1) + 1)).U a₀ ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀)),
      gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀))
        (res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U b₀ from fun _ hx => ⟨hx.1, hx.2.1.1⟩) (L.g a₀ b₀) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U c₀ from fun _ hx => ⟨hx.1, hx.2.1.2⟩) (L.g a₀ c₀) ^ (d * t) *
        res (show (pw L (d * (t + 1) + 1)).U a₀ ⊓ (tw (tw L (pw L d) t) (pw L d) 1).U ((b₀, c₀), e₀) ≤
          L.U a₀ ⊓ L.U e₀ from fun _ hx => ⟨hx.1, hx.2.2⟩) (L.g a₀ e₀) ^ d) =
      gm (𝟙 X) x (L.U a₀ ⊓ L.U b₀) (L.g a₀ b₀) * gm (𝟙 X) x (L.U a₀ ⊓ L.U c₀) (L.g a₀ c₀) ^ (d * t) *
        gm (𝟙 X) x (L.U a₀ ⊓ L.U e₀) (L.g a₀ e₀) ^ d := by
    intro a₀ b₀ c₀ e₀ h
    rw [map_mul, map_mul, map_zpow, map_zpow, gm_res _ x _ h, gm_res _ x _ h, gm_res _ x _ h]
  have eB : gm (𝟙 X) x ((pw L (d * (t + 1) + 1)).U a ⊓ (pw L (d * (t + 1) + 1)).U a')
      ((pw L (d * (t + 1) + 1)).g a a') = gm (𝟙 X) x (L.U a ⊓ L.U a') (L.g a a') ^ (d * (t + 1) + 1) :=
    map_zpow (gm (𝟙 X) x (L.U a ⊓ L.U a')) (L.g a a') _
  have eA : gm (𝟙 X) x ((tw (tw L (pw L d) t) (pw L d) 1).U ((b, c), e) ⊓
      (tw (tw L (pw L d) t) (pw L d) 1).U ((b', c'), e'))
      ((tw (tw L (pw L d) t) (pw L d) 1).g ((b, c), e) ((b', c'), e')) =
      gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b') * (gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d) ^ t *
        (gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d) ^ (1 : ℤ) := by
    have g1 : gm (𝟙 X) x ((pw L d).U c ⊓ (pw L d).U c') ((pw L d).g c c') =
        gm (𝟙 X) x (L.U c ⊓ L.U c') (L.g c c') ^ d := map_zpow _ _ _
    have g2 : gm (𝟙 X) x ((pw L d).U e ⊓ (pw L d).U e') ((pw L d).g e e') =
        gm (𝟙 X) x (L.U e ⊓ L.U e') (L.g e e') ^ d := map_zpow _ _ _
    refine (GlobalTheory.LBAlg.gm_tw (tw L (pw L d) t) (pw L d) 1 (𝟙 X) x ((b, c), e) ((b', c'), e') ⟨hp, hq⟩).trans ?_
    exact congrArg₂ (· * ·) ((GlobalTheory.LBAlg.gm_tw L (pw L d) t (𝟙 X) x (b, c) (b', c') ⟨hp.1, hq.1⟩).trans
      (congrArg₂ (· * ·) rfl (congrArg (· ^ t) g1))) (congrArg (· ^ (1 : ℤ)) g2)
  refine (sec a b c e ⟨ha, hp⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm
    (congrArg (·⁻¹) eA.symm)) (sec a' b' c' e' ⟨ha', hq⟩).symm))
  rw [rel ha ha' hb hb', rel ha ha' hc hc', rel ha ha' he he']
  exact units_identity _ _ _ _ _ _ _ d t

end GlobalTheory.FormalAlg.ConsecPowers

namespace GlobalTheory.FormalAlg.ConsecPowers

theorem exists_veryAmpleBy_pw_and_succ : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∀ c : ℕ, c = d ∨ c = d + 1 → ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (GlobalTheory.AbLaw.pw L c)), VeryAmpleBy X.hom (GlobalTheory.AbLaw.pw L c) s := by
  intro R _ X L hL hA
  obtain ⟨d₁, hd₁, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R X L hL).1 hA
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (AbLaw.pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hH := isLB_pw hL (d₁ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.TwistGen.twist_generated R X.left X.hom _ n s hH hs L hL
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t₀ ≤ (t : ℤ) := ⟨t₀.toNat, Int.self_le_toNat t₀⟩
  obtain ⟨m, u, hu⟩ := ht₀ (t : ℤ) ht
  refine ⟨d₁ * (t + 1), Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), fun c hc => ?_⟩
  rcases hc with rfl | rfl
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R X.left X.hom _ n s hH hs (t + 1) (by omega)
    have e : GlobalTheory.AbLaw.pw L ((d₁ * (t + 1) : ℕ) : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) ((t + 1 : ℕ) : ℤ) := by
      rw [pw_pw]
      push_cast
      rfl
    rw [e]
    exact ⟨n', s', hs'⟩
  · obtain ⟨n', s', hs'⟩ := GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple R X.left X.hom (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (tw L (GlobalTheory.AbLaw.pw L (d₁ : ℤ)) (t : ℤ))
      n m s u hH (isLB_tw hL hH _) hs hu
    obtain ⟨s'', hs''⟩ := GlobalTheory.exists_veryAmpleBy_of_lbIso (isLB_tw (isLB_tw hL hH _) hH 1) (isLB_pw hL _)
      (lbIso_tw_tw hL (d₁ : ℤ) (t : ℤ)) hs'
    have e : ((d₁ * (t + 1) + 1 : ℕ) : ℤ) = (d₁ : ℤ) * ((t : ℤ) + 1) + 1 := by push_cast; ring
    rw [e]
    exact ⟨n', s'', hs''⟩

end GlobalTheory.FormalAlg.ConsecPowers
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_weilRepresentation_vacuum_cosetVectors_grid : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (sc : Consts) (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ W : G.Weil, W.ψ = ψ := by
  first | exact @GlobalTheory.GridWeil.exists_weil | exact GlobalTheory.GridWeil.exists_weil | (intros; apply GlobalTheory.GridWeil.exists_weil <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.LocGlobIndEt

theorem eqv_of_comp_iso {R : Type} [CommRing R] {E E' E'' : Spc} (g : E ⟶ E') (e : E' ⟶ E'') [IsIso e] (F : Shv R)
    (h : Eqv R (g ≫ e) F) : Eqv R g F := by
  intro n
  have he : Function.Bijective (pull R e F n) := by
    refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv e) F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    · rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  refine (Function.Bijective.of_comp_iff (pull R g F n) he).1 ?_
  have : (⇑(pull R g F n) ∘ ⇑(pull R e F n)) = ⇑(pull R (g ≫ e) F n) := funext fun x => (pull_comp R g e F n x).symm
  rw [this]
  exact h n

theorem main : ∀ (q : ℕ) (B : Type) [CommRing B] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of B)) [QuasiCompact f]
    [QuasiSeparated f], IsUnit (q : B) → ∀ i : ℤ, (∀ (A : Type) [CommRing A] [Algebra B A], SH A → IndEt B A →
      Eqv _ (sch.map (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B A))))) (tw q i)) →
    Eqv _ (sch.map f) (tw q i) := by
  intro q B _ Y f _ _ _ i hyp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) Y (Spec (CommRingCat.of B)) (Spec (CommRingCat.of B)) f
    (𝟙 _) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hind, rfl⟩ := isStalk_affine B O s hs
  have key := @hyp O _ inst hSH hind
  refine eqv_of_comp_iso _ (sch.map (pullback.snd (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap B O))))) _ ?_
  rw [← sch.map_comp, pullback.lift_snd, Category.comp_id]
  generalize hf : f ≫ 𝟙 _ = f'
  rw [Category.comp_id] at hf
  subst hf
  exact key

end GlobalTheory.LocGlobIndEt
end
end
