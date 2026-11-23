module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle238
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut.OppFlagWeight

theorem weight_of_triangular {A : Type} [CommRing A] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) A}
    {L T : Matrix (Fin r) (Fin n) A} {x : Matrix (Fin n) (Fin n) A} {B B' : Matrix (Fin r) (Fin r) A}
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M)
    (hLX : L * X = 1) (hTY : T * Y = 1) (hLY : L * Y = 0)
    (hB : x * Y = Y * B) (hB' : L * x = B' * L) (tB : ∀ i j, d j < d i → B i j = 0) (tB' : ∀ i j, d i < d j → B' i j = 0)
    (ε : Option (Fin r ⊕ Fin r) → Matrix (Fin n) (Fin n) A)
    (e0 : ε none = 1 - (X * L + Y * T)) (e1 : ∀ j, ε (some (.inl j)) = X * single j j (1 : A) * L)
    (e2 : ∀ j, ε (some (.inr j)) = Y * single j j (1 : A) * T) :
    ∀ a b, wt d M b < wt d M a → ε a * x * ε b = 0 := by
  have k0 : ε none * Y = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLY, hTY]; simp
  have k1 : L * ε none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLY, hLX]; simp
  have k2 : ∀ (m : Matrix (Fin n) (Fin n) A) j, m * Y = 0 → m * x * ε (some (.inr j)) = 0 := fun m j h => by
    rw [e2, Matrix.mul_assoc Y, ← Matrix.mul_assoc, Matrix.mul_assoc m, hB, ← Matrix.mul_assoc m, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp [wt] at hab
  · have := hd j; simp [wt] at hab; omega
  · exact k2 _ j k0
  · rw [e1, Matrix.mul_assoc _ L, hB', ← Matrix.mul_assoc, Matrix.mul_assoc _ L, k1, Matrix.mul_zero]
  · rw [e1, e1, sandwich_eq_zero hLX, hB', Matrix.mul_assoc, hLX, Matrix.mul_one]
    exact tB' i j (by simp [wt] at hab; omega)
  · exact k2 _ j (by rw [e1, Matrix.mul_assoc, hLY, Matrix.mul_zero])
  · have := hd i; simp [wt] at hab; omega
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, e2, sandwich_eq_zero hTY, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hTY, Matrix.one_mul]
    exact tB i j (by simp [wt] at hab; omega)

theorem not_raise_of_mem_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J Y d, ∀ a b, wt d M b < wt d M a → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y d M hd _ hY hXY p hp
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => sigma_sigma h _
  have hYX : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hXY
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have f := form_mul_of_mul_cols eB'
  rw [inv_inv] at f
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have adj : ∀ Z : Matrix (Fin r) (Fin r) E, adjA σ J ((X * Z * (Formalism.UG.cT (σ : E →+* E) Y * J)).map φ) =
      Y.map φ * (Formalism.UG.cT (σ : E →+* E) Z).map φ * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun Z => by
    rw [adjA_map, ← Matrix.map_mul, ← Matrix.map_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J⁻¹, Matrix.nonsing_inv_mul _ (det_isUnit hJ), Matrix.one_mul]
  refine weight_of_triangular (X := X.map φ) (Y := Y.map φ) (L := (Formalism.UG.cT (σ : E →+* E) Y * J).map φ)
    (T := (Formalism.UG.cT (σ : E →+* E) X * J).map φ) hd ?_ ?_ ?_ eB f (fun i j hij => hB hij) (fun i j hij => ?_) _ ?_
    (fun j => idemA_eq _ _ j) (fun j => ?_)
  · rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hY, Matrix.map_zero _ (map_zero _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' hij, map_zero]
  · have := adj 1
    rw [Matrix.mul_one, Formalism.UG.cT_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

    rw [← map_sum, sum_idemA, this, Matrix.map_mul]
  · refine (adj (single j j 1)).trans ?_
    congr 2
    ext a b
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp [Formalism.UG.cT, single, h1, h2]

end GlobalTheory.UAut.OppFlagWeight
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.UAut.NoLower

theorem abstract_no_lower {A : Type} [CommRing A] {n r : ℕ} (st : Matrix (Fin n) (Fin n) A →+ Matrix (Fin n) (Fin n) A)
    (u : Fin r → Matrix (Fin n) (Fin n) A) (X Y : Matrix (Fin n) (Fin r) A) (L T : Matrix (Fin r) (Fin n) A)
    (hu : ∀ j, u j = X * single j j (1 : A) * L) (hs : ∀ j, st (u j) = Y * single j j (1 : A) * T)
    (hLX : L * X = 1) (hTX : T * X = 0) (hTY : T * Y = 1) (d : Fin r → ℕ) (M : ℕ) (hd : ∀ j, d j < M)
    (x : Matrix (Fin n) (Fin n) A) (B C : Matrix (Fin r) (Fin r) A) (hB : ∀ i j, d j < d i → B i j = 0)
    (hC : ∀ i j, d i < d j → C i j = 0) (eB : x * X = X * B) (eC : T * x = C * T) :
    ∀ a b, wt d M a < wt d M b → fam st u a * x * fam st u b = 0 := by
  have e0 : fam st u none = 1 - (X * L + Y * T) := by
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs]
    simp only [hu, ← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  have e1 : ∀ j, fam st u (some (.inl j)) = X * single j j (1 : A) * L := hu
  have e2 : ∀ j, fam st u (some (.inr j)) = Y * single j j (1 : A) * T := hs
  have k0 : fam st u none * X = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLX, hTX]; simp
  have k1 : T * fam st u none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTY, hTX]; simp
  have l1 : ∀ (e : Matrix (Fin n) (Fin n) A) (j : Fin r), e * x * (X * single j j (1 : A) * L) =
      e * X * B * single j j (1 : A) * L := fun e j => by
    rw [Matrix.mul_assoc e X, ← eB]; simp only [Matrix.mul_assoc]
  have l2 : ∀ (e : Matrix (Fin n) (Fin n) A) (j : Fin r), (Y * single j j (1 : A) * T) * x * e =
      Y * single j j (1 : A) * C * (T * e) := fun e j => by
    rw [Matrix.mul_assoc _ T, eC]; simp only [Matrix.mul_assoc]
  have sm : ∀ (D : Matrix (Fin r) (Fin r) A) (i j : Fin r), D i j = 0 →
      single i i (1 : A) * D * single j j (1 : A) = 0 := fun D i j h => by
    rw [Matrix.single_mul_mul_single, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp at hab
  · rw [e1, l1, k0]; simp
  · have := hd j; simp [wt] at hab; omega
  · have := hd i; simp [wt] at hab; omega
  · have h := sm B i j (hB i j (by simp [wt] at hab; omega))
    rw [e1, e1, l1, Matrix.mul_assoc _ L, hLX, Matrix.mul_one, Matrix.mul_assoc X, Matrix.mul_assoc X, h]; simp
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, l2, k1]; simp
  · rw [e1, e2, l1, Matrix.mul_assoc _ T, hTX]; simp
  · have h := sm C i j (hC i j (by simp [wt] at hab; omega))
    rw [e2, e2, l2, ← Matrix.mul_assoc T, ← Matrix.mul_assoc T, hTY, Matrix.one_mul, ← Matrix.mul_assoc,
      Matrix.mul_assoc Y, Matrix.mul_assoc Y, h]; simp

theorem parFlag_no_lower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J X d, ∀ a b, wt d M a < wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y d M hd hXX _ hXY p hp
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hcm
  have cc : ∀ {m q : Type} (A : Matrix m q E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have eC := form_mul_of_mul_cols eB'
  rw [inv_inv] at eC
  have hLX : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hXY
    rwa [cT_mul, cT_mul, cc, cT_form hJ, cT_one, ← Matrix.mul_assoc] at this
  refine abstract_no_lower _ _ (adMat F X) (adMat F Y) (adMat F (cT (σ : E →+* E) Y * J))
    (adMat F (cT (σ : E →+* E) X * J)) (fun j => idemA_eq _ _ j) (fun j => ?_) ?_ ?_ ?_ d M hd _ B _
    (fun i j h => hB h) (fun i j h => ?_) eB eC
  · have s : cT (σ : E →+* E) (single j j (1 : E) : Matrix (Fin r) (Fin r) E) = single j j 1 := by
      rw [cT, Matrix.map_single, Matrix.transpose_single, map_one]
    have e : J⁻¹ * cT (σ : E →+* E) (X * single j j (1 : E) * (cT (σ : E →+* E) Y * J)) * J =
        Y * single j j (1 : E) * (cT (σ : E →+* E) X * J) := by
      rw [cT_mul, cT_mul, cT_mul, cc, cT_form hJ, s, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]
      simp only [Matrix.mul_assoc]
    rw [idemA, adjA_map, e]
    exact idemA_eq Y _ j
  · rw [adMat, adMat, ← Matrix.map_mul, hLX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [adMat, adMat, ← Matrix.map_mul, hXX, Matrix.map_zero _ (map_zero _)]
  · rw [adMat, adMat, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' h, map_zero]

end GlobalTheory.UAut.NoLower
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open ValuativeRel

namespace GlobalTheory.PrimFrameExist

theorem exists_gl_mul_isPrimFrame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : ℕ) (C : Type) [Fintype C] [DecidableEq C] (d : C → kˣ) (X : Matrix (Fin a) C k), X.rank = a →
    ∃ g₀ : GL (Fin a) k, IsPrimFrame (diagLat d) (g₀.val * X) := by
  intro k _ _ _ _ a C _ _ d X hX
  classical
  set Λ : Submodule 𝒪[k] (C → k) := diagLat d with hΛdef
  set V : Submodule k (C → k) := Submodule.span k (Set.range X.row) with hVdef
  set M : Submodule 𝒪[k] (C → k) := V.restrictScalars 𝒪[k] ⊓ Λ with hMdef
  have hΛfg : Λ.FG := (isLattice_diagLat d).fg
  haveI : IsNoetherian 𝒪[k] Λ := isNoetherian_of_fg_of_noetherian Λ hΛfg
  haveI : IsNoetherian 𝒪[k] M := isNoetherian_of_le inf_le_right
  haveI : Module.IsTorsionFree 𝒪[k] k := inferInstance
  haveI : Module.IsTorsionFree 𝒪[k] (C → k) := Module.IsTorsionFree.trans_faithfulSMul 𝒪[k] k (C → k)
  haveI : Module.IsTorsionFree 𝒪[k] M := inferInstance
  haveI : Module.Free 𝒪[k] M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex 𝒪[k] M
  let b : Module.Basis ι 𝒪[k] M := Module.Free.chooseBasis 𝒪[k] M
  let v : ι → (C → k) := fun i => (b i : C → k)
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2.1
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (b i).2.2
  have hrepr : ∀ y (hy : y ∈ M), y = ∑ i, ((b.repr ⟨y, hy⟩ i : 𝒪[k]) : k) • v i := by
    intro y hy
    have h := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
  have hli : LinearIndependent k v := by
    rw [← LinearIndependent.iff_fractionRing (R := 𝒪[k]) (K := k)]
    exact b.linearIndependent.map' M.subtype M.ker_subtype
  have hclear : ∀ x : C → k, ∃ r : 𝒪[k], r ≠ 0 ∧ (r : k) • x ∈ Λ := by
    intro x
    obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
      (fun j => x j / (d j : k))
    refine ⟨r, nonZeroDivisors.coe_ne_zero r, ?_⟩
    rw [hΛdef, mem_diagLat]
    intro j
    obtain ⟨s, hs⟩ := hr j
    rw [Algebra.smul_def] at hs
    have h1 : valuation k (algebraMap 𝒪[k] k r * (x j / d j)) ≤ 1 := by
      rw [← hs]; exact (Valuation.mem_integer_iff _ _).1 s.2
    have e : ((r : 𝒪[k]) : k) • x = fun l => (algebraMap 𝒪[k] k r * (x l / d l)) * d l := by
      funext l; simp only [Pi.smul_apply, smul_eq_mul]; rw [mul_assoc, div_mul_cancel₀ _ (d l).ne_zero]; rfl
    rw [e, map_mul]
    exact mul_le_of_le_one_left' h1
  have hli' : X.rank = Fintype.card (Fin a) ↔ LinearIndependent k X.row := by
    rw [rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, eq_comm]; rfl
  have hXli : LinearIndependent k X.row := hli'.1 (by simpa using hX)
  have hVle : V ≤ Submodule.span k (Set.range v) := by
    intro x hx
    obtain ⟨r, hr0, hr⟩ := hclear x
    have hrx : ((r : 𝒪[k]) : k) • x ∈ M := ⟨V.smul_mem _ hx, hr⟩
    have e := hrepr _ hrx
    have hr0' : ((r : 𝒪[k]) : k) ≠ 0 := fun h => hr0 (Subtype.ext h)
    have hx' : x = ((r : 𝒪[k]) : k)⁻¹ • (((r : 𝒪[k]) : k) • x) := (inv_smul_smul₀ hr0' x).symm
    rw [hx', e]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hspan : Submodule.span k (Set.range v) = V :=
    le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hvV i)) hVle
  have hcard : Fintype.card ι = a := by
    rw [← finrank_span_eq_card hli, hspan, hVdef, finrank_span_eq_card hXli, Fintype.card_fin]
  let e : Fin a ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let Y : Matrix (Fin a) C k := Matrix.of fun i => v (e i)
  have hYV : ∀ i, Y.row i ∈ V := fun i => hvV (e i)
  choose g hg using fun i => (Submodule.mem_span_range_iff_exists_fun k).1 (hYV i)
  have hYg : (Matrix.of g) * X = Y := by
    ext i l
    have h := congrFun (hg i) l
    rw [Finset.sum_apply] at h
    rw [Matrix.mul_apply]
    exact (Finset.sum_congr rfl fun j _ => rfl).trans h
  have hYli : LinearIndependent k Y.row := hli.comp e e.injective
  have hgli : LinearIndependent k (Matrix.of g).row := by
    refine LinearIndependent.of_comp (Matrix.vecMulLinear X) ?_
    convert hYli using 1
    funext i
    rw [← hYg]
    try rfl
  have hu : IsUnit (Matrix.of g) := Matrix.linearIndependent_rows_iff_isUnit.1 hgli
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hYg, isPrimFrame_iff]
  refine ⟨fun i => hvΛ (e i), fun c hc i => ?_⟩
  have hcV : c ᵥ* Y ∈ V := by
    rw [vecMul_eq_sum]; exact V.sum_mem fun i _ => V.smul_mem _ (hYV i)
  have hcM : c ᵥ* Y ∈ M := ⟨hcV, hc⟩
  have e1 := hrepr _ hcM
  have e2 : c ᵥ* Y = ∑ t, c (e.symm t) • v t := by
    rw [vecMul_eq_sum, ← e.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [e.symm_apply_apply]; rfl
  have h := Fintype.linearIndependent_iffₛ.1 hli (fun t => c (e.symm t))
    (fun t => ((b.repr ⟨_, hcM⟩ t : 𝒪[k]) : k)) (by rw [← e2, ← e1]) (e i)
  simp only [Equiv.symm_apply_apply] at h
  rw [h]
  exact (b.repr _ _).2

end GlobalTheory.PrimFrameExist
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

namespace GlobalTheory.RegSSClass

theorem nilpotent_eq_zero_of_commute_sep_alg {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  set f := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' N) := hc.map Matrix.toLinAlgEquiv'
  have hNl : IsNilpotent (Matrix.toLin' N) := hN.map Matrix.toLinAlgEquiv'
  obtain ⟨k, hk⟩ := hNl
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N) := fun μ v hv => by
    have h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩
    have hc' : Matrix.toLin' N v = c • v := (congrArg Subtype.val hc).symm
    have hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
    have h5 : c ^ k • v = 0 := by rw [← hpow, hk]; rfl
    have hc0 : c = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact pow_eq_zero_iff'.1 h |>.1
      · exact absurd h h0
    rw [LinearMap.mem_ker, hc', hc0, zero_smul]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top] at h3
  exact Matrix.toLin'.injective (by rw [h3, map_zero])

theorem nilpotent_eq_zero_of_commute_sep {K : Type} [Field K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  have h := nilpotent_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K)
    (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K)))
    (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
    (hc.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem isSemisimple_of_charpoly_separable {K : Type} [Field K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly.Separable) : Module.End.IsSemisimple (Matrix.toLin' A) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := A.charpoly) h.squarefree ?_
  have := LinearMap.aeval_self_charpoly (Matrix.toLin' A)
  rwa [Matrix.charpoly_toLin'] at this

theorem charpoly_eq_of_isConj {K : Type} [Field K] {n : ℕ} {G : Subgroup (GL (Fin n) K)} {a b : G}
    (h : IsConj a b) : b.1.1.charpoly = a.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  simpa using Matrix.charpoly_units_conj c.1 a.1.1

end GlobalTheory.RegSSClass

open GlobalTheory.RegSSClass in
theorem GlobalTheory.regSS_conjClass_isSSClass : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ : GF V | IsConj γ δ} := by
  intro D V γ hγ
  have hs : γ.1.1.charpoly.Separable := hγ
  refine ⟨γ, isSemisimple_of_charpoly_separable hs, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨x, ⟨isSemisimple_of_charpoly_separable ?_, Commute.refl _, by simp⟩, hx⟩
    rw [charpoly_eq_of_isConj hx]; exact hs
  · rintro ⟨s, ⟨_, hcomm, hnil⟩, hconj⟩
    have hss : s.1.1.charpoly.Separable := by rw [charpoly_eq_of_isConj hconj]; exact hs
    have h0 := nilpotent_eq_zero_of_commute_sep hss hnil (hcomm.symm.sub_right (Commute.refl _))
    have hxs : x = s := Subtype.ext (Units.ext (sub_eq_zero.1 h0))
    rw [hxs]; exact hconj
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

theorem vacuum_int_root_of_unity : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ),
    e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (r : GA D a), r ∈ intG D a →
    ∃ c : ℂ, (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧ W.Om r 1 e0 = c • e0 := by
  intro D δ crv a d e0 he W r hr
  obtain ⟨x, x', hx, hx', h⟩ := (GlobalTheory.NormSum.VacInt.vacuum_eigen D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ crv a d e0 he W).2.1
    r hr 1 (one_mem _)
  obtain ⟨m, hm, hxm⟩ := (GlobalTheory.T.unitaryHeckeCharacter_values D d W.chV' x).2.1 hx
  obtain ⟨m', hm', hxm'⟩ := (GlobalTheory.T.unitaryHeckeCharacter_values D a W.chV x').2.1 hx'
  refine ⟨_, ⟨m * m', Nat.mul_pos hm hm', ?_⟩, h⟩
  rw [← Units.val_pow_eq_pow_val, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm W.ep, mul_comm W.ep', zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, mul_comm m m', pow_mul, hxm', one_pow, one_zpow,
    mul_comm m' m, pow_mul, hxm, one_pow, one_zpow, one_mul, Units.val_one]

end GlobalTheory.FunObj.StdDatum
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.iSup_eEp3_eq_whole_space_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → (⨆ p, R.EEp3 p) = ⊤ := by
  first | exact @GlobalTheory.SpanParts.iSup_rows_eigenparts_principal_level_eq_top | exact GlobalTheory.SpanParts.iSup_rows_eigenparts_principal_level_eq_top | (intros; apply GlobalTheory.SpanParts.iSup_rows_eigenparts_principal_level_eq_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_rational_frameCoords_of_mem_torusLattice : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank), ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) := by
  first | exact @GlobalTheory.ThetaLawLat.mem_La_frame | exact GlobalTheory.ThetaLawLat.mem_La_frame | (intros; apply GlobalTheory.ThetaLawLat.mem_La_frame <;> assumption)
end
