module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle149
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rationalAdelicPoint_of_unitary_baseSpace : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  first | exact @GlobalTheory.Core.Mi.exists_GQ_of_unitary0 | exact GlobalTheory.Core.Mi.exists_GQ_of_unitary0 | (intros; apply GlobalTheory.Core.Mi.exists_GQ_of_unitary0 <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rationalRepLevelDecomposition_finiteUnitary : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (g : GA D (D.sp.X 0)), ∃ p, GlobalTheory.AdForm.IsDec F.cls0.lev F.cls0.y (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p := by
  first | exact @GlobalTheory.Core.Mi.exists_isDec_finM | exact GlobalTheory.Core.Mi.exists_isDec_finM | (intros; apply GlobalTheory.Core.Mi.exists_isDec_finM <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

theorem mul_mul_mul_of_gram {a b c e n : Type*} [Fintype b] [Fintype c] [Fintype e] {R : Type*} [Semiring R]
    {A : Matrix a b R} {G : Matrix b c R} {M : Matrix c e R} {C : Matrix a e R} (h : A * G * M = C)
    (N : Matrix e n R) : A * (G * (M * N)) = C * N := by
  rw [← h]; simp only [Matrix.mul_assoc]

def selFirst (D : D7) (σ : ℕ) : Matrix (Fin σ) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun i j => if j = i.castSucc then 1 else 0

def lastE (D : D7) (σ : ℕ) : Fin (σ + 1) → D.host.E := Pi.single (Fin.last σ) 1

def besselRationalBasePointMatrix (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem ell_succ_eq : ell D (σ + 1) = fun i => incA D (lastE D σ i) := by
  funext i
  by_cases h : i = Fin.last σ
  · subst h
    show (if (Fin.last σ).1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ (Fin.last σ))
    rw [if_pos (by rw [Fin.val_last]), lastE, Pi.single_eq_same, map_one]
  · have h' : ¬ (i.1 + 1 = σ + 1) := fun h' => h (Fin.ext (by rw [Fin.val_last]; omega))
    show (if i.1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ i)
    rw [if_neg h', lastE, Pi.single_eq_of_ne h, map_zero]

theorem zl_eq_rat (B : BesLev D σ) : zl B = rat (vecMulVec B.ζ (lastE D σ)) := by
  funext i j
  simp [zl, zEll, rat, ratV, vecMulVec, ell_succ_eq]

theorem rat_x0Rat (B : BesLev D σ) : rat (besselRationalBasePointMatrix B) = x0 B := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_x0Rat (B : BesLev D σ) :
    (besselRationalBasePointMatrix B)ᴴ * B.V.gram * besselRationalBasePointMatrix B =
      (vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ) := by
  have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.ee
  have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.i₀e
  have hX0 : B.d.eᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
  have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.iso
  have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.o.isoB
  have hz : vecMulVec (vecB B.o B.ζ) (lastE D σ) = B.o.iB * vecMulVec B.ζ (lastE D σ) := by
    rw [vecB, mul_vecMulVec]
  rw [besselRationalBasePointMatrix, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gramSkew_x0Rat (B : BesLev D σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat (besselRationalBasePointMatrix B) : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zl B) := by
  rw [zl_eq_rat, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, gram_rat _ (gram_x0Rat B), gram_rat B.L rfl]

theorem linearIndependent_x0Rat (B : BesLev D σ) : LinearIndependent D.host.E (besselRationalBasePointMatrix B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : besselRationalBasePointMatrix B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * besselRationalBasePointMatrix B = selFirst D σ := by
    rw [besselRationalBasePointMatrix, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_x0Rat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec]
      at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 B.line.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem exists_rationalOrbit_point_eq_besselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x ∈ orb B, (rat x : Mx D B.V.rank (σ + 1)) = x0 B :=
  fun _ _ B => ⟨besselRationalBasePointMatrix B, ⟨linearIndependent_x0Rat B, gramSkew_x0Rat B⟩, rat_x0Rat B⟩

end GlobalTheory.Unf.FB

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

def x0Mat (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (B.d.e k) ((B.d.i₀ *ᵥ vecB B.o B.ζ) k)

theorem rat_x0Mat (B : BesLev D σ) : rat (x0Mat B) = x0 B := by
  refine Matrix.ext fun k j => ?_
  refine Fin.lastCases ?_ (fun b => ?_) j

  · simp [x0Mat, x0, xLast, rat, HypDec.j0, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  · simp [x0Mat, x0, xLast, rat, HypDec.jX]

def besselBasePointLevelNorm (B : BesLev D σ) : D.host.E := star (vecB B.o B.ζ) ⬝ᵥ B.V₀.gram *ᵥ vecB B.o B.ζ

theorem besselBasePointLevelNorm_eq_gram_form (B : BesLev D σ) : besselBasePointLevelNorm B = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
  rw [besselBasePointLevelNorm, vecB, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    B.o.isoB]

theorem besselBasePointLevelNorm_ne_zero (B : BesLev D σ) : besselBasePointLevelNorm B ≠ 0 := by
  rw [besselBasePointLevelNorm_eq_gram_form]; exact B.line.2

def besselBasePointLeftInverse (B : BesLev D σ) : Matrix (Fin (σ + 1)) (Fin B.V.rank) D.host.E :=
  Matrix.of (Fin.snoc (α := fun _ => Fin B.V.rank → D.host.E) (fun a => B.d.qX a)
    ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))))

theorem besselLevelDatum_qX_dot_e_eq_one (B : BesLev D σ) : B.d.qX * B.d.e = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.pX_jX)

theorem wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero (B : BesLev D σ) : B.d.qX * B.d.i₀ = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pX_j0)

theorem wittDecomposition_projectionZero_mul_e_eq_zero (B : BesLev D σ) : B.d.q0 * B.d.e = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.p0_jX)

theorem wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one (B : BesLev D σ) : B.d.q0 * B.d.i₀ = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.p0_j0)

theorem besselBasePointLeftInverse_mul_snocMatrix (B : BesLev D σ) : besselBasePointLeftInverse B * x0Mat B = 1 := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · have h : ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))) ⬝ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = 1 := by
      rw [smul_dotProduct, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc, wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one, Matrix.mul_one,
        ← Matrix.dotProduct_mulVec, smul_eq_mul]
      exact inv_mul_cancel₀ (besselBasePointLevelNorm_ne_zero B)
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last]
    exact h
  · have h : ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))) ᵥ* B.d.e = 0 := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc, wittDecomposition_projectionZero_mul_e_eq_zero, Matrix.mul_zero, Matrix.vecMul_zero, smul_zero]
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last b).symm]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
    exact congrFun h b
  · have h : B.d.qX *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = 0 := by
      rw [Matrix.mulVec_mulVec, wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero, Matrix.zero_mulVec]
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a)]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
    exact congrFun h a
  · rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Fin.castSucc_inj]
    rw [← Matrix.one_apply (α := D.host.E) (i := a) (j := b), ← besselLevelDatum_qX_dot_e_eq_one B, Matrix.mul_apply]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_castSucc]

theorem fourierBesselBasePoint_rational_with_rational_leftInverse : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ),
    (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ x0 B = 1) ∧ x0 B ∈ ratMx D B.V.rank (σ + 1) := fun _ _ B =>
  ⟨⟨rat (besselBasePointLeftInverse B), rat_mem _, by rw [← rat_x0Mat, ← rat_mul, besselBasePointLeftInverse_mul_snocMatrix, rat_one]⟩, rat_x0Mat B ▸ rat_mem _⟩

end GlobalTheory.Unf.FB
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SuperposT

theorem symplOH_zero_left {D : D7} {S T : HSp D} (y : WO S T) : symplOH S T 0 y = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 y
  rw [add_zero] at h
  linear_combination -h

theorem symplOH_zero_right {D : D7} {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0
  rw [add_zero] at h
  linear_combination -h

theorem psi_neg_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (s : AF D.host.F) : ψ (-s) * ψ s = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem symplOH_resT_symm {D : D7} {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u u' : WO S A) (v v' : WO S B) :
    symplOH S T ((o.resT S).symm (u, v)) ((o.resT S).symm (u', v')) = symplOH S A u u' + symplOH S B v v' := by
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem superpos_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ S A fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ := by
  intro D ψ hψ T A B S o F hF Ω _ μ k a hk ha
  haveI : BorelSpace (Mx D B.rank S.rank) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D A.rank S.rank
  haveI : FirstCountableTopology (WO S A) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  set e := o.resT S with he
  have hsplit : ∀ (u u' : WO S A) (v : WO S B), e.symm (u + u', v) = e.symm (u, v) + e.symm (u', 0) := by
    intro u u' v
    rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
  have hmeas : ∀ (F' : WO S T → ℂ), Continuous F' → ∀ (c : WO S T) (u : WO S A),
      AEStronglyMeasurable (fun ξ => F' (e.symm (u, k ξ) + c)) μ := by
    intro F' hF' c u
    exact ((hF'.comp (((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).add
      continuous_const)).measurable.comp hk).aestronglyMeasurable

  let φ : WO S A →+ WO S T := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (WO S A) (WO S B))
  have hφ : ∀ u, φ u = e.symm (u, 0) := fun u => rfl
  have hφc : Continuous φ := (o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)
  have hφmap : ∀ (R : Type) [CommRing R] (f : Formalism.L2.Theta.AE D →+* R) (u : WO S A), u.map f = 0 → (φ u).map f = 0 := by
    intro R _ f u hu
    rw [hφ, he, o.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.map_mul, hu, Matrix.mul_zero]
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  ·
    have hr : e.symm (ratW A S γ, 0) = ratW T S (o.iA * γ) := by
      rw [he, o.resT_symm_apply, Matrix.mul_zero, add_zero]
      exact (rat_mul _ _).symm
    have h1 : ∀ ξ, F (e.symm (ratW A S γ + u, k ξ)) =
        ψ (-(symplOH S A (ratW A S γ) u)) * F (e.symm (u, k ξ)) := by
      intro ξ
      rw [add_comm (ratW A S γ) u, hsplit, add_comm, hr, hF.quasi, ← hr, symplOH_resT_symm, symplOH_zero_left, add_zero]
    simp_rw [h1]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    ring
  ·
    obtain ⟨U, hU, hl⟩ := hF.level
    refine ⟨U.comap φ, hU.preimage hφc, fun u hu h0 => ?_⟩
    have hl' := hl (φ u) hu (hφmap _ _ u h0)
    funext w
    simp only [heisO]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    have h2 := congrFun hl' (e.symm (w, k ξ))
    simp only [heisO] at h2
    rw [hφ, symplOH_resT_symm, symplOH_zero_right, add_zero, ← hsplit] at h2
    rw [mul_left_comm, h2]
  ·
    refine continuous_of_dominated (bound := fun ξ => ‖a ξ‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_
    · have := hmeas F hF.cont 0 u
      simp only [add_zero] at this
      exact ha.aestronglyMeasurable.mul this
    · exact Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · exact Filter.Eventually.of_forall fun ξ => continuous_const.mul
        (hF.cont.comp ((o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)))
  ·
    intro n L hLc hL0 w
    obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L' : (Fin n → ℝ) →+ WO S T := φ.comp L
    have hL'c : Continuous L' := hφc.comp hLc
    have hL'0 : ∀ t, (L' t).map (finPart D) = 0 := fun t => hφmap _ _ _ (hL0 t)
    let M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S :=
      ((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)
    let N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW A S :=
      ((GlobalTheory.FockCompare.piW θ A S).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ A S).comp hLc)
    have hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t) := fun t => (h.iota_pi (hL'0 t)).symm
    have hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ A S (N t) := fun t => (h.iota_pi (hL0 t)).symm
    let om := LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO S A (GlobalTheory.FockCompare.piW θ A S w))
    have key : ∀ t, (∫ x, a x * F (e.symm (w + L t, k x)) ∂μ) =
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ := by
      intro t
      have hph : ψ (-symplOH S A w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) := by
        have e1 : -symplOH S A w (L t) = symplOH S A w (L (-t)) := by
          rw [map_neg]
          have := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := A) w (L t) (-L t)
          rw [add_neg_cancel, symplOH_zero_right] at this
          linear_combination this
        rw [e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]
        rfl
      rw [← hph, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [heisO]
      rw [← hM, hsplit]
      have hs : symplOH S T (e.symm (w, k x)) (L' t) = symplOH S A w (L t) := by
        show symplOH S T (e.symm (w, k x)) (e.symm (L t, 0)) = _
        rw [symplOH_resT_symm, symplOH_zero_right, add_zero]
      rw [hs]
      change a x * F (_ + L' t) = ψ (-symplOH S A w (L t)) * (a x * (ψ (symplOH S A w (L t)) * F (_ + L' t)))
      have := psi_neg_mul ψ (symplOH S A w (L t))
      linear_combination (-(a x * F (e.symm (w, k x) + L' t))) * this
    have hf : (fun t => (fun u => ∫ x, a x * F (e.symm (u, k x)) ∂μ) (w + L t)) = fun t =>
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ :=
      funext key
    rw [hf]
    refine ContDiff.mul ?_ ((GlobalTheory.SuperposSmooth.main D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)
    · exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (om.contDiff.comp (N.contDiff.comp contDiff_neg))))
    · exact ((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).measurable.comp hk

end GlobalTheory.SuperposT

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar


theorem _root_.GlobalTheory.T.exists_levi_preimage_of_fix_isotropic_frames : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S), mt S g ⬝ d.jX = d.jX → mt S g ⬝ d.jY = d.jY → ∃ b : GA D S₀, d.emb0 b = g := by
  first | exact @GlobalTheory.MixModel.HypDec.exists_emb0_eq_of_fix_jX_jY | exact GlobalTheory.MixModel.HypDec.exists_emb0_eq_of_fix_jX_jY | (intros; apply GlobalTheory.MixModel.HypDec.exists_emb0_eq_of_fix_jX_jY <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_congruenceModulus_idelicCharacter_trivial : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitAll.char_trivial_modSet | exact GlobalTheory.HeckeSplitAll.char_trivial_modSet | (intros; apply GlobalTheory.HeckeSplitAll.char_trivial_modSet <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_finPartOne_mul_inv_mem_heckeSplitCongruence : ∀ (D : D7) (N : ℕ), 0 < N → ∀ x : (AE D)ˣ, ∃ z : (AE D)ˣ, finPart D (z : AE D) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitAll.grpH D N := by
  first | exact @GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem | exact GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem | (intros; apply GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.mem_closure_heckeSplitCongruence_of_finPart_one : ∀ (D : D7) (N : ℕ), 0 < N → ∀ z : (AE D)ˣ, finPart D (z : AE D) = 1 → z ∈ closure (GlobalTheory.HeckeSplitAll.grpH D N : Set (AE D)ˣ) := by
  first | exact @GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one | exact GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one | (intros; apply GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem piU_rieszJ : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (s : X.B.I.Ginf), s ∈ Hinf X u → ∀ z z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt s) z z' → X.piU u s (rieszJ tr z) = rieszJ tr z' := by
  intro D X u F tr s hs z z' hz
  have hrep := X.piU_rep u
  have hS := hinf_le_sinf X u s hs
  have hSi := hinf_le_sinf X u _ ((Hinf X u).inv_mem hs)
  refine ext_inner_left ℂ fun η => ?_
  have hη : X.piU u s (X.piU u s⁻¹ η) = η := by
    rw [← ContinuousLinearMap.mul_apply, ← hrep.2.1 _ hS _ hSi, mul_inv_cancel, hrep.1]
    rfl
  rw [← hη, hrep.2.2.1 s hS, inner_rieszJ, inner_rieszJ, tr.J_eqv s hs _ z' z hz]

end GlobalTheory.Core.Mi
end
