module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle167
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def x0Mat (B : BesL D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (B.d.e k) ((B.d.i₀ *ᵥ vecB B.o B.ζ) k)

theorem rat_x0Mat (B : BesL D σ) : rat (x0Mat B) = xLast B.d (vecB B.o B.ζ) := by
  refine Matrix.ext fun k j => ?_
  refine Fin.lastCases ?_ (fun b => ?_) j

  · simp [x0Mat, xLast, rat, HypDec.j0, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  · simp [x0Mat, xLast, rat, HypDec.jX]

def besselBasePointLevelNorm (B : BesL D σ) : D.host.E := star (vecB B.o B.ζ) ⬝ᵥ B.V₀.gram *ᵥ vecB B.o B.ζ

theorem besselBasePointLevelNorm_eq_gram_form (B : BesL D σ) : besselBasePointLevelNorm B = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
  rw [besselBasePointLevelNorm, vecB, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    B.o.isoB]

theorem besselBasePointLevelNorm_ne_zero (B : BesL D σ) : besselBasePointLevelNorm B ≠ 0 := by
  rw [besselBasePointLevelNorm_eq_gram_form]; exact B.line.2

def besselBasePointLeftInverse (B : BesL D σ) : Matrix (Fin (σ + 1)) (Fin B.V.rank) D.host.E :=
  Matrix.of (Fin.snoc (α := fun _ => Fin B.V.rank → D.host.E) (fun a => B.d.qX a)
    ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))))

theorem besselLevelDatum_qX_dot_e_eq_one (B : BesL D σ) : B.d.qX * B.d.e = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.pX_jX)

theorem wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero (B : BesL D σ) : B.d.qX * B.d.i₀ = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pX_j0)

theorem wittDecomposition_projectionZero_mul_e_eq_zero (B : BesL D σ) : B.d.q0 * B.d.e = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.p0_jX)

theorem wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one (B : BesL D σ) : B.d.q0 * B.d.i₀ = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.p0_j0)

theorem besselBasePointLeftInverse_mul_snocMatrix (B : BesL D σ) : besselBasePointLeftInverse B * x0Mat B = 1 := by
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

theorem xLast_rat_leftInv : ∀ (D : D7) (σ : ℕ) (B : BesL D σ),
    (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ xLast B.d (vecB B.o B.ζ) = 1) ∧ xLast B.d (vecB B.o B.ζ) ∈ ratMx D B.V.rank (σ + 1) := fun _ _ B =>
  ⟨⟨rat (besselBasePointLeftInverse B), rat_mem _, by rw [← rat_x0Mat, ← rat_mul, besselBasePointLeftInverse_mul_snocMatrix, rat_one]⟩, rat_x0Mat B ▸ rat_mem _⟩

end GlobalTheory.Asc.FBL
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

noncomputable section

namespace GlobalTheory.Asc

variable {D : D7}

theorem symplOH_swap {S T : HSp D} (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  have h := symplOH_self (S := S) (T := T) (x + y)
  rw [symplOH_add_left, symplOH_add_right, symplOH_add_right, symplOH_self, symplOH_self] at h
  linear_combination h

theorem symplO_swap {S T : HSp D} (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap]; ring

theorem psi_symplO_swap (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x y : WO S T) :
    ψ (symplO S T y x) = 1 ↔ ψ (symplO S T x y) = 1 := by
  rw [symplO_swap, AddChar.map_neg_eq_inv, inv_eq_one]

theorem heisO_comm (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a b : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T a (heisO ψ S T b f) = ψ (symplO S T a b) • heisO ψ S T b (heisO ψ S T a f) := by
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm b a, ← AddChar.map_add_eq_mul,
    GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap a b]
  have e : symplOH S T a b + symplOH S T a b + -symplOH S T a b = symplOH S T a b := by ring
  rw [e]

theorem annVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)),
    (∀ f, VacG ψ S T Γ f → ∀ w ∈ Ann ψ S T Γ, VacG ψ S T Γ (heisO ψ S T w f)) ∧
    (∀ w : WO S T, (∀ u ∈ Γ, u.map (infPart D) = 0) → w.map (finPart D) = 0 → w ∈ Ann ψ S T Γ) ∧
    ∀ (v : VolM D T.rank S.rank) f f₀, VacG ψ S T Γ f → VacG ψ S T Γ f₀ → ∀ w, w ∉ Ann ψ S T Γ →
      thPair v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
  intro D ψ hψ S T Γ
  refine ⟨fun f hf w hw => ?_, fun w hΓ hw => ?_, fun v f f₀ hf hf₀ w hw => ?_⟩
  · refine ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf.1 w, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · show heisO ψ S T (2 • u) (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.1 u hu, (psi_symplO_swap ψ _ _).2 (hw.1 u hu), one_smul]
    · show heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.2 e he u hu hh, (psi_symplO_swap ψ _ _).2 (hw.2 e he u hu hh), one_smul]
  · have key : ∀ u ∈ Γ, symplO S T w u = 0 := fun u hu => by
      rw [GlobalTheory.ThetaSquare.symplO_eq, (symplOH_fin_real (hΓ u hu) hw).2, add_zero]
    refine ⟨fun u hu => ?_, fun e _ u hu _ => by rw [key u hu, AddChar.map_zero_eq_one]⟩
    rw [key _ (Γ.nsmul_mem hu 2), AddChar.map_zero_eq_one]
  · obtain ⟨hμ, h𝓕, -⟩ := v.covol
    have hex : ∃ u, heisO ψ S T u f = f ∧ heisO ψ S T u f₀ = f₀ ∧ ψ (symplO S T w u) ≠ 1 := by
      by_contra hno
      push_neg at hno
      exact hw ⟨fun u hu => hno _ (hf.2.1 u hu) (hf₀.2.1 u hu),
        fun e he u hu hh => hno _ (hf.2.2 e he u hu hh) (hf₀.2.2 e he u hu hh)⟩
    obtain ⟨u, hu, hu₀, hc⟩ := hex
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀.1 w
    have e1 := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf.1 hg u
    rw [hu, heisO_comm, hu₀] at e1
    have e2 : GlobalTheory.Ker.ipO v.μ v.𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) =
        starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) := by
      unfold GlobalTheory.Ker.ipO
      rw [← integral_const_mul]
      congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
    have hc' : starRingEnd ℂ (ψ (symplO S T u w)) ≠ 1 := by
      intro h
      apply hc
      have h2 := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, map_one] at h2
      exact (psi_symplO_swap ψ _ _).1 h2
    rw [e2] at e1
    show GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0
    have h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
      linear_combination e1
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc')

end GlobalTheory.Asc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct Matrix GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LinkInvTheta

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem map_starAdj_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (hφ : ∀ z, φ z = 0 → φ (cA D z) = 0)
    (L S : HSp D) {x : WO L S} (hx : x.map φ = 0) : (starAdj L S x).map φ = 0 := by
  have h1 : (adj x).map φ = 0 := by
    funext i j
    exact hφ (x j i) (congrFun (congrFun hx j) i)
  have h2 := map_mul_eq_zero_right φ (giA L) (map_mul_eq_zero_left φ h1 (gA S))
  funext i j
  have h3 : φ ((giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0 := congrFun (congrFun h2 i) j
  show φ (incA D D.host.xi0 * (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0
  rw [map_mul, h3, mul_zero]

theorem continuous_starAdj (L S : HSp D) : Continuous (starAdj L S) := by
  have h1 : Continuous fun x : WO L S => (adj x ⬝ gA S : Mx D L.rank S.rank) :=
    continuous_adj.matrix_mul continuous_const
  have h2 : Continuous fun x : WO L S => (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) :=
    continuous_const.matrix_mul h1
  exact h2.const_smul (incA D D.host.xi0)

theorem starAdj_mem (L S : HSp D) {x : WO L S} (hx : x ∈ ratMx D S.rank L.rank) :
    starAdj L S x ∈ ratMx D L.rank S.rank := by
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hx
  rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
  exact rat_mem _

theorem lnk_simil {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Lnk L ζ L' ζ') : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

theorem link_inv_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  intro D ψ hψ L L' S ζ ζ' hL hL' l
  have hτ := lnk_simil hL' l
  refine ⟨hτ, fun Φ₀ hΦ => ?_⟩
  have hτ' : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hτ
  obtain ⟨hadd, -, -, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L' S l.τ 1 hτ' (l.κ S) (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (l.κ S w) (l.κ S w') = -symplOH S L' w w' := fun w w' => by
    unfold symplOH; rw [hsym]; push_cast; ring
  have hτ0 : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : ζ = 0 := neg_eq_zero.mp e.symm
    apply hL.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one hL.1 hL'.1 l.τ hτ0
  let g : WO L S → WO S L' := fun x => (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x
  have hgk : ∀ w, g (l.κ S w) = w := by
    intro w
    show (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S (l.κ S w) = w
    rw [Lnk.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  have hkg : ∀ x, l.κ S (g x) = x := by
    intro x
    show l.κ S ((rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x) = x
    rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]
  have gadd : ∀ x y, g (x + y) = g x + g y := fun x y => by
    conv_lhs => rw [← hkg x, ← hkg y, ← hadd, hgk]
  have gH : ∀ x y, symplOH S L' (g x) (g y) = -symplOH L S x y := fun x y => by
    conv_rhs => rw [← hkg x, ← hkg y, hH, neg_neg]
  have gcont : Continuous g := continuous_const.matrix_mul (continuous_starAdj L S)
  have grat : ∀ x ∈ ratMx D S.rank L.rank, g x ∈ ratMx D L'.rank S.rank := fun x hx =>
    ratMx_mul (rat_mem σ) (starAdj_mem L S hx)
  have gfin : ∀ x : WO L S, x.map (finPart D) = 0 → (g x).map (finPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (finPart D) _
      (map_starAdj_eq_zero (finPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.finPart_conj, hz, map_zero]) L S h)
  have ginf : ∀ x : WO L S, x.map (infPart D) = 0 → (g x).map (infPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (infPart D) _
      (map_starAdj_eq_zero (infPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.infPart_conj, hz, map_zero]) L S h)
  let A : WO L S →+ WO S L' := AddMonoidHom.mk' g gadd
  refine ⟨fun x => star (Φ₀ (g x)), ⟨fun γ x => ?_, ?_, continuous_star.comp (hΦ.cont.comp gcont), fun k M h1 h2 x => ?_⟩, ?_⟩
  · obtain ⟨γ', hγ'⟩ := grat (ratW S L γ) ⟨γ, rfl⟩
    have e : g (ratW S L γ) = ratW L' S γ' := hγ'.symm
    show star (Φ₀ (g (ratW S L γ + x))) = ψ (-(symplOH L S (ratW S L γ) x)) * star (Φ₀ (g x))
    rw [gadd, e, hΦ.quasi, star_mul', star_psi hψ, ← e, gH, neg_neg]
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U.comap A, hU.preimage gcont, fun u hu h0 => ?_⟩
    funext x
    have e := congrFun (h _ hu (ginf u h0)) (g x)
    unfold heisO at e ⊢
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = star (Φ₀ (g x))
    rw [← e, star_mul', star_psi hψ]
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = ψ (-symplOH S L' (g x) (g u)) * star (Φ₀ (g x + g u))
    rw [gH, neg_neg, gadd]
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => gfin (M t) (h2 t)
    have := hΦ.smooth k (A.comp M) (gcont.comp h1) h3 (g x)
    have heq : (fun t => Φ₀ (g (x + M t))) = fun t => Φ₀ (g x + A (M t)) :=
      funext fun t => congrArg Φ₀ (gadd x (M t))
    have h4 := (congrArg (ContDiff ℝ _) heq).mpr this
    exact Complex.conjCLE.contDiff.comp h4
  · funext w
    show Φ₀ w = star (star (Φ₀ (g (l.κ S w))))
    rw [hgk, star_star]
end GlobalTheory.LinkInvTheta
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBx

open GlobalTheory.Unf.FB (mul_mul_mul_of_gram selFirst lastE ell_succ_eq)

variable {D : D7} {σ : ℕ}

def xRat (B : BesL D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem zEll_eq_rat (B : BesL D σ) : zEll B.L (σ + 1) B.ζ = rat (vecMulVec B.ζ (lastE D σ)) := by
  funext i j
  simp [zEll, rat, ratV, vecMulVec, ell_succ_eq]

theorem rat_xRat (B : BesL D σ) : rat (xRat B) = xLast B.d (vecB B.o B.ζ) := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [xRat, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [xRat, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_xRat (B : BesL D σ) :
    (xRat B)ᴴ * B.V.gram * xRat B =
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
  rw [xRat, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gramSkew_xRat (B : BesL D σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat (xRat B) : Mx D B.V.rank (σ + 1)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ) := by
  rw [zEll_eq_rat, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, gram_rat _ (gram_xRat B), gram_rat B.L rfl]

theorem linearIndependent_xRat (B : BesL D σ) : LinearIndependent D.host.E (xRat B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : xRat B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * xRat B = selFirst D σ := by
    rw [xRat, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_xRat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
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

theorem exists_rat_eq_xLast : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x ∈ {x : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E |
    LinearIndependent D.host.E x.transpose ∧ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ)}, (rat x : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) :=
  fun _ _ B => ⟨xRat B, ⟨linearIndependent_xRat B, gramSkew_xRat B⟩, rat_xRat B⟩

end GlobalTheory.Asc.FBx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem _root_.GlobalTheory.T.thetaTriple_polynomialFock_stable_mul_trace_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (q : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F),
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')) x q : ℂ) * f x := by
  first | exact @GlobalTheory.PolMul.pol_mul_pairInf | exact GlobalTheory.PolMul.pol_mul_pairInf | (intros; apply GlobalTheory.PolMul.pol_mul_pairInf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem _root_.GlobalTheory.T.exists_complexStructure_gaussVacuum_fockEquations : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ f₀ : SInf F (Fin a × Fin (a + a')), G.M.IsGauss B.ψ B.emb f₀ →
    ∃ J₀ : ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ ∀ w x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a'))) (J₀ w) ⇑f₀ x =
        Complex.I * GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a'))) w ⇑f₀ x := by
  first | exact @GlobalTheory.GaussFockJ.exists_complex_structure | exact GlobalTheory.GaussFockJ.exists_complex_structure | (intros; apply GlobalTheory.GaussFockJ.exists_complex_structure <;> assumption)
end
