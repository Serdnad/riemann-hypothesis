module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorsReframeSource
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle253
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unramifiedQuadraticCharSign_split_eq_one_inert_eq_neg : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → quadSign D v = 1) ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) := by
  first | exact @GlobalTheory.QuadSignLocal.quadSign_split_inert | exact GlobalTheory.QuadSignLocal.quadSign_split_inert | (intros; apply GlobalTheory.QuadSignLocal.quadSign_split_inert <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.ThetaCarry

theorem continuous_reW {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b : WO (reS S b) T → WO S T) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun x : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D)))

theorem reW_ratW {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    reW S T b (ratW T (reS S b) γ) = ratW T S (γ * frPinv S b) := by
  unfold reW ratW
  rw [Matrix.map_mul]
  rfl

theorem reW_map_inf {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) {u : WO (reS S b) T}
    (hu : u.map (infPart D) = 0) : (reW S T b u).map (infPart D) = 0 := by
  refine (Matrix.map_mul (L := (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u))
    (M := (frPinv S b).map (incA D)) (f := infPart D)).trans ?_
  rw [show (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u).map (infPart D) = 0 from hu, Matrix.zero_mul]

theorem reW_map_fin {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) {u : WO (reS S b) T}
    (hu : u.map (finPart D) = 0) : (reW S T b u).map (finPart D) = 0 := by
  refine (Matrix.map_mul (L := (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u))
    (M := (frPinv S b).map (incA D)) (f := finPart D)).trans ?_
  rw [show (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u).map (finPart D) = 0 from hu, Matrix.zero_mul]

theorem isThetaFunO_reF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := by
  intro D ψ S T b hs f hf
  have hsH : ∀ x y : WO (reS S b) T, symplOH (reS S b) T x y = symplOH S T (reW S T b x) (reW S T b y) := by
    intro x y
    unfold symplOH
    rw [hs]
  have hc := continuous_reW S T b
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hc, fun k L h1 h2 w => ?_⟩
  · have e := reW_ratW S T b γ
    rw [reF_apply, reF_apply, reW_add, hsH]
    erw [e]
    exact hf.quasi _ _
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap (reWHom S T b), hU.preimage hc, fun u hu h0 => ?_⟩
    rw [heisO_reF S T b ψ hs u f, h (reW S T b u) hu (reW_map_inf S T b h0)]
  · have := hf.smooth k ((reWHom S T b).comp L) (hc.comp h1) (fun t => reW_map_fin S T b (h2 t)) (reW S T b w)
    simp only [reF_apply, reW_add]
    exact this

end GlobalTheory.AdSpan.ReVec.ThetaCarry

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.Sympl

theorem quad_sum_eq_trace {A : Type} [CommRing A] {m n : ℕ} (H : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b * y c b * G c d * x d a = Matrix.trace (H * (yᵀ * (G * x))) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem trace_change {A : Type} [CommRing A] {m n : ℕ} (H Q Q' : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin m) (Fin m) A) (x y : Matrix (Fin m) (Fin n) A) :
    Matrix.trace ((Q * (H * Q'ᵀ)) * (yᵀ * (G * x))) = Matrix.trace (H * ((y * Q')ᵀ * (G * (x * Q)))) := by
  rw [Matrix.transpose_mul]
  have hre : H * (Q'ᵀ * yᵀ * (G * (x * Q))) = (H * Q'ᵀ * yᵀ * G * x) * Q := by
    simp only [Matrix.mul_assoc]
  rw [hre, Matrix.trace_mul_comm (H * Q'ᵀ * yᵀ * G * x) Q]
  simp only [Matrix.mul_assoc]

variable {D : D7}

theorem gram_reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from HSpace.gram (reS S b))
      = (frP S b)ᴴ * HSpace.gram S * frP S b := by
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k => by
    simp only [frP, Module.Basis.toMatrix_apply]
    exact (S.frame.sum_repr (b k)).symm
  ext i j
  change S.hT (b i) (b j) = _
  rw [hb i, hb j]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply,
  Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  simp only [HSpace.gram, RingHom.id_apply, starRingEnd_apply]
  ring

theorem gram_reS_inv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from HSpace.gram (reS S b))⁻¹
      = frPinv S b * ((HSpace.gram S)⁻¹ * (frPinv S b)ᴴ) := by
  have h := gram_reS S b
  dsimp only at h ⊢
  rw [h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.inv_eq_left_inv (frPinv_mul_frP S b)]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (((HSpace.gram S)⁻¹).map (incA D) *
      ((Matrix.map (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from y) (cA D))ᵀ *
        ((HSpace.gram T).map (incA D) * (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from x)))) := by
  unfold hO
  dsimp only
  refine Eq.trans ?_ (quad_sum_eq_trace _ _ _ _)
  simp only [Matrix.map_apply]

theorem hO_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T) :
    hO (reS S b) T x y = hO S T (reW S T b x) (reW S T b y) := by
  have hP : (frPinv S b * ((HSpace.gram S)⁻¹ * (frPinv S b)ᴴ)).map (incA D) =
      (frPinv S b).map (incA D) * ((HSpace.gram S)⁻¹.map (incA D) *
        (((frPinv S b).map (incA D)).map (cA D))ᵀ) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
  have hi := gram_reS_inv S b
  dsimp only at hi
  have key := trace_change ((HSpace.gram S)⁻¹.map (incA D)) ((frPinv S b).map (incA D))
    (((frPinv S b).map (incA D)).map (cA D)) ((HSpace.gram T).map (incA D)) x (y.map (cA D))
  rw [← hP, ← hi] at key
  rw [hO_eq_trace, hO_eq_trace]
  dsimp only
  refine key.trans ?_
  clear key hi hP
  unfold reW
  have hm : (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) y ((frPinv S b).map (incA D))).map (cA D) =
      Matrix.map (α := AE D) (m := Fin T.rank) (n := Fin S.rank) y (cA D) * ((frPinv S b).map (incA D)).map (cA D) :=
    Matrix.map_mul
  exact congrArg (fun M => ((HSpace.gram S)⁻¹.map (incA D) *
    (Mᵀ * ((HSpace.gram T).map (incA D) *
      HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))))).trace) hm.symm

theorem symplO_reW : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T),
    symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := by
  intro D S T b x y
  unfold symplO
  rw [hO_reW]

end GlobalTheory.AdSpan.ReVec.Sympl

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialVectors_reframeSource : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, ∃ BS' : D.what₂.Tau → Matrix (Fin (reS S b).rank) (Fin (reS S b).rank) ℂ, (∀ τ, (BS' τ)ᴴ * gramAt D (reS S b) τ * BS' τ = (BS τ)ᴴ * gramAt D S τ * BS τ) ∧ ∀ (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ (reS S b) T (fun _ => 1) sT BS' BT (reF S T b f) P = reF S T b (pureTensorO ψ θ S T (fun _ => 1) sT BS BT f P) := by
  first | exact @GlobalTheory.AdSpan.pureTensorO_reF | exact GlobalTheory.AdSpan.pureTensorO_reF | (intros; apply GlobalTheory.AdSpan.pureTensorO_reF <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r)

theorem map_mem_intLoc_fld {v : HeightOneSpectrum (𝓞 F)} {c : Fv F v ⊗[F] E} (hc : c ∈ intLoc F E v) :
    Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) (IsScalarTower.toAlgHom F E (Fld P)) c ∈
      intLoc F (Fld P) v := by
  refine intLoc_induction (p := fun c => Algebra.TensorProduct.map (AlgHom.id F (Fv F v))
      (IsScalarTower.toAlgHom F E (Fld P)) c ∈ intLoc F (Fld P) v) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem hy) hc
  rw [Algebra.TensorProduct.map_tmul]
  exact tmul_mem_intLoc ha ⟨algebraMap E (Fld P) x, x.2.algebraMap⟩

theorem eventually_mem_intLoc_iff_coordEquiv_mem :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P,
      y ∈ intLoc F (Fld P) v ↔ coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v := by
  let b := RingOfIntegers.basis (Fld P)
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j =>
      eventually_one_tmul_mem_intLoc (F := F) ((powB P).repr (b j : Fld P) i),
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (E := Fld P) (powB P i)] with v h1 h2 y
  rw [mem_latLoc_stdLattice]
  constructor
  · intro hy i
    rw [coordEquiv_apply]
    refine intLoc_induction (p := fun y => coordF P (Fv F v) i y ∈ intLoc F E v) (fun a ha x => ?_) (by simp)
      (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem hy) hy
    rw [coordF_tmul]
    have e : (powB P).repr (x : Fld P) i = ∑ j, b.repr x j • (powB P).repr (b j : Fld P) i := by
      conv_lhs => rw [← b.sum_repr x]

      simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [← zsmul_eq_mul, map_zsmul]
    rw [e, TensorProduct.tmul_sum]
    refine sum_mem fun j _ => ?_
    rw [TensorProduct.tmul_smul]
    refine zsmul_mem ?_ _
    have e2 : a ⊗ₜ[F] ((powB P).repr (b j : Fld P) i) =
        (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] (powB P).repr (b j : Fld P) i) := by simp
    rw [e2]
    exact mul_mem (tmul_mem_intLoc ha 1) (h1 i j)
  · intro h
    rw [← coordInv_coordF P (Fv F v) y]
    refine sum_mem fun i _ => ?_
    rw [smul_eq_map_mul]
    exact mul_mem (map_mem_intLoc_fld P (h i)) (h2 i)

end GlobalTheory.TrUnitLat

theorem GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P, y ∈ intLoc F (Fld P) v ↔ GlobalTheory.TrUnitLat.coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v :=
  fun F E _ _ _ _ _ σ r P => GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem P
end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

theorem trace_mul_star_eq_sum (z z' : Fld P) :
    ∑ i, ∑ j, σ ((powB P).repr z' i) * gramOne P i j * (powB P).repr z j =
      Algebra.trace E (Fld P) (z * star' P z') := by
  have hs : star' P z' = ∑ i, σ ((powB P).repr z' i) • star' P (powB P i) := by
    conv_lhs => rw [← (powB P).sum_repr z']

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.smul_def, map_mul, star'_algebraMap, ← Algebra.smul_def]

  rw [hs, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (powB P).sum_repr z]

  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, smul_eq_mul, gramOne, Matrix.of_apply]
  ring

theorem isIsom_coordEquiv : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k],
    IsIsom P k (GlobalTheory.TrUnitLat.gramOne P) 1 (GlobalTheory.TrUnitLat.coordEquiv P k) := by
  intro F E _ _ _ σ r P k _ _ y y'
  simp only [Formalism.UG.hform, hx, one_mul, coordEquiv_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
    simp only [map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
    | tmul a' z' =>
      have e1 : ∀ e : E, sigR k σ (a' ⊗ₜ[F] e) = a' ⊗ₜ[F] σ e := fun e => rfl
      have e2 : sigR k (star' P) (a' ⊗ₜ[F] z') = a' ⊗ₜ[F] star' P z' := rfl
      have e3 : ∀ i j, JR k (gramOne P) i j = (1 : k) ⊗ₜ[F] gramOne P i j := fun i j => rfl
      have e4 : ∀ (b : k) (w : Fld P), trBase P k (b ⊗ₜ[F] w) = b ⊗ₜ[F] Algebra.trace E (Fld P) w := fun b w => rfl
      simp only [coordF_tmul, e1, e2, e3, Algebra.TensorProduct.tmul_mul_tmul, e4, mul_one, ← TensorProduct.tmul_sum,
        trace_mul_star_eq_sum]
      rw [mul_comm a' a]

end GlobalTheory.TrUnitLat
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

theorem subring_pi_mem_of_const_of_injective {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring (ι → ℂ))
    (hc : ∀ c : ℂ, (fun _ => c) ∈ R) (a : ι → ℂ) (ha : Function.Injective a) (haR : a ∈ R) (x : ι → ℂ) :
    x ∈ R := by
  have hp : ∀ p : ℂ[X], (fun i => p.eval (a i)) ∈ R := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have := R.add_mem hp hq
      convert this using 1
      ext i; simp
    | monomial n c =>
      have := R.mul_mem (hc c) (R.pow_mem haR n)
      convert this using 1
      ext i; simp [eval_monomial]
  have := hp (Lagrange.interpolate Finset.univ a x)
  convert this using 1
  ext i
  exact (Lagrange.eval_interpolate_at_node x ha.injOn (Finset.mem_univ i)).symm

theorem exists_extensionEmbedding_eq_ofReal {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsReal) (t : ℝ) : ∃ a : w.Completion, InfinitePlace.Completion.extensionEmbedding w a = (t : ℂ) := by
  refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t, ?_⟩
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem PsiAll_surjective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} [_root_.NumberField.IsTotallyComplex E] {r : ℕ} (P : PPol σ r) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) : Function.Surjective (PsiAll P τ) := by
  intro x
  have hτ : ¬ ComplexEmbedding.IsReal τ.1 := IsTotallyComplex.complexEmbedding_not_isReal τ.1
  have : ∃ e : E, (τ.1 e).im ≠ 0 := by
    by_contra h
    push_neg at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext e
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (h e)
  obtain ⟨e, he⟩ := this
  refine subring_pi_mem_of_const_of_injective (PsiAll P τ).range ?_ (cxRoots τ.1 P) (cxRoots_injective P τ) ?_ x
  · intro c
    obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal hw (c.re - c.im / (τ.1 e).im * (τ.1 e).re)
    obtain ⟨b, hb⟩ := exists_extensionEmbedding_eq_ofReal hw (c.im / (τ.1 e).im)
    refine ⟨a ⊗ₜ[F] 1 + b ⊗ₜ[F] algebraMap E (Fld P) e, ?_⟩
    ext i : 1
    rw [PsiAll_apply, map_add (f := _), Psi_tmul, Psi_tmul, psiL_algebraMap, map_one, ha, hb, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  · refine ⟨1 ⊗ₜ[F] alpha P, ?_⟩
    ext i : 1
    rw [PsiAll_apply, Psi_tmul, psiL_alpha, map_one, one_mul]

theorem PsiAll_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) := by
  intro F E _ _ _ _ _ σ hCM r P w τ
  haveI : IsTotallyReal F := hCM.1
  haveI : IsTotallyComplex E := hCM.2.1
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hs := PsiAll_surjective P hw τ
  refine ⟨?_, hs⟩
  letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
  let f : w.Completion ⊗[F] Fld P →ₗ[w.Completion] (Fin r → ℂ) :=
    { toFun := PsiAll P τ
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]
        ext i
        rw [Pi.mul_apply, PsiAll_apply, Psi_tmul, map_one, mul_one, Pi.smul_apply, Algebra.smul_def]
        rfl }
  have hk : Module.finrank w.Completion ℂ = 2 := by
    rw [Algebra.finrank_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (RingEquiv.refl ℂ) ?_,
      Complex.finrank_real_complex]
    ext x
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x
  haveI : Module.Finite w.Completion ℂ := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite E (Fld P) := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finite
  haveI : Module.Finite F (Fld P) := Module.Finite.trans E (Fld P)
  have hd : Module.finrank w.Completion (w.Completion ⊗[F] Fld P) = Module.finrank w.Completion (Fin r → ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank F E (Fld P), h2, finrank_Fld,
      Module.finrank_pi_fintype]
    simp [hk, mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) hd).2 hs

end GlobalTheory.TrEll.RealTorus
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_linearIsometryEquiv_intertwining_modelRep : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  first | exact @GlobalTheory.SeeInt.conjModel_of_setting | exact GlobalTheory.SeeInt.conjModel_of_setting | (intros; apply GlobalTheory.SeeInt.conjModel_of_setting <;> assumption)
end
