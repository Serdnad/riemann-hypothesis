module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle406
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorEqOffPlaceMulAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle407
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle408
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle432
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle015

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (a b : ℕ), ∃ I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) * I' = 1 ∧ ∀ x : D.host.E, x ∈ I' ↔ star x ∈ P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) := by
  first | exact @GlobalTheory.ConjIdeal.stA_modul_conj_inv | exact GlobalTheory.ConjIdeal.stA_modul_conj_inv | (intros; apply GlobalTheory.ConjIdeal.stA_modul_conj_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.unitaryEmbedding_continuous_mul_rational : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), Continuous (stabilizerEmbedding d) ∧
    (∀ g h, stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h) ∧ ∀ γ ∈ GQ A, stabilizerEmbedding d γ ∈ GQ B := by
  first | exact @GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational | exact GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational | (intros; apply GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_continuous_hom_rational <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_unramified_over_place : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}, IsPlaceIdem D v ε → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) → GlobalTheory.WeilParts.UnramAt ε χ := by
  first | exact @GlobalTheory.UnrOverPlaceConv.unramAt_of_unrAt_all | exact GlobalTheory.UnrOverPlaceConv.unramAt_of_unrAt_all | (intros; apply GlobalTheory.UnrOverPlaceConv.unramAt_of_unrAt_all <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

theorem _root_.GlobalTheory.T.integratedOperator_normalizedIndicatorProd_fixed : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, IsOpen (K' v : Set (GLoc D.sp.cm.sig V.gram v))) → (∀ v, K' v ≤ Kv V v) → (∀ᶠ v in cofinite, K' v = Kv V v) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W), (∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x) → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)))) P → P x = x := by
  first | exact @GlobalTheory.TrIdem.integralOp_normInd_fix | exact GlobalTheory.TrIdem.integralOp_normInd_fix | (intros; apply GlobalTheory.TrIdem.integralOp_normInd_fix <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.haar_eq_restrictedProductMeasure_unitaryFiniteAdelic : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (ν : Measure (GfC V)), IsFinMeas V μf ν → ∀ s : Set (GfC V), IsCompact (closure s) → ν s = νF ((finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' s) := by
  first | exact @GlobalTheory.FinMeasEq.finMeas_eq | exact GlobalTheory.FinMeasEq.finMeas_eq | (intros; apply GlobalTheory.FinMeasEq.finMeas_eq <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.pureTensorOperator_eq_offPlace_mul_atPlace : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ (H : W →ₗ[ℂ] W) (K : Subgroup (GfC V)), IsOpen (K : Set (GfC V)) ∧ (∀ g x, H (σ (locFin V u g) x) = σ (locFin V u g) (H x)) ∧ (∀ x, ∀ k ∈ K, finLoc V u k = 1 → σ k (H x) = H x) ∧ ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (μf u) (σ.comp (locFin V u)) f B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (Function.update ff u f)) (H ∘ₗ B) := by
  first | exact @GlobalTheory.OffOp.exists_offOp | exact GlobalTheory.OffOp.exists_offOp | (intros; apply GlobalTheory.OffOp.exists_offOp <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.rationalMatrix_sandwich_mem_completed_ideal_latticeHom : ∀ {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E), (∀ y ∈ M, j *ᵥ y ∈ Λ) → (∀ t ∈ Λ', q *ᵥ t ∈ M') → ∀ x : Mx D m n, x ∈ hatMx (𝔪 • homLat Λ Λ') → rat q * x * rat j ∈ hatMx (𝔪 • homLat M M') := by
  first | exact @GlobalTheory.TwistHatMx.rat_conj_mem_hatMx | exact GlobalTheory.TwistHatMx.rat_conj_mem_hatMx | (intros; apply GlobalTheory.TwistHatMx.rat_conj_mem_hatMx <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.exists_rational_hom_approx_half_mod_ideal : ∀ {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → Submodule.IsFullLattice D.host.E Λ → Submodule.IsFullLattice D.host.E Λ' → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → ∀ z : Mx D m n, IsHalf e z → z ∈ hatMx (homLat Λ Λ') → ∃ x₁ : homLat Λ Λ', z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  first | exact @GlobalTheory.CosRatApprox.exists_rat_approx | exact GlobalTheory.CosRatApprox.exists_rat_approx | (intros; apply GlobalTheory.CosRatApprox.exists_rat_approx <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.CosFlip

open Matrix GlobalTheory.FunObj.Comparison₂ GlobalTheory.SplitFlip GlobalTheory.StdFrames ValuativeRel Formalism.L2.DIV

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem v_le_cosExp (G : GridData L sc) {s : OA D} (hs : s ∈ idS D.host.F G.modul) (w : Pl D.host.E) :
    Valued.v (cpt (D := D) w s.1) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  by_cases hw : w ∈ G.pl.W0
  · exact (mem_idS_modul G s).1 hs w hw
  · rw [(depthAt_of_notMem G hw).1, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact (mem_OA_iff _).1 s.2 w

theorem coord_sub_mem (G : GridData L sc) (B : Frames G) (t : T) (w : Pl D.host.E) (h : 0 < D.R.m)
    (h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0))) (h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)))
    {y y₀ : homLat (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0))} (hy : Cos.mk G.modul y = Cos.mk G.modul y₀) :
    B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (y.1.map (algebraMap D.host.E (Kw w))) -
      B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (y₀.1.map (algebraMap D.host.E (Kw w))) ∈ matLat (Fin ((locGrid G t w).rank (1, 0))) (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t w).rank (0, 0)))) := by
  rw [mem_matLat_pow, map_algebraMap, map_algebraMap, coord_map, coord_map]
  intro a b
  obtain ⟨s, hs, e⟩ := fr_mem_idS h1 h0 (sub_mem_of_mk_eq hy)
    (Fin.cast (rank_vertex G t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
    (Fin.cast (rank_vertex G t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)
  simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rw [← RingHom.map_sub, ← Matrix.sub_apply, ← fr_sub, ← Matrix.map_sub _ (map_sub (eToEAf D)), ← e]
  exact v_le_cosExp G hs w

theorem cosetSet_mk (G : GridData L sc) (B : Frames G) (t : T) (w : Pl D.host.E) (h : 0 < D.R.m)
    (h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0))) (h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)))
    (y₀ : homLat (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0))) :
    cosetSet t w B h (Cos.mk G.modul y₀) = {x | x - B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩
      ⟨h, Nat.zero_le _⟩ (y₀.1.map (algebraMap D.host.E (Kw w))) ∈
        matLat (Fin ((locGrid G t w).rank (1, 0))) (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t w).rank (0, 0))))} := by
  ext x
  constructor
  · rintro ⟨y, hy, hx⟩
    have := add_mem hx (coord_sub_mem G B t w h h0 h1 hy)
    rwa [sub_add_sub_cancel] at this
  · intro hx
    exact ⟨y₀, rfl, hx⟩

end GlobalTheory.FunObj.CosFlip

namespace GlobalTheory.FunObj.CosFlip

open Matrix GlobalTheory.FunObj.Comparison₂ GlobalTheory.SplitFlip GlobalTheory.StdFrames ValuativeRel Formalism.L2.DIV

theorem sub_mem_iff_of_sub_mem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (S : Submodule R M) {a b : M}
    (h : a - b ∈ S) (x : M) : x - a ∈ S ↔ x - b ∈ S := by
  constructor
  · intro hx
    have := add_mem hx h
    rwa [sub_add_sub_cancel] at this
  · intro hx
    have := sub_mem hx h
    rwa [sub_sub_sub_cancel_right] at this

theorem exists_cos_cosetSet_eq : ∀ {D : D7} {T T' : Type} {L : LevCh D T} {L' : LevCh D T'} {sc : Consts} (G : GridData L sc) (G' : GridData L' sc)
    (B : GlobalTheory.FunObj.Frames G) (B' : GlobalTheory.FunObj.Frames G'),
    IsSDFrame (Yc D 0) (L.βY 0) (L.ΛY 0) (D.host.g 0 * D.host.g 1) →
    IsSDFrame (Yc D 0) (L'.βY 0) (L'.ΛY 0) (D.host.g 0 * D.host.g 1) →
    G'.pl.v0 = G.pl.v0 → G'.pl.w = G.pl.w → G'.sp.Vs 1 0 = G.sp.Vs 1 0 → HEq (B'.βs 1 0) (B.βs 1 0) →
    ∀ (h : 0 < D.R.m) (κ' : G'.CosAt 0), ∃ κ : G.CosAt 0, ∀ (t : T') (t₀ : T) (w : Pl D.host.E),
      GlobalTheory.FunObj.cosetSet t w B' h κ' = GlobalTheory.FunObj.cosetSet t₀ w B h κ := by
  intro D T T' L L' sc G G' B B' hY hY' hv0 hw _ _ h κ'
  have h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0)) := hY.choose_spec.1
  have h0' : IsFrame (B'.β 0 0) (G'.Λ (.grid 0 0)) := hY'.choose_spec.1
  have h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)) := B.isFrame 1 0 le_rfl h (Nat.zero_le _)
  have h1' : IsFrame (B'.β 1 0) (G'.Λ (.grid 1 0)) := B'.isFrame 1 0 le_rfl h (Nat.zero_le _)
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
  have hdep : ∀ v, G'.pl.depth sc v = G.pl.depth sc v := fun v => by
    unfold Places.depth
    rw [hv0]
  have hexp : ∀ w, cosExp G' w = cosExp G w := fun w => by
    by_cases hm : w ∈ G.pl.W0
    · rw [cosExp, cosExp, if_pos (by rw [hW0]; exact hm), if_pos hm, hdep]
    · rw [cosExp, cosExp, if_neg (by rw [hW0]; exact hm), if_neg hm]
  obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _ κ'
  have hint : ∀ i j, ∃ s ∈ idS D.host.F ⊤, s.1 = fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D)) i j :=
    fr_mem_idS h1' h0' (by rw [Submodule.top_smul]; exact y'.2)
  choose N _ hN using hint
  have hr : (G.V (.grid 1 0)).rank = (G'.V (.grid 1 0)).rank := by
    show (G.sp.Vs 1 0).sp.rank = (G'.sp.Vs 1 0).sp.rank
    rw [‹G'.sp.Vs 1 0 = G.sp.Vs 1 0›]
  obtain ⟨x₀, hx₀, hs⟩ := HatFrame.homLat_approx_mod (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0)) (B.β 1 0) (B.β 0 0) h1 h0
    G.modul (G.pl.modul_ne_bot sc) (fun i j => N i (Fin.cast hr j))
  refine ⟨Cos.mk G.modul ⟨x₀, hx₀⟩, fun t t₀ w => ?_⟩
  have hk : Cos.mk G'.modul y' = κ' := hy'
  rw [← hk, cosetSet_mk G' B' t w h h0' h1' y', cosetSet_mk G B t₀ w h h0 h1 ⟨x₀, hx₀⟩, hexp]
  have key : @id (Matrix (Fin ((locGrid G t₀ w).rank (1, 0))) (Fin ((locGrid G t₀ w).rank (0, 0))) (Kw w))
        (B'.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
          (y'.1.map (algebraMap D.host.E (Kw w)))) -
      B.coord t₀ w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (x₀.map (algebraMap D.host.E (Kw w))) ∈ matLat (Fin ((locGrid G t₀ w).rank (1, 0)))
        (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t₀ w).rank (0, 0)))) := by
    rw [mem_matLat_pow]
    dsimp only [id]
    rw [Comparison₂.map_algebraMap, Comparison₂.map_algebraMap, coord_map, coord_map]
    intro a b
    obtain ⟨s, hs1, hs2⟩ := hs (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
      (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)
    have e1 : (N (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
        (Fin.cast hr (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)) : EAf D) =
        fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) := hN _ _
    have e2 : fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) -
        fr (B.β 0 0) (B.β 1 0) (x₀.map (eToEAf D))
          (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) = -(s : EAf D) := by
      rw [hs2, ← e1]
      exact (neg_sub _ _).symm
    show Valued.v (cpt (D := D) w (fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)) -
        cpt (D := D) w (fr (B.β 0 0) (B.β 1 0) (x₀.map (eToEAf D))
          (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a))) ≤ _
    rw [← RingHom.map_sub, e2, RingHom.map_neg, Valuation.map_neg]
    exact v_le_cosExp G hs1 w
  ext x
  exact sub_mem_iff_of_sub_mem _ key x

end GlobalTheory.FunObj.CosFlip
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host


theorem _root_.GlobalTheory.T.gridGivenPathTensor_mem_subfield : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) → (∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) → ∀ z : (locGrid G t w).Args, (givenStage t w B Φ).tensor z ∈ F := by
  first | exact @GlobalTheory.GivenField.tensor_givenStage_mem | exact GlobalTheory.GivenField.tensor_givenStage_mem | (intros; apply GlobalTheory.GivenField.tensor_givenStage_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.idempotentSum_scalar_smul_mem_completedModulus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  first | exact @GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | exact GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | (intros; apply GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HalfPowField

theorem apow_half_mem_of_sqrt : ∀ {D : D7} (F : Subfield ℂ) (w : Pl D.host.E), ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F → ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ F := by
  intro D F w hs u
  simpa using GlobalTheory.MovedField.apow_half_mem hs u 1

end GlobalTheory.HalfPowField
end
end
