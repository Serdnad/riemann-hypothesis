module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownConv

open GlobalTheory.Grid

variable {D : D7}

theorem MeasDat.haar_fd {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem integrableOn_thetaKO_mul_cusp (hP : GlobalTheory.Published.CuspRapidDecay) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T}
    (hω : IsWeilDatumO ψ (sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ (sgn ε S) T Φ)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν)
    {φ : GA D S → ℂ} (hφ : IsAutFunSm θ S φ) (hc : IsCuspFun S φ) (h : GA D T) :
    IntegrableOn (fun g => thetaKO ω g h Φ * φ g) 𝓕 ν := by
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S φ := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc
  have e : ∀ g, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((ofSgn ε S).symm g) h Φ := fun g => by
    show ω (g, h) Φ 0 = ω (ofSgn ε S ((ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hcont : Continuous fun g => thetaKO ω g h Φ := by
    simp only [e]
    exact (hω.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε S).prodMk continuous_const)
  have hinv : ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  have hg : GlobalTheory.Grow.ModGrowth S fun g => thetaKO ω g h Φ := by
    obtain ⟨C, A, hC⟩ := GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_modGrowth_fst hθ hω hΦ h
    exact ⟨C, A, fun g => by simp only [e]; exact hC _⟩
  exact hR.integrableOn_modGrowth_mul hν h𝓕 hg hinv hcont.measurable.aestronglyMeasurable

end GlobalTheory.DownConv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaLiftTypeTh

theorem sigOK_vert {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R)
    (hG : G.Is) {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (G.V i j).V.SigOK := by
  cases i with
  | succ i => exact (hG.spaces.vert i j hi hj).sigOK
  | zero =>
    show (GlobalTheory.Grid.row0 R j).V.SigOK
    cases j with
    | zero => exact D.sp.Y_sig 0
    | succ j =>
      simp only [GlobalTheory.Grid.row0]
      split_ifs
      · exact D.sp.Y_sig _
      · exact D.sp.X'_sig

end GlobalTheory.ThetaLiftTypeTh
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaArrowType


open GlobalTheory.Grid in
theorem sigOK_vert {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridPre R) (hG : G.Is) :
    ∀ i j, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).V.SigOK
  | 0, 0, _, _ => D.sp.Y_sig 0
  | 0, j + 1, _, _ => by
    show (row0 R (j + 1)).V.SigOK
    by_cases h : j + 1 < D.R.m
    · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]; exact D.sp.Y_sig _
    · rw [← nodeX_eq_chainVertexAtRowZero_of_ge R h]; exact D.sp.X'_sig
  | i + 1, j, hi, hj => (hG.spaces.vert i j hi hj).sigOK

theorem goodPar_of_node {D : D7} (N : GlobalTheory.Grid.Node D) (hV : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  obtain ⟨hp, hq⟩ := GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hV (tauE D τ))
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), hp, hq⟩

end GlobalTheory.ThetaArrowType
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColConv

open GlobalTheory.Grid

theorem measDat_haar_fd {D : D7} {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {u : WO S T → ℂ}

theorem thetaKO_mul_cusp_integrableOn_fst (hP : GlobalTheory.Published.CuspRapidDecay) (hω : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) (hu : IsThetaFunO ψ S T u) {y : GA D S → ℂ} (hy : IsAutFunSm θ S y)
    (hc : IsCuspFun S y) (x : GA D T) : IntegrableOn (fun g => thetaKO om g x u * y g) 𝓕 ν := by
  have : BorelSpace (GA D S) := ⟨rfl⟩
  exact (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hy hc).integrableOn_modGrowth_mul hν h𝓕
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_modGrowth_fst hθ hω hu x)
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hu x)
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_continuous_fst hω hu x).measurable.aestronglyMeasurable

theorem measX_haar_fd {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}
    (hG : G.Is) (j : ℕ) (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact measDat_haar_fd (hG.meas.P D.R.m le_rfl)
  | succ j => exact measDat_haar_fd (hG.meas.X j hj)

end GlobalTheory.ColConv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open Matrix

noncomputable section
namespace GlobalTheory.LatExpand




variable {D : D7}

theorem finPart_liftFin (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (GlobalTheory.LatticeStable.liftFin D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a m => rfl

theorem toEAf_apply (w : Formalism.L2.Theta.AE D) :
    Formalism.IndefR.Datum.toEAf D w = Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D w) := rfl

theorem toEAf_liftFin (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.IndefR.Datum.toEAf D (GlobalTheory.LatticeStable.liftFin D y) =
      Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y := by
  rw [toEAf_apply, finPart_liftFin]

theorem toEAf_incA' (e : D.host.E) :
    Formalism.IndefR.Datum.toEAf D (incA D e) = Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) e := rfl

theorem exists_integralCombination_of_mem_completedLattice {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z : Fin n → Formalism.IndefR.Datum.EAf D) (hz : z ∈ Formalism.L2.Herm.hatL (F := D.host.F) B) :
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, z i = Formalism.IndefR.Datum.toEAf D (∑ p, β p * incA D (b p i)) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨1, fun _ => 1, fun _ => c, fun _ => ?_, fun _ => hc, fun i => ?_⟩
    · exact (GlobalTheory.SplitDec.int_iff 1).2 (by rw [map_one]; exact one_mem _)
    · rw [Fin.sum_univ_one, one_mul, toEAf_incA']
  | zero =>
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, fun i => ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, map_zero]; rfl
  | add x y _ _ hx hy =>
    obtain ⟨m, β, b, hβ, hb, he⟩ := hx
    obtain ⟨m', β', b', hβ', hb', he'⟩ := hy
    refine ⟨m + m', Fin.append β β', Fin.append b b', fun p => ?_, fun p => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
      · rw [Fin.append_left]; exact hβ q
      · rw [Fin.append_right]; exact hβ' q
    · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
      · rw [Fin.append_left]; exact hb q
      · rw [Fin.append_right]; exact hb' q
    · rw [Fin.sum_univ_add, map_add (f := _), Pi.add_apply, he i, he' i]
      simp only [Fin.append_left, Fin.append_right]
  | smul r x _ hx =>
    obtain ⟨m, β, b, hβ, hb, he⟩ := hx
    set y := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm (r : Formalism.IndefR.Datum.EAf D)
    have hy : Formalism.IndefR.Datum.toEAf D (GlobalTheory.LatticeStable.liftFin D y) = r := by
      rw [toEAf_liftFin, AlgEquiv.apply_symm_apply]
    have hyi : finPart D (GlobalTheory.LatticeStable.liftFin D y) ∈ intAE D :=
      (GlobalTheory.SplitDec.int_iff _).2 (by rw [hy]; exact r.2)
    refine ⟨m, fun p => GlobalTheory.LatticeStable.liftFin D y * β p, b, fun p => ?_, hb, fun i => ?_⟩
    · rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE hyi (hβ p)
    · simp only [mul_assoc, ← Finset.mul_sum, map_mul, hy]
      rw [Pi.smul_apply, he i, Subring.smul_def, smul_eq_mul]

theorem expand {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Y : Fin n → Formalism.L2.Theta.AE D)
    (hY : (fun i => Formalism.IndefR.Datum.toEAf D (Y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B) :
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, finPart D (Y i) = finPart D (∑ p, β p * incA D (b p i)) := by
  obtain ⟨m, β, b, hβ, hb, he⟩ := exists_integralCombination_of_mem_completedLattice B _ hY
  refine ⟨m, β, b, hβ, hb, fun i => ?_⟩
  have h := he i
  rw [toEAf_apply, toEAf_apply] at h
  exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem finPart_eq_int_comb_of_mem_hatL : ∀ {D : D7} {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Y : Fin n → Formalism.L2.Theta.AE D),
    (fun i => Formalism.IndefR.Datum.toEAf D (Y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B →
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, finPart D (Y i) = finPart D (∑ p, β p * incA D (b p i)) := fun B Y hY => expand B Y hY

end GlobalTheory.LatExpand
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MultLatDecomp




theorem heisO_eq_root_smul_finRat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ n : ℕ, 0 < n → ∀ w : WO S T, n • w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (ζ : ℂ), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ heisO ψ S T w f = ζ • heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f := by
  intro D ψ S T ΛS ΛT hψ hS hT f hf n hn w hw
  classical
  have hinf : w.map (infPart D) = 0 := by
    have h1 := GlobalTheory.VacUnique.latO_inf S T _ _ _ hw
    funext i j
    have h2 : infPart D ((n • w) i j) = 0 := congrFun (congrFun h1 i) j
    rw [Matrix.smul_apply, map_nsmul] at h2
    have hn' : (n : D.host.F) ≠ 0 := by exact_mod_cast hn.ne'
    have h3 : (n : D.host.F) • infPart D (w i j) = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h2
    show infPart D (w i j) = 0
    rw [← inv_smul_smul₀ hn' (infPart D (w i j)), h3, smul_zero]
  obtain ⟨M, u, hu, hM⟩ := GlobalTheory.LatVac.approx hS hT w
  have hw_eq : w = GlobalTheory.VacUnique.finRat S T M + u := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · have h1 : infPart D (w i j) = 0 := congrFun (congrFun hinf i) j
      have h2 : infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 :=
        congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
      rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add (f := _), h1, h2, GlobalTheory.LatVac.infPart_of_mem hu, add_zero,
        sub_zero]
    · rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add (f := _), hM, sub_eq_zero]
      rfl
  have hmem : GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    have e : GlobalTheory.VacUnique.finRat S T (n • M) = n • w - n • u := by
      rw [map_nsmul, hw_eq, smul_add, add_sub_cancel_right]
    rw [e]
    exact sub_mem hw (nsmul_mem hu n)
  obtain ⟨ε, hε, hεf⟩ := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).2.2 f hf u hu
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ (GlobalTheory.VacUnique.finRat S T M) u f
  rw [hεf f hf, GlobalTheory.LatVac.heisO_smul] at h1
  have hinv : ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) = 1 := by
    rw [← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one]
  have hX : ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) =
      ψ (symplO S T (GlobalTheory.VacUnique.finRat S T M) u) := by
    rw [← ψ.map_add_eq_mul, symplOH, ← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]
  have hY : ψ (symplO S T (GlobalTheory.VacUnique.finRat S T M) u) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    have e : n • symplO S T (GlobalTheory.VacUnique.finRat S T M) u = symplO S T (GlobalTheory.VacUnique.finRat S T (n • M)) u := by
      change n • GlobalTheory.LatVac.symplHom S T (GlobalTheory.VacUnique.finRat S T M) u =
        GlobalTheory.LatVac.symplHom S T (GlobalTheory.VacUnique.finRat S T (n • M)) u
      rw [map_nsmul (GlobalTheory.VacUnique.finRat S T), map_nsmul (GlobalTheory.LatVac.symplHom S T), AddMonoidHom.nsmul_apply]
    rw [e]
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hmem hu
  have e1 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ n = 1 := by
    rw [hX]; exact hY
  refine ⟨M, ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u), ⟨2 * n, by omega, ?_⟩, hmem, ?_⟩
  · calc (ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ (2 * n)
        = (ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ (2 * n) *
          (ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ n := by
          rw [e2, mul_one]
      _ = (ε ^ 2) ^ n * ((ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) *
          ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ 2) ^ n := by ring
      _ = 1 := by rw [e1, hinv]; simp
  · rw [hw_eq, mul_comm, mul_smul, h1, smul_smul, hinv, one_smul]

end GlobalTheory.MultLatDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedTrans

theorem entry_tr (zz xx : ℂ) (r : ℝ) :
    -(Real.pi * Complex.I) * (-((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ (zz + xx) * -xx)).re : ℝ) : ℂ)) +
      -((Real.pi * r : ℝ) : ℂ) * ((‖zz + xx‖ ^ 2 : ℝ) : ℂ) =
    -((Real.pi * r : ℝ) : ℂ) * ((‖zz‖ ^ 2 : ℝ) : ℂ) +
      (-(Real.pi : ℂ) * (2 * (r : ℂ) * (zz * starRingEnd ℂ xx)) - (Real.pi : ℂ) * (2 * (r : ℂ) * (xx * starRingEnd ℂ xx)) / 2) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

theorem heisO_finRat_real : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), X = (fun τ a b => -(((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T M τ) * GlobalTheory.FockPos.frAt frS τ) a b)) → ∀ w : WO S T, w.map (finPart D) = 0 → heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f w = GlobalTheory.FockPos.gaussO θ frS frT w * (Φ (GlobalTheory.FockPos.zCo θ frS frT w + X) * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, GlobalTheory.FockPos.zCo θ frS frT w τ a b * starRingEnd ℂ (X τ a b)) - (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2)) := by
  intro D ψ θ S T frS frT hS hT hψ hθ f hf Φ hΦ M X hX w hw
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨z, rfl⟩ : ∃ z, GlobalTheory.FockCompare.iotaW σ T S z = w := ⟨_, hch.iota_pi hw⟩
  have e : GlobalTheory.FockCompare.iotaW σ T S z + GlobalTheory.VacUnique.finRat S T M =
      ratW T S M + GlobalTheory.FockCompare.iotaW σ T S (z - GlobalTheory.VacUnique.infRat S T M) := by
    rw [GlobalTheory.VacUnique.ratW_eq hch, AddMonoidHom.map_sub]; abel
  show ψ (symplOH S T _ (GlobalTheory.VacUnique.finRat S T M)) * f (_ + GlobalTheory.VacUnique.finRat S T M) = _
  rw [GlobalTheory.FinTranslate.symplOH_real_fin (GlobalTheory.VacUnique.finRat_inf S T M) hw, AddChar.map_zero_eq_one, one_mul, e,
    hf.quasi, AddChar.map_neg_eq_inv, GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ hθ hψ S T _ _ (Or.inr (hch.real_iota T S _)),
    GlobalTheory.VacUnique.piW_ratW hθ, hch.pi_iota, ← Complex.exp_neg,
    hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO]
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) with hZ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z - GlobalTheory.VacUnique.infRat S T M)) = Z + X := by
    rw [hZ, GlobalTheory.ThetaLawOF.zCo_iota hch, GlobalTheory.ThetaLawOF.zCo_iota hch, hX]; funext τ a b
    show ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) - Matrix.of (GlobalTheory.VacUnique.infRat S T M τ)) * GlobalTheory.FockPos.frAt frS τ) a b = _
    rw [Matrix.mul_sub, Matrix.sub_mul]
    exact sub_eq_add_neg _ _
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T M) (z - GlobalTheory.VacUnique.infRat S T M) =
      ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (starRingEnd ℂ ((Z + X) τ a b) * -X τ a b)).re := by
    rw [GlobalTheory.ThetaLawOF.omO_frame frS frT hS hT, ← hz2, GlobalTheory.ThetaLawOF.zCo_iota hch]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hX]
    simp only [neg_neg]
  rw [hz2, hom]
  have kE : Complex.exp (-(-(Real.pi * Complex.I) * ((∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ ((Z + X) τ a b) * -X τ a b)).re : ℝ) : ℂ))) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry_tr (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    simp only [Pi.add_apply] at h ⊢
    push_cast at h ⊢
    linear_combination h
  rw [← mul_assoc, kE]
  ring

end GlobalTheory.MovedTrans

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.local_factor_finite_place_heisenberg_sum_base_vector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → IsLocOp ψ S T μ 𝓕 f₀ (.inl v) x := by
  first | exact @GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin | exact GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin | (intros; apply GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin <;> assumption)
end
