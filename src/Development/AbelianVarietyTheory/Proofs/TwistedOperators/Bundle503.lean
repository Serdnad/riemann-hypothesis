module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormEqMulInner
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle321
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

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

noncomputable section

namespace GlobalTheory.MovedKappaEx

def OffPrime {D : D7} (e : Formalism.L2.Theta.AE D) (q : ℕ) : Prop :=
  ∀ v ε, IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε → ((q : 𝓞 D.host.F)) ∉ v.asIdeal

def splitOff {D : D7} (V : HSp D) (Q : Finset ℕ) : Subgroup (GfC V) :=
  Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧ SuppAt e V (g : GA D V)}

def RatFin {D : D7} (V : HSp D) (g : GfC V) : Prop := ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V)

def UnitAt (q : ℕ) [Fact q.Prime] (c : ℂ) : Prop := ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam c‖ = 1

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetKap (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)

end

end GlobalTheory.MovedKappaEx
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def InvLine (ch : Choice R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : Sizes) (P : ι → Entries S), (∀ τ, (P τ).Good) ∧
    ∃ e : PolCol ch.G × PolRow ch.G → OM P, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ l ∈ invFun (omRep P), ∀ Q, defPer t ch.S.toGridChoice M Q d (colFn ch a) (formTop ch t y) = l (e Q)

theorem periodsOnLine_of_invLine (hL : OneLine) (ch : Choice R) (h : InvLine ch) : PeriodsOnLine ch := by
  obtain ⟨ι, _, _, S, P, hP, e, he⟩ := h
  have : Module.Free ℂ (invFun (omRep P)) := Module.Free.of_divisionRing ℂ _
  obtain ⟨L0, -, hL0⟩ := finrank_eq_one_iff'.1 (hL ι S P hP)
  refine ⟨fun Q => L0.1 (e Q), fun t a hS β hβ M hM τ hτ d hd y => ?_⟩
  obtain ⟨l, hl, hle⟩ := he t a hS β hβ M hM τ hτ d hd y
  obtain ⟨c, hc⟩ := hL0 ⟨l, hl⟩
  refine ⟨c, fun Q => ?_⟩
  have hc' : c • L0.1 = l := congrArg Subtype.val hc
  rw [hle Q, ← hc']
  rfl

end GlobalTheory.RowReal

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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_snd_one_sub_idemS :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) atTop (𝓝 0) := by
  classical
  have hin : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) w, w ∈ T → evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) = 0 := by
    intro T w hw
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) = 0
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS, if_pos hw, sub_self]
  have hint : ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) w,
      evalV F w (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) ∈ w.adicCompletionIntegers F := by
    intro T w
    change evFin F w (1 - GlobalTheory.FinDecomp.idemS F T) ∈ w.adicCompletionIntegers F
    rw [map_sub, map_one, GlobalTheory.FinDecomp.evFin_idemS]
    split_ifs
    · rw [sub_self]; exact zero_mem _
    · rw [sub_zero]; exact one_mem _
  let A : ∀ w : HeightOneSpectrum (𝓞 F), Set (w.adicCompletion F) := fun w => w.adicCompletionIntegers F
  let o : ∀ w, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩
  let g : Finset (HeightOneSpectrum (𝓞 F)) → ∀ w, A w := fun T w => ⟨_, hint T w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({w} : Finset _)] with T hT
    exact Subtype.ext (hin T w (hT (Finset.mem_singleton_self w))).symm
  have h := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_infIdem : At (evI F) (pairA F 1 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * 1, u.2 * 0) = (0, 0)
  rw [h1, zero_mul, mul_zero]

theorem one_sub_idemS_eq (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) :
    1 - GlobalTheory.FinDecomp.idemS F T = pairA F 1 0 + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) := by
  have h := GlobalTheory.FinDecomp.fst_idemS (F := F) T
  refine Prod.ext ?_ ?_
  · change 1 - fstA F (GlobalTheory.FinDecomp.idemS F T) = 1 + 0
    rw [h, sub_zero, add_zero]
  · change sndA F (1 - GlobalTheory.FinDecomp.idemS F T) = 0 + sndA F (1 - GlobalTheory.FinDecomp.idemS F T)
    rw [zero_add]

theorem tendsto_cut :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T))) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (0 : Ainf F))).prodMk_nhds (tendsto_snd_one_sub_idemS (F := F))
  exact h

theorem tendsto_phi {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE F E)) (hM : pairA F 1 0 • (M - 1) = 0) :
    Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) => GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M) atTop (𝓝 M) := by
  have key : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M =
      M + pairA F 0 (sndA F (1 - GlobalTheory.FinDecomp.idemS F T)) • (1 - M) := by
    intro T
    have h0 : pairA F 1 0 • (1 - M) = 0 := by rw [← neg_sub, smul_neg, hM, neg_zero]
    have h1 : GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) M = M + (1 - GlobalTheory.FinDecomp.idemS F T) • (1 - M) := by
      simp only [GlobalTheory.FinDecomp.phi, sub_smul, smul_sub, one_smul]; abel
    rw [h1, congrArg (· • (1 - M)) (one_sub_idemS_eq T), add_smul, h0, zero_add]
  simp_rw [key]
  have h := (tendsto_const_nhds (x := M)).add ((tendsto_cut (F := F)).smul_const (1 - M))
  have e : M + (0 : AF F) • (1 - M) = M := by rw [zero_smul, add_zero]
  rw [e] at h
  exact h

end GlobalTheory.FinDecompLim
end

noncomputable section
namespace GlobalTheory.FinDecompLim

open Filter Topology

theorem tendsto_loc_idemS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J),
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K - 1) = 0) →
    Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idemS F T) (GlobalTheory.FinDecomp.idemS_mul_self T) K) Filter.atTop (nhds K) := by
  intro F E _ _ _ _ _ σ d J K hK
  have hM : pairA F 1 0 • (mat K - 1) = 0 := hK _ at_infIdem
  have hN : pairA F 1 0 • (mat K⁻¹ - 1) = 0 := by
    have h : mat K⁻¹ - 1 = mat K⁻¹ * (1 - mat K) := by
      rw [Matrix.mul_sub, Matrix.mul_one, GlobalTheory.FinDecomp.mat_inv_mul]
    rw [h, ← Matrix.mul_smul, ← neg_sub (mat K), smul_neg, hM, neg_zero, Matrix.mul_zero]
  rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  change Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K),
        MulOpposite.op (GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idemS F T) (mat K⁻¹)))) atTop
      (𝓝 (mat K, MulOpposite.op (mat K⁻¹)))
  exact (tendsto_phi _ hM).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_phi _ hN))

end GlobalTheory.FinDecompLim
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem ga_eq_of_match {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} {W : G'.Weil} {G : GlobalTheory.Grid.GridPre R} (hM : GlobalTheory.GridJoin.Match G W) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : GA D (G.V i j).V = GA D (G'.V (.grid i j)) := by
  obtain ⟨L, h1, h2, e⟩ := (hM.1.vert i j hi hj).sp
  rw [e]; rfl

end GlobalTheory.FlipRun
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipDown

theorem kernel_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (eA : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (eB : GA D (G.V i j).V = GA D (G'.V (.grid i j)))
    (Ψ : WO (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) → ℂ), IsThetaFunO W.ψ (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) Ψ →
    ∃ Φ : WO (G.V i j).V (G.V i (j + 1)).V → ℂ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ ∧
      ∀ h g, thetaKO (G.th t i j).ω h g Φ = W.kerA (.down t i j) Ψ (cast eA g) (cast eB h) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW G hG hM t i j hi hj eA eB Ψ hΨ
  obtain ⟨L1, a1, b1, e1⟩ := (hM.1.vert i j hi (by omega)).sp
  obtain ⟨L2, a2, b2, e2⟩ := (hM.1.vert i (j + 1) hi (by omega)).sp
  have hω := hM.2.omT t i j hi hj
  revert eA eB hω
  generalize (G.th t i j).ω = ω
  revert ω
  generalize (G.V i j).V = S at e1 ⊢
  generalize (G.V i (j + 1)).V = U at e2 ⊢
  subst e1 e2
  intro ω eA eB hω
  have hω' : ω = W.om (.mu t i j) := eq_of_heq hω
  subst hω'
  refine ⟨Ψ, ?_, fun h g => rfl⟩
  rw [← hW.ψ]
  exact ⟨hΨ.1, hΨ.2, hΨ.3, hΨ.4⟩

end GlobalTheory.FlipDown
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.IoPhase

open GlobalTheory.ConjLiftUnique

theorem isONBasis_of_adapted {n : ℕ} {G B : Mn n} (h : IsAdapted G 1 B) : IsONBasis G 1 B n := by
  obtain ⟨ε, h1, h2⟩ := h
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have c : Formalism.REAL.Jm ε * (Bᴴ * G) * B = 1 := by rw [Matrix.mul_assoc, h1, hJ]
  have e : Formalism.REAL.Jm ε = 1 := by
    calc Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Bᴴ * G) * B * Formalism.REAL.Jm ε := by rw [c, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc _ B, ← h2, Matrix.one_mul, c]
  exact ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [h1, e], by simp⟩

theorem io_eq_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}
    (hω : IsWeilDatumO ψ V W χV χW ω) (h1 : Formalism.IndefR.FWT.LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    (hc : c.Is) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)) (ht : ∀ P, IsThetaFunO ψ V W (pt P))
    (hinj : Function.Injective pt) {Δ : PolF D W.rank V.rank}
    {io io' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    (hio' : IsIoW θ M c ω pt Δ io') : ∃ a : ℂ, ‖a‖ = 1 ∧ io' = a • io := by
  classical
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W := io.compr₂ (pt.codRestrict (thetaSub ψ V W) ht)
  let F' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W := io'.compr₂ (pt.codRestrict (thetaSub ψ V W) ht)
  have f1 : ∀ x w, (F x w).1 = pt (io x w) := fun _ _ => rfl
  have f2 : ∀ x w, (F' x w).1 = pt (io' x w) := fun _ _ => rfl
  clear_value F F'
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  have hF' : Eqv θ ω F' := ⟨fun u hu x w => by rw [f2, f2, hio'.1 u hu],
    fun τ k hk v u hu w => by rw [f2, f2, hio'.2.1 τ k hk v u hu]⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₁, w₁, n1', n2', e'⟩ := hio'.2.2
  obtain ⟨b, hb⟩ := exists_invForm hω
  obtain ⟨c₁, k1⟩ := exists_const_of_eqv h1 h2 hc hb hF hF w₀ n2
  obtain ⟨c₂, k2⟩ := exists_const_of_eqv h1 h2 hc hb hF' hF' w₀ n2
  obtain ⟨c₃, k3⟩ := exists_const_of_eqv h1 h2 hc hb hF hF' w₀ n2
  obtain ⟨κ, hκ, hk⟩ := exists_phase b hb.symm hb.pos hb.defin (fun v w => F (PiTensorProduct.tprod ℂ v) w)
    (fun v w => F' (PiTensorProduct.tprod ℂ v) w) k1 k2 k3 n1 n1' n2 n2' (l := 1) norm_one
    (Subtype.ext (by rw [one_smul, f1, f2, e, e']))
  have hFF : F' = κ • F := PiTensorProduct.ext (MultilinearMap.ext fun v => LinearMap.ext (hk v))
  refine ⟨κ, hκ, LinearMap.ext fun x => LinearMap.ext fun w => hinj ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← f1, ← f2, hFF]
  rfl

theorem ioUniq (D : D7) : IoUniq D := by
  intro i M M' ψ θ χS χT ω hθ hω _ c hc _ BV f hf io io' hio hio'
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h : ∃ ρ, tauE D ρ = σ
    · exact ⟨h.choose⟩
    · exact ⟨(not_not.1 fun h' => h ((GlobalTheory.PointAtPlace.tauE_cm σ).2 h')).choose⟩
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ M' fun τ =>
    GlobalTheory.LowSmooth.shape_at M' τ (D.hc τ) (Formalism.IndefR.FWT.rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ) rfl
  have hB := fun τ => isONBasis_of_adapted (hf τ).onS
  exact io_eq_smul hω hlow.1 hlow.2 hc _
    (GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M') (onb M') (hf τ₀).theta)
    (GlobalTheory.FockIndep.pureTensorO_injective D ψ θ _ _ _ M' BV f hω.std hθ
      (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hB τ)) hB (hf τ₀).theta (hf τ₀).ne fun τ => (hf τ).vac) hio hio'

theorem ioUniq_of_discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoUniq D :=
  fun _ _ => ioUniq

end GlobalTheory.ArchRec.IoPhase

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.CuspKFin

variable {D : D7}

def KFinAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
    (ρ : Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) W),
    GlobalTheory.Published.AutFin.IsContRep ρ ∧ GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) ρ ψ

end GlobalTheory.CuspKFin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SupVal

theorem tprod_ne_zero' {κ : Type} [Fintype κ] {E : κ → Type} [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {v : ∀ j, E j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem exists_bound_half_lt : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)), GlobalTheory.Unf.Vol V → ∀ t ∈ MultT θ M J 1, t ≠ 0 →
    ∀ w : M.Vec, (∀ τ, (w τ : M.H τ) ≠ 0) → ∃ b : ℝ, ∃ x : GA D V,
      (∀ h, ‖t (PiTensorProduct.tprod ℂ w) h‖ ≤ b) ∧ b / 2 < ‖t (PiTensorProduct.tprod ℂ w) x‖ := by
  intro hP D θ hθ V S M J vol t ht ht0 w hw
  have hw' : PiTensorProduct.tprod ℂ w ≠ 0 :=
    tprod_ne_zero' fun τ h => hw τ (by simp [h])
  have hS := GlobalTheory.T.schurMult_multiplicitySpaces_of_rapidDecay hP D θ hθ V S M J 1 vol.μ vol.𝓕 vol.haar vol.fund
  set φ := t (PiTensorProduct.tprod ℂ w) with hφ
  have hφ0 : φ ≠ 0 := fun h => ht0 (GlobalTheory.T.multiplicitySpace_eq_zero_of_apply_nonzero_tensor_zero θ M J 1 vol.μ vol.𝓕 hθ vol.haar vol.fund hS t ht _ hw' h)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)
  have hR := (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J 1 t ht
    (PiTensorProduct.tprod ℂ w)).2.2
  obtain ⟨C, hC⟩ := hR.2.2 0
  have hbdd : BddAbove (Set.range fun g => ‖φ g‖) := ⟨C, by
    rintro _ ⟨g, rfl⟩
    simpa using hC g⟩
  have hle : ∀ h, ‖φ h‖ ≤ sSup (Set.range fun g => ‖φ g‖) := fun h => le_csSup hbdd ⟨h, rfl⟩
  have hpos : 0 < sSup (Set.range fun g => ‖φ g‖) := lt_of_lt_of_le (norm_pos_iff.2 hx₀) (hle x₀)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) (half_lt_self hpos)
  exact ⟨_, x, hle, hx⟩

end GlobalTheory.SupVal
end
end
