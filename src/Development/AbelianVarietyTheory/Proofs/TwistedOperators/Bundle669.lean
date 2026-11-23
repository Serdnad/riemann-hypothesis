module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle657
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle663
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainTopPairMovedVectorRowCharacter
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle658
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle600
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle616
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle911
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle664
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockSubstitution_columnStep_rename_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC i)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC (i + 1)))
    (Q : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank),
    GlobalTheory.RowReal.trRow G i (GlobalTheory.RowReal.fockSubAll (fun _ => 0) (fun _ => (G.V (.grid i D.R.m)).rank)
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2)))
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trRow G i Q) := by
  first | exact @GlobalTheory.RowReal.trRow_fockSubAll | exact GlobalTheory.RowReal.trRow_fockSubAll | (intros; apply GlobalTheory.RowReal.trRow_fockSubAll <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockSubstitution_rowStep_rename_unitary : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR j)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nR (j + 1)))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank),
    GlobalTheory.RowReal.trCol G j (GlobalTheory.RowReal.fockSubAll (fun _ => (G.V (.top j)).rank) (fun _ => (G.V (.top (j + 1))).rank)
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j) j.2.le)))
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (j := j + 1) j.2))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trCol G j Q) := by
  first | exact @GlobalTheory.RowReal.trCol_fockSubAll_unitary | exact GlobalTheory.RowReal.trCol_fockSubAll_unitary | (intros; apply GlobalTheory.RowReal.trCol_fockSubAll_unitary <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.compactChain_chiPair_movedVector_columnCharacter : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (GlobalTheory.RowReal.ptGrid W g i) (GlobalTheory.RowReal.ptGrid W g (i + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.colScal (GlobalTheory.RowReal.rowEntries D sc.cGap) i g • movedVec t S d := by
  first | exact @GlobalTheory.RowReal.om_ptGrid_movedVec | exact GlobalTheory.RowReal.om_ptGrid_movedVec | (intros; apply GlobalTheory.RowReal.om_ptGrid_movedVec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.compactChain_topPair_movedVector_rowCharacter : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (j : Fin D.R.m)
    (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    W.om (.top t j) (G.toPair (.top t j) (GlobalTheory.RowReal.ptTop W g j) (GlobalTheory.RowReal.ptTop W g (j + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.rowScal (GlobalTheory.RowReal.rowEntries D sc.cGap) j g • movedVec t S d := by
  first | exact @GlobalTheory.RowReal.om_ptTop_movedVec | exact GlobalTheory.RowReal.om_ptTop_movedVec | (intros; apply GlobalTheory.RowReal.om_ptTop_movedVec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GEquivCx



theorem pGEquiv_of_baseW : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.BaseW F.lv2 → R.toRealDat.ExAt → R.PGEquiv F := by
  intro hCR D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hB hE
  have hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2 :=
    ⟨hB.lev, hB.grp, hB.fam, hB.models, RealDat.chain_of_weak hB.chain hE, RealDat.thP_of_weak hB.thP hE⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hCR R.toRealDat F.lv2 hC
  refine ⟨fun t g x => ?_, fun j t g x => ?_⟩
  · exact h1 t g x
  · have e : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t ((A3.A.fam.L j t).r g x)) =
        R.gW j (sg0 D A3.A) g (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t x)) :=
      (congrArg (fun y => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • y) (h2 j t g x)).trans
        (LinearMap.map_smul _ _ _).symm
    exact e

end GlobalTheory.GEquivCx
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepLift

theorem exists_lastStep_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels →
    R.IsChainW → R.ex_ioX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hfam hmod hc
  have hIt : R.chain_ItX := hc.ItX.1 (GlobalTheory.T.exists_lastStep_intertwiner_chain D G Pl0 T A Ks R hlev hfam hmod hc)
  obtain ⟨io, hio⟩ := GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hlev hfam hmod hc.ωX hc.vX hc.ptX hIt
  exact fun t => ⟨io t, hio t⟩

end GlobalTheory.Twist.LastStepLift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixTarget

theorem om_pow_eq_snd {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)) (k : GA D V)
    (f : WO S V → ℂ) (c : ℂ) (hc : om (1, k) f = c • f) : ∀ m : ℕ, om (1, k ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : (((1 : GA D S), k ^ (m + 1)) : GA D S × GA D V) = (1, k ^ m) * (1, k) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

def congGroup {D : D7} (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | GlobalTheory.Member.FinCong V N k}
  one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V N
  mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
  inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha

theorem isOpen_congGroup {D : D7} (V : HSp D) {N : ℕ} (hN : 0 < N) : IsOpen (congGroup V N : Set (GA D V)) :=
  Subgroup.isOpen_of_mem_nhds _ (g := 1) (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN)

end GlobalTheory.VacFixTarget

namespace GlobalTheory.VacFixTarget

open Formalism.L2.Fam.ThC (fixSig)

theorem isThetaFunO_fixSig {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ}
    (h : IsThetaFunO ψ S T f) : IsThetaFunO ψ (fixSig S) (fixSig T) f :=
  ⟨h.quasi, h.level, h.cont, h.smooth⟩

theorem isVacO_fixSig {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : IsVacO ψ θ (fixSig S) (fixSig T) sS sT LS LT f :=
  ⟨h.1, h.2.inf, isThetaFunO_fixSig h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩

end GlobalTheory.VacFixTarget

namespace GlobalTheory.VacFixTarget

open GlobalTheory.Grid (neg)



theorem exists_open_fix_vac_target : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac := by
  intro D T L sc G W i j A A' WW X hX t
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have hvac : IsVacO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ X.vac := hX.is.isVac
  have hθ : IsInfFam W.θ := hvac.2.inf
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hone : ∀ κ : GA D WW, (X.ω t).toSgn true (1, κ) = X.ω t (1, κ) := fun κ => by
    simp [GlobalTheory.Grid.WRep.toSgn]
  have hev := (GlobalTheory.LatNhds.eventually_actO D (neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D (neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D WW => (((1 : GA D (neg A)), x) : GA D (neg A) × GA D WW)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const.prodMk continuous_id :
      Continuous fun x : GA D WW => (((1 : GA D (neg A)), x) : GA D (neg A) × GA D WW))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC WW, GlobalTheory.Member.FinCong WW n.factorial x →
      ∀ u ∈ (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        actO (neg A) WW 1 x u ∈
          (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC WW, GlobalTheory.Member.FinCong WW n₁.factorial k →
      ∃ c : ℂ, ‖c‖ = 1 ∧ (X.ω t).toSgn true (1, k) X.vac = c • X.vac := by
    intro k hk hc
    have hΛ : ∀ u : WO (neg A) WW, u ∈ (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E))
        (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO (neg A) WW
        (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        u = actO (neg A) WW 1 k u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO (neg A) WW 1 k⁻¹ u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO (1 : GA D (neg A)) k⁻¹ u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hW hθ
      (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rW.s X.rW.s _ _ _ _ 1 k
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one (neg A) W.θ τ (-X.rA.s τ))
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ WW hk τ, Matrix.one_mul, Matrix.mul_one]) hΛ X.vac hvac
    exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig (neg A)) (Formalism.L2.Fam.ThC.fixSig WW)
      (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT X.rA.Λ X.rW.Λ
      hsdS hsdT X.vac _ (isVacO_fixSig hvac) (isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D WW => (X.ω t).toSgn true (1, k) X.vac w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_const.prodMk continuous_id)
  have key : ∃ n : ℕ, ∀ k ∈ GfC WW, GlobalTheory.Member.FinCong WW (n₁.factorial * n.factorial) k →
      (X.ω t).toSgn true (1, k) X.vac = X.vac := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, (X.ω t).toSgn true (1, k n ^ m) X.vac = c • X.vac ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (om_pow_eq_snd _ (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup WW (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup WW (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : (X.ω t).toSgn true ((1 : GA D (neg A)), (1 : GA D WW)) X.vac w₀ = X.vac w₀ := by
      show (X.ω t).toSgn true 1 X.vac w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖X.vac w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (X.vac w₀)]
  obtain ⟨n, hn⟩ := key
  refine ⟨congGroup WW (n₁.factorial * n.factorial),
    isOpen_congGroup WW (Nat.mul_pos n₁.factorial_pos n.factorial_pos), fun κ hU hκ => ?_⟩
  rw [← hone]
  exact hn κ hκ hU

end GlobalTheory.VacFixTarget
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.squareFlip_equivariant_blockDiagonal_columnSubstitution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  first | exact @GlobalTheory.SquareFlipCols.squareFlip_blockDiag_cols | exact GlobalTheory.SquareFlipCols.squareFlip_blockDiag_cols | (intros; apply GlobalTheory.SquareFlipCols.squareFlip_blockDiag_cols <;> assumption)
end
