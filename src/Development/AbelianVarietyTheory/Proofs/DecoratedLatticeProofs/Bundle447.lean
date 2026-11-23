module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroApproximationTwistPrimes
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle419
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle420
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacter
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle421
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle401
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_approximation_twistPrimes : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (c : {c // A.chOf 0 c = β}) (x : TC.GA B (B.R.N 0)), x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) → ∃ h : TC.GA B (B.R.N 0), h ∈ (A.K 0 (Nat.zero_le _) β).lev.U ∧ h ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (Formalism.L2.Col.colLev I.Ch 0).grp ∧ ∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0, TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) β).y c).1) * (x * h) * TC.kStd X u (B.R.N 0)) q := by
  first | exact @GlobalTheory.ApproxZero.approx_zero | exact GlobalTheory.ApproxZero.approx_zero | (intros; apply GlobalTheory.ApproxZero.approx_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelZeroChartCharacter_eq_memberChartCharacter_stdBase : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (x : (A.K 0 (Nat.zero_le _) β).lev.U) (x' : (C.forms u).to0.cls0.lev.U), x.1 = x'.1 → (A.K 0 (Nat.zero_le _) β).lev.chi x = (C.forms u).to0.cls0.lev.chi x' := by
  first | exact @GlobalTheory.Fam.chi_zero_std | exact GlobalTheory.Fam.chi_zero_std | (intros; apply GlobalTheory.Fam.chi_zero_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_representative_differs_by_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ c : {c // A.chOf 0 c = β}, ∃ κ : (A.K 0 (Nat.zero_le _) β).lev.U, ((C.forms u).to0.cls0.y ((I.eCls0 l u a).symm c.1)).1 = ((A.K 0 (Nat.zero_le _) β).y c).1 * κ.1 ∧ (A.K 0 (Nat.zero_le _) β).lev.chi κ = 1 := by
  first | exact @GlobalTheory.Fam.rep_zero_std | exact GlobalTheory.Fam.rep_zero_std | (intros; apply GlobalTheory.Fam.rep_zero_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem _root_.GlobalTheory.T.thetaLiftChainStep_exact_innerProduct : ∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D → SoftQ D → QPeel D → LevInt D → StepExactNS D := by
  first | exact @GlobalTheory.ChainTw.ExactNS.stepExactNS | exact GlobalTheory.ChainTw.ExactNS.stepExactNS | (intros; apply GlobalTheory.ChainTw.ExactNS.stepExactNS <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel


theorem _root_.GlobalTheory.T.isPlaceModel_tensor_splitPlaceLatticeIndicator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∃ T'' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T'' ∧ ∀ Φ, T'' Φ = T' ((ofSplit P.q).tensorAt P.FS P.FT Φ (Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1)) := by
  first | exact @GlobalTheory.LatIdemVac.isPlaceModel_tensorLat | exact GlobalTheory.LatIdemVac.isPlaceModel_tensorLat | (intros; apply GlobalTheory.LatIdemVac.isPlaceModel_tensorLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_selfDualLineLattice_splitting_sum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S A B : HSp D) (o : OrthDec S A B) (MS : GlobalTheory.FinPl.Lat S) (MA : GlobalTheory.FinPl.Lat A) (Y : Type) [Fintype Y] [DecidableEq Y] (FA : Frame k A.rank Y) (FS : Frame k S.rank (Y ⊕ Unit)) (z : Fin B.rank → k), IsSelfDualC S MS → IsSelfDualC A MA → (∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB) → (∀ r a, FS.β r (Sum.inl a) = (o.iA.map (ofSplit q).pr * FA.β) r a) → (∀ r, FS.β r (Sum.inr ()) = (o.iB.map (ofSplit q).pr *ᵥ z) r) → IntIn q S FS MS → IntIn q A FA MA → ∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB ∧ GlobalTheory.FinPl.OrthAt o MS MA LB q.v ∧ ∀ y : k, (y ∈ 𝒪[k] ↔ (fun i => q.sec (z i * y)) ∈ GlobalTheory.FinPl.latV B LB (· = q.v)) := by
  first | exact @GlobalTheory.LineSplit.exists_lineLat | exact GlobalTheory.LineSplit.exists_lineLat | (intros; apply GlobalTheory.LineSplit.exists_lineLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_move_selfDual_lattice_split_frames : ∀ (D : D7) (S : HSp D) (L₀ : GlobalTheory.FinPl.Lat S), IsSelfDualC S L₀ → ∀ (I : Type) [Finite I] (K : I → Type) [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsNonarchimedeanLocalField (K i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (K i)) (Y : I → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : ∀ i, GlobalTheory.LocMod.Frame (K i) S.rank (Y i)), (∀ i i', (q i).v = (q i').v → i = i') → ∃ L : GlobalTheory.FinPl.Lat S, IsSelfDualC S L ∧ ∀ i, IntIn (q i) S (F i) L := by
  first | exact @GlobalTheory.SplitLat.exists_selfDual_frames | exact GlobalTheory.SplitLat.exists_selfDual_frames | (intros; apply GlobalTheory.SplitLat.exists_selfDual_frames <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero



theorem latV_normalFrame_zero_loc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → ∀ (a : ℕ) (ha : 0 + a = G.s + 1) (Λ L : GlobalTheory.FinPl.Lat (c.V 0)), Formalism.L2.DIV.IsFrame β Λ → GlobalTheory.FinPl.Moves (c.V 0) b Λ L (· = G.q.v) → ∀ y : XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin a → G.k, (fun r => G.q.sec (((G.FY 0 a ha).β *ᵥ y) r)) ∈ GlobalTheory.FinPl.latV (c.V 0) L (· = G.q.v) ↔ (∀ z, y (Sum.inl z) ∈ 𝒪[G.k]) ∧ ∀ i : Fin a, ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k] := by
  intro D c v G PP b β hloc n hn Λ L hβ hmv y
  obtain rfl : n = G.s + 1 := by omega
  obtain ⟨e, -, hM⟩ := hloc.frame (G.s + 1) hn
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.LocMod.PinEx.exists_topFrame G.q hloc.idem (c.V 0) Λ β hβ
  have hb := GlobalTheory.LocMod.liftM_map β.val
  have h1 := hM _ hb
  have h2 := hB1 _ hb
  rw [GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul] at h2
  rw [Matrix.map_mul, h2] at h1
  let ε := e.symm.trans (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hn)
  let X := (G.FY 0 (G.s + 1) hn).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn).val
  let P := (mt (c.V 0) b).map G.q.pr
  let Pi := (mt (c.V 0) b⁻¹).map G.q.pr
  have h1' : P * B.val = X.submatrix id ε := h1
  have hPPi : P * Pi = 1 := by
    change (mt (c.V 0) b).map G.q.pr * (mt (c.V 0) b⁻¹).map G.q.pr = 1
    rw [← Matrix.map_mul, ← GlobalTheory.LocMod.mt_mul_gaMat, mul_inv_cancel, GlobalTheory.LocMod.mt_one_gaMat,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hPiP : Pi * P = 1 := by
    change (mt (c.V 0) b⁻¹).map G.q.pr * (mt (c.V 0) b).map G.q.pr = 1
    rw [← Matrix.map_mul, ← GlobalTheory.LocMod.mt_mul_gaMat, inv_mul_cancel, GlobalTheory.LocMod.mt_one_gaMat,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : X = (P * B.val).submatrix id ε.symm := by
    rw [h1', submatrix_submatrix, Function.comp_id, Equiv.self_comp_symm, submatrix_id_id]
  let z := (((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn)⁻¹).val *ᵥ y
  have hw : (G.FY 0 (G.s + 1) hn).β *ᵥ y = (P * B.val) *ᵥ (z ∘ ε) := by
    have e1 : (G.FY 0 (G.s + 1) hn).β *ᵥ y = X *ᵥ z := by
      change _ = ((G.FY 0 (G.s + 1) hn).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn).val) *ᵥ
        ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn)⁻¹).val *ᵥ y)
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [e1, hX, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_id]
  have key : (fun r => G.q.sec (((G.FY 0 (G.s + 1) hn).β *ᵥ y) r)) =
      mt (c.V 0) b *ᵥ (fun r => G.q.sec ((Pi *ᵥ ((G.FY 0 (G.s + 1) hn).β *ᵥ y)) r)) := by
    rw [GlobalTheory.Core.Mi.LatMatch.mulVec_sec_split]
    change _ = fun r => G.q.sec ((P *ᵥ (Pi *ᵥ _)) r)
    rw [mulVec_mulVec, hPPi, one_mulVec]
  rw [key, ← hmv _ (fun i => GlobalTheory.FrameGlob.sec_mem_idAt G.q _), hB2, hw, mulVec_mulVec, mulVec_mulVec]
  have hB : (B⁻¹).val * Pi * (P * B.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPiP, Matrix.one_mul, Units.inv_mul]
  rw [hB, one_mulVec]
  have hz : ∀ w, z w = (GlobalTheory.LevZeroUp.scal (Fin D.R.t) G.S.ϖ w)⁻¹ * y w := by
    intro w
    change ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val *ᵥ y) w = _
    rw [GlobalTheory.LevZeroUp.bas_inv_val, mulVec_diagonal]
  have hall : (∀ i, (z ∘ ε) i ∈ 𝒪[G.k]) ↔ ∀ w, z w ∈ 𝒪[G.k] :=
    ⟨fun h w => by simpa using h (ε.symm w), fun h i => h _⟩
  rw [hall, Sum.forall]
  refine and_congr (forall_congr' fun w => ?_) (forall_congr' fun i => ?_)
  · rw [hz]
    simp [GlobalTheory.LevZeroUp.scal]
  · rw [hz]
    rfl

end GlobalTheory.LevZero

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = psiBes c.ψ (c.bes 0 D.R.rS h0).d 1 (vecB (c.bes 0 D.R.rS h0).o (c.bes 0 D.R.rS h0).ζ) n := by
  first | exact @GlobalTheory.LevZeroChar.levChi_eq_psiBes | exact GlobalTheory.LevZeroChar.levChi_eq_psiBes | (intros; apply GlobalTheory.LevZeroChar.levChi_eq_psiBes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdealQuot

theorem intAt_mul {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
  rw [map_mul]
  have hx := ha.2
  have hy := hb.2
  generalize finPart D a = x at hx
  generalize finPart D b = y at hy
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, c, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, d, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, c * d, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem commRing_rearrange_idempotent_fixed_product {R : Type*} [CommRing R] (Y X P Q ε s : R) (e2 : P * Q = Y * X) (hse : ε * s = s) :
    Y * (s * (X * ε)) = P * (Q * s) := by
  linear_combination (Y * X) * hse - s * e2

theorem commGroup_mul_mul_eq_mul_mul_div {R : Type*} [CommRing R] (Y P Q C s a : R) (e2 : P * Q * C = Y) :
    Y * (s * a) = P * ((Q * s) * (C * a)) := by
  linear_combination (-(s * a)) * e2

theorem unit_of_gen {D : D7} {v : Pl D} {c : D.host.E} (hc : c ≠ 0)
    (h : ∀ s, s ∈ idV (1 : FI D) v ↔ incA D c⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) (t : AE D) :
    (t ∈ intAt D (· = v) → incA D c⁻¹ * t ∈ intAt D (· = v)) ∧
      (t ∈ intAt D (· = v) → incA D c * t ∈ intAt D (· = v)) := by
  refine ⟨fun ht => ((h t).1 ((GlobalTheory.SeeSaw.idV_one_eq_intAt D v t).2 ht)).1, fun ht => ?_⟩
  have h1 : incA D c * t ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ht.1
  have h2 : incA D c⁻¹ * (incA D c * t) = t := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  exact (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).1 ((h _).2 ⟨by rw [h2]; exact ht, h1⟩)

theorem mul_subset_iff : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D), 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v),
    (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v := by
  intro D v 𝔞 𝔟 h𝔞 h𝔟 s hs
  obtain ⟨x, hx, gx⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  obtain ⟨y, hy, gy⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔟 h𝔟
  obtain ⟨z, hz, gz⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞⁻¹ (inv_ne_zero h𝔞)
  have gyz := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔟 𝔞⁻¹ y z hy hz gy gz
  have gxz := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔞⁻¹ x z hx hz gx gz
  rw [mul_inv_cancel₀ h𝔞] at gxz
  have hxz : x * z ≠ 0 := mul_ne_zero hx hz
  have u := unit_of_gen hxz gxz
  obtain ⟨ε, -, -, hε, hεa, -⟩ := (GlobalTheory.FinPl.localComponents D (· = v)).1
  rw [gyz]
  constructor
  · intro H
    have hxε : incA D x * ε ∈ idV 𝔞 v := by
      refine (gx _).2 ⟨?_, Ideal.mul_mem_left _ _ hε.1⟩
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
    have h1 := ((gy _).1 (H _ hxε)).1
    have e1 : incA D y⁻¹ * (s * (incA D x * ε)) = incA D (x * z) * (incA D (y * z)⁻¹ * s) := by
      have hse : ε * s = s := (hεa s).1 hs
      have e2 : incA D (x * z) * incA D (y * z)⁻¹ = incA D y⁻¹ * incA D x := by
        rw [← map_mul, ← map_mul]; congr 1; field_simp
      exact commRing_rearrange_idempotent_fixed_product _ _ _ _ _ _ e2 hse
    rw [e1] at h1
    refine ⟨?_, hs⟩
    have := (u _).1 h1
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hxz, map_one, one_mul] at this
  · rintro ⟨H, -⟩ a ha
    obtain ⟨ha1, ha2⟩ := (gx a).1 ha
    refine (gy _).2 ⟨?_, Ideal.mul_mem_right _ _ hs⟩
    have e1 : incA D y⁻¹ * (s * a) = incA D (x * z) * ((incA D (y * z)⁻¹ * s) * (incA D x⁻¹ * a)) := by
      have e2 : incA D (x * z) * incA D (y * z)⁻¹ * incA D x⁻¹ = incA D y⁻¹ := by
        rw [← map_mul, ← map_mul]; congr 1; field_simp
      exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _ _ _ e2
    rw [e1]
    exact (u _).2 (intAt_mul H ha1)

end GlobalTheory.IdealQuot
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.DiUnit

variable {D : D7}

theorem eq_one_iff {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} : idV 𝔞 v = idV 1 v ↔
    ∀ s, s ∈ idV 𝔞 v ↔ incA D (1 : D.host.E)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  simp only [inv_one, map_one, one_mul]
  constructor
  · intro h s
    rw [h, GlobalTheory.SeeSaw.idV_one_eq_intAt]
    exact ⟨fun h => ⟨h, h.1⟩, fun h => h.1⟩
  · intro h
    ext s
    rw [h, GlobalTheory.SeeSaw.idV_one_eq_intAt]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

theorem mul_eq_one {𝔞 𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (h1 : idV 𝔞 v = idV 1 v) (h2 : idV 𝔟 v = idV 1 v) :
    idV (𝔞 * 𝔟) v = idV 1 v := by
  have := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔟 1 1 one_ne_zero one_ne_zero (eq_one_iff.1 h1) (eq_one_iff.1 h2)
  rw [mul_one] at this
  exact eq_one_iff.2 this

theorem pow_eq_one {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} (h : idV 𝔞 v = idV 1 v) (n : ℕ) : idV (𝔞 ^ n) v = idV 1 v := by
  induction n with
  | zero => rw [pow_zero]
  | succ n ih => rw [pow_succ]; exact mul_eq_one ih h

theorem inv_eq_one {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} (h : idV 𝔞 v = idV 1 v) : idV 𝔞⁻¹ v = idV 1 v := by
  have h0 : 𝔞 ≠ 0 := fun e =>
    GlobalTheory.SeeSaw.LiftModel.idV_ne_bot (one_ne_zero (α := FI D)) v (by rw [← h, e, GlobalTheory.SeeSaw.idV_zero])
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞⁻¹ (inv_ne_zero h0)
  have h1 := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔞⁻¹ 1 y one_ne_zero hy0 (eq_one_iff.1 h) hy
  rw [mul_inv_cancel₀ h0, one_mul] at h1
  ext s
  rw [hy, ← h1]

theorem AAbar_eq_one {v : GlobalTheory.FinPl.Pl D} (hA : idV D.host.AA v = idV 1 v) : idV D.host.AAbar v = idV 1 v := by
  ext s
  have h1 := GlobalTheory.SeeSaw.idV_cA_iff D v D.host.AA (cA D s)
  rw [GlobalTheory.SeeSaw.cA_cA, GlobalTheory.SeeSaw.conjFI_AA] at h1
  have h2 := GlobalTheory.SeeSaw.idV_cA_iff D v 1 s
  rw [map_one] at h2
  rw [← h1, hA, h2]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fractionalIdealCompletion_xi0Span_eq_unit_at_splitPlace (p : SplitPt D k) (hp : p.UnitAA) :
    idV (FractionalIdeal.spanSingleton _ D.host.xi0) p.v = idV 1 p.v := by
  have hx : D.host.xi0 ≠ 0 := Formalism.L2.Pj.cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  ext s
  rw [GlobalTheory.SeeSaw.idV_one_eq_intAt]
  constructor
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, a, ha, rfl⟩ := hy
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
      have e : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (r • D.host.xi0) : AE D) =
          incA D D.host.xi0 * (pairA D.host.F 0 α ⊗ₜ[D.host.F] algebraMap (𝓞 D.host.E) D.host.E r) := by
        rw [GlobalTheory.IdVGen.incA_mul_tmul, Algebra.smul_def, mul_comm (algebraMap (𝓞 D.host.E) D.host.E r)]
      rw [e]
      exact (hp.1 _ (GlobalTheory.IdVGen.gen_mem_intAt hα hαv r)).1
    | zero => exact GlobalTheory.IdVGen.intAt_zero' _
    | add a b _ _ ha hb => exact GlobalTheory.IdVGen.intAt_add' ha hb
    | neg a _ ha => exact GlobalTheory.IdVGen.intAt_neg' ha
  · intro hs
    have h3 := (GlobalTheory.SeeSaw.idV_one_eq_intAt D p.v _).2 (hp.1 s hs).2
    have key : ∀ y ∈ idV (1 : FI D) p.v,
        incA D D.host.xi0 * y ∈ idV (FractionalIdeal.spanSingleton _ D.host.xi0) p.v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, hαv, a, ha, rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
        rw [GlobalTheory.IdVGen.incA_mul_tmul]
        refine AddSubgroup.subset_closure ⟨α, hα, hαv, _, ?_, rfl⟩
        exact (FractionalIdeal.mem_spanSingleton _).2 ⟨o, by rw [Algebra.smul_def]; exact mul_comm _ _⟩
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have := key _ h3
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul] at this

theorem AA_eq_one (p : SplitPt D k) (hp : p.UnitAA) : idV D.host.AA p.v = idV 1 p.v := by
  let L : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1
  let ζ : Fin L.rank → D.host.E := fun _ => 1
  have hζ : ζ ≠ 0 := fun e => one_ne_zero (congrFun e ⟨0, by change 0 < 1; decide⟩)
  have e : GlobalTheory.FinPl.latA L (GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 1) (· = p.v) =
      GlobalTheory.FinPl.latV L (GlobalTheory.SeeSaw.LiftModel.lineLat L ζ D.host.AA) (· = p.v) := by
    unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    congr 1
    ext y
    constructor
    · rintro ⟨α, h1, h2, a, ha, _, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨α, h1, h2, 1, rfl, _, ⟨a * c, ?_, rfl⟩, ?_⟩
      · have := FractionalIdeal.mul_mem_mul (S := nonZeroDivisors (𝓞 D.host.E)) (I := D.host.AA) (J := 1) ha hc
        rwa [mul_one] at this
      · funext i; simp [mul_assoc]
    · rintro ⟨α, h1, h2, _, rfl, _, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨α, h1, h2, c, hc, _, ⟨1, FractionalIdeal.one_mem_one _, rfl⟩, ?_⟩
      funext i; simp
  have key : ∀ s ∈ idAt D (· = p.v), s ∈ idV D.host.AA p.v ↔ s ∈ idV 1 p.v := fun s hs => by
    rw [← GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ D.host.AA p.v s hs,
      ← GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ 1 p.v s hs, ← e, hp.2]
  ext s
  exact ⟨fun h => (key s (GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s h)).1 h,
    fun h => (key s (GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s h)).2 h⟩

end GlobalTheory.Core.Mi.LatMatch.DiUnit


open GlobalTheory.Core.Mi.LatMatch.DiUnit in
theorem GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), p.UnitAA → ∀ (n : ℕ) (a : AE D), (a ∈ idV (dI D ^ n) p.v ↔ a ∈ intAt D (· = p.v)) ∧ (a ∈ idV (dI D ^ n)⁻¹ p.v ↔ a ∈ intAt D (· = p.v)) := by
  intro D k _ _ _ _ p hp n a
  have hd : idV (dI D) p.v = idV 1 p.v := by
    have hA := AA_eq_one p hp
    unfold GlobalTheory.SeeSaw.dI
    exact mul_eq_one (mul_eq_one (fractionalIdealCompletion_xi0Span_eq_unit_at_splitPlace p hp) hA) (AAbar_eq_one hA)
  have h1 := pow_eq_one hd n
  have h2 := inv_eq_one h1
  exact ⟨by rw [h1, GlobalTheory.SeeSaw.idV_one_eq_intAt], by rw [h2, GlobalTheory.SeeSaw.idV_one_eq_intAt]⟩

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : GlobalTheory.QPl.QFam v t), F.Pins w → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) → ∀ (μ : Measure (GfC (c.V j))), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D (c.V j))) (b : GA D (c.V j)), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D (c.V j))) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (c.V j))) : Set (GfC (c.V j))) → (∀ κ, InK _ (v.N j) (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g (v.N j) (v.N j) (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i d hd x, (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY j d hd).β * x.val * ((F.Q i).FY j d hd).γ → x ∈ ((F.Q i).T.lev j d hd).J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx j : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) ∧ (IsSelfDualC c.T v.NT → (∀ i, IsOpen ((F.Q i).T.levTop.J : Set (GL (F.Q i).Z (F.Q i).k))) → ∀ (μ : Measure (GfC c.T)), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D c.T)) (b : GA D c.T), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D c.T)) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC c.T)) : Set (GfC c.T)) → (∀ κ, InK _ v.NT (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g v.NT v.NT (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (F.Q i).Z (F.Q i).k), (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ → x ∈ (F.Q i).T.levTop.J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx D.R.m : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) := by
  first | exact @GlobalTheory.LevIdx.vol_level_eq | exact GlobalTheory.LevIdx.vol_level_eq | (intros; apply GlobalTheory.LevIdx.vol_level_eq <;> assumption)
end
