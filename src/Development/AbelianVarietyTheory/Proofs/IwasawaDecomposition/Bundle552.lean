module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle546
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle475
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EisGEqZeroOfInfinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle019
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrderThree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle535
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeanSquareEvenThetaTwelfthRootInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle891
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle880
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle903
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle548
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle545
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasLev
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob GlobalTheory.Mem.TruePeriods GlobalTheory.Mem.PeriodTie

theorem omTied_retie_of_cube {D : D7} (hF : FieldOK D.host D.what₂.embLL D.embE) (h3 : ∀ z : ℂ, z ^ 3 = 1 → z ∈ coefM D) {δ : ℂ}
    (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (retie D) δ := by
  obtain ⟨δ', h', m2, m3⟩ := exists_delta_data D hF
  have h0 := delta_ne_zero h'
  have hu0 : δ / δ' ≠ 0 := div_ne_zero (delta_ne_zero h) h0
  have hu : (δ / δ') ^ 12 = 1 := by
    unfold IsDiscriminantTwelfthRootOfIdealLattice at h h'
    rw [div_pow, h, ← h', div_self (pow_ne_zero _ h0)]
  have hmap : lamOf D D.host.ccK δ = (lamOf D D.host.ccK δ').map (AddMonoidHom.mulLeft (δ / δ')) := by
    rw [lamOf_eq_map, lamOf_eq_map, AddSubgroup.map_map]
    congr 1
    ext; simp [← mul_assoc, div_mul_cancel₀ _ h0]
  generalize δ / δ' = u at hu0 hu hmap
  refine (ties_of_data hF h ?_ ?_).1
  · have e : g2 (lamOf D D.host.ccK δ) = (u ^ 4)⁻¹ * g2 (lamOf D D.host.ccK δ') := by
      unfold g2
      rw [hmap, Model.eisG_map _ _ hu0]; ring
    rw [e]
    exact mul_mem (inv_mem (h3 _ (by rw [← pow_mul, hu]))) m2
  · have e : g3 (lamOf D D.host.ccK δ) = (u ^ 6)⁻¹ * g3 (lamOf D D.host.ccK δ') := by
      unfold g3
      rw [hmap, Model.eisG_map _ _ hu0]; ring
    rw [e]
    refine mul_mem (inv_mem ?_) m3
    rcases sq_eq_one_iff.1 (show (u ^ 6) ^ 2 = 1 by rw [← pow_mul, hu]) with e | e <;> rw [e]
    · exact one_mem _
    · exact neg_mem (one_mem _)

open GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC in

theorem omTied_withTrue {B : Base} {C : Cols B} (hF : FieldOK B.host B.embLL B.embE) (hc : B.host.ccK = ⊤) {δ : ℂ}
    (h : Th.IsDiscriminantTwelfthRootOfIdealLattice B.host ⊤ δ) (Z : Later B C) (hZ : Z.G.gx = Per.trueGx B.host B.embLL B.embE (Equiv.refl _)) :
    Formalism.L2.GlobalTheoryTheory.OmegaCompatible (recOf Z) δ := by
  have h1 : IsDiscriminantTwelfthRootOfIdealLattice (recOf Z) (recOf Z).host.ccK δ := by
    have : (recOf Z).host.ccK = ⊤ := hc
    rw [this]; exact h
  have h2 := omTied_retie_of_cube (D := recOf Z) hF (fun z hz => B.fixedField_le_coefficientField (B.KsC_le_LL0C (B.rootsField_le_KsC
    ((le_sup_right.trans le_sup_left : Fld.cycField (3 ^ 4) ≤ Fld.rootsField B.toPre)
      (Fld.mem_cycField (by norm_num) (by rw [show 3 ^ 4 = 3 * 27 by norm_num, pow_mul, hz, one_pow])))))) h1
  obtain ⟨W, V, S, N, G⟩ := Z
  obtain ⟨M, i, e, a, b, c⟩ := h2
  refine ⟨M, i, e, a, b, fun τ => ?_⟩
  obtain ⟨d, hd, hs⟩ := c τ
  refine ⟨d, hd, fun s => ?_⟩
  have : (recOf (⟨W, V, S, N, G⟩ : Later B C)).gx = G.gx := rfl
  rw [this, show G.gx = _ from hZ]
  exact hs s

section Stages

open Formalism.MainNotions.G Formalism.L2.G IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.ConcreteRecord GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}



theorem isLocalFamily_stages (sc : Scale) (Z Z' : Later B C) (L0 : LevelData (recOf Z)) (T : ∀ u, Forms0 (recOf Z) u) (g)
    (h : IsLocalFamily sc (recOf Z) L0 T g) : IsLocalFamily sc (recOf Z') L0 (fun u => forms0Re Z' (T u)) g := by
  run_tac do
    let m ← Lean.Elab.Tactic.getMainGoal
    m.withContext do m.assign (← Lean.Meta.getFVarFromUserName `h)

end Stages

section Main

open Formalism.MainNotions.G Formalism.L2.G IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.ConcreteRecord GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top.GroupRetwisting

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

theorem companion_of_colsHermS {D : D7} (H : Formalism.L2.Herm.ColsHermS D) : Companion D H.base.lev0 := fun u =>
  have hi : IsIntegral ℤ (D.host.conj ((H.atT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  ⟨Ideal.span {(⟨_, hi⟩ : 𝓞 D.host.E)}, (H.baseL u ⟨_, hi⟩ rfl).1⟩

theorem exists_gTiedS_heq {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (H0 : Formalism.L2.Herm.Herm0 D) (h : H0.lev0 = H.lev0) :
    ∃ g : Formalism.L2.Herm.SymmetricGroupCompatibility D H, HEq g H0.g := by
  obtain ⟨l, g⟩ := H0
  dsimp only at h
  subst h
  exact ⟨g, HEq.rfl⟩

theorem herm0_eq_to0 {D : D7} (X : Formalism.L2.Herm.FullTiedS D) (H0 : Formalism.L2.Herm.Herm0 D) (h : X.base.lev0 = H0.lev0)
    (hg : HEq X.g H0.g) : H0 = X.to0 := by
  obtain ⟨l, g⟩ := H0
  dsimp only at h hg
  subst h
  obtain rfl := eq_of_heq hg
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem columnLocalData_of_levelZero_concreteData (w : ColW B f T) (Z : w.Lt) (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C)
    (hL : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)) (hV : Formalism.L2.Herm.VolumeCompatible (w.D Z)) (hO : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D Z) w.I.J.δ)
    (Gt : GatTies (w.D Z)) (c : LatCmp (w.D Z)) (G : GroupCompatibilityAll (w.D Z) Gt c) (hR : IsRecG K.s (w.D Z) Gt c G.herm G.forms)
    (hl : G.herm.lev0 = C.herm.base.lev0) (hf : G.forms = fun u => (C.forms u).to0)
    (hpl : ∀ u v hg (a : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' a)) (x : 𝓞 (w.D Z).host.F),
      x ∈ ((G.herm.g u v hg).pl a).1.asIdeal ↔ (0 : WithTop ℤ) < (w.D Z).what₂.places.val v
        (tauLL (w.D Z) (Gt.gat_pos u v hg ⟨a, s⟩) (algebraMap (w.D Z).host.F (w.D Z).host.E (x : (w.D Z).host.F)))) :
    Nonempty (ColumnDataSplitPrimes K w Z) := by
  obtain ⟨g, hg⟩ := exists_gTiedS_heq C.herm.base G.herm hl
  obtain ⟨Fu, h1, h2⟩ := GlobalTheory.T.exists_fullHermitianColumns_trueColumns w.I w.ok w.pins w.l Z C g hC hV
  have e : Fu.1.base.lev0 = G.herm.lev0 :=
    (congrArg (fun H : Formalism.L2.Herm.ColsHermS (w.D Z) => H.base.lev0) Fu.2).trans hl.symm
  exact ⟨⟨⟨C, hC, hL, Fu, h2, Gt, c, G, herm0_eq_to0 Fu.1 G.herm e (h1.trans hg), hf,
    gPlTiedS_of G.herm hpl _ _ e (h1.trans hg)⟩, hR, hO⟩⟩



theorem nonempty_columnLocalData_of_standardConcreteFamily (w : ColW B f T) (Z : w.Lt) (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C)
    (hL : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)) (g) (hd)
    (h : IsLocalFamily K.s (w.D Z) C.herm.base.lev0 (fun u => (C.forms u).to0) g)
    (hV : Formalism.L2.Herm.VolumeCompatible (w.D { Z with G := { Z.G with gat := g, gat_d := hd } }))
    (hO : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D { Z with G := { Z.G with gat := g, gat_d := hd } }) w.I.J.δ) :
    Nonempty (ColumnDataSplitPrimes K w { Z with G := { Z.G with gat := g, gat_d := hd } }) := by
  obtain ⟨Gt, c, G, hR, hl, hf, hpl⟩ := isRecG_of_isLocalFamily C.joint0
    (fun u => GlobalTheory.T.exists_psi0_eq_embLL w.I w.ok w.pins w.l Z (C.forms u).gl (hC u).gl) hd h
  exact columnLocalData_of_levelZero_concreteData w _ (colsRe _ C) (stdC_colsRe w.I w.l _ C hC) (fun u => stdLvC_colsRe w.I w.l _ C u (hL u)) hV hO Gt c G hR
    (funext hl) (funext fun u => (hf u).trans ((forms0Re_setGat g hd _).symm.trans (columnFormsAlongLaterStages_stageZero_eq _ C u).symm)) hpl



theorem exists_trueVolume_stage_of_any_column_choice (p : WP) : StepW p fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := by
  refine StepW.of_all fun K B f T w hO _ _ => ?_
  obtain ⟨Z₀⟩ := TrueColsTest.later w.l (JetEx.hasLetters_of_over hO)
  obtain ⟨C, hC, hL⟩ := GlobalTheory.T.exists_standardColumnComparisons_trueColumns w.I w.ok w.pins w.l Z₀
  obtain ⟨g, hd, h⟩ := exists_isLocalFamily K.s (D := w.D Z₀) (fun u => (C.forms u).to0) C.herm.std (companion_of_colsHermS C.herm)
    C.joint0 fun u => GlobalTheory.T.exists_psi0_eq_embLL w.I w.ok w.pins w.l Z₀ (C.forms u).gl (hC u).gl
  refine ⟨{ Z₀.G.withTrue with gat := g, gat_d := hd }, (LayerTwoModel.gIs2_iff w _).2 fun W V S N => ?_⟩
  have hV : Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, { Z₀.G.withTrue with gat := g, gat_d := hd }⟩) :=
    GlobalTheory.T.volumesAgreeAdelic_of_trueVolume _ fun _ => rfl
  refine ⟨hV, nonempty_columnLocalData_of_standardConcreteFamily w ⟨W, V, S, N, Z₀.G.withTrue⟩ (colsRe _ C) (stdC_colsRe w.I w.l _ C hC)
    (fun u => stdLvC_colsRe w.I w.l _ C u (hL u)) g hd ?_ hV.hermVolTied
    (omTied_withTrue w.fld w.px.ccK_top w.ok.amb_ok.delta _ rfl)⟩
  have h' := isLocalFamily_stages K.s Z₀ ⟨W, V, S, N, Z₀.G.withTrue⟩ _ _ g h
  exact (congrArg (fun F => IsLocalFamily K.s (recOf ⟨W, V, S, N, Z₀.G.withTrue⟩) C.herm.base.lev0 F g)
    (funext (columnFormsAlongLaterStages_stageZero_eq ⟨W, V, S, N, Z₀.G.withTrue⟩ C))).mpr h'

theorem exists_trueVolumeStage_columnChoiceStep : StepW Pinned fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := exists_trueVolume_stage_of_any_column_choice Pinned

end Main

end GlobalTheory.Mem.Top.Bl.TrueLocal

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct




namespace GlobalTheory.GeoTie.CuspLev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem heckeIs_of_levels (Z : GlobalTheory.SeriesTie.ExportTie YS v₀) (hev : fw.Evaluates)
    (hLev : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hHW : Rl.toRealDat.models_HW) (hU : Rl.toRealDat.LUnif) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (hRd' : ∀ hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j,
      GlobalTheory.HeckeSup.ReadsCusp T0 Rl.toRealDat κ j (res T0 (sg0 D A3.A)) hV)
    (hS : ∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)))
    (hHT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P) :
    ∃ (c : FractionRing (D.ntw.O i)),
      Z.ρ.e i b c = (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) ^ k ∧ (∃ n : ℕ, n ≠ 0 ∧ c ^ n = 1) ∧
      ‖embC YS iC b (hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV)‖ = 1 ∧
      HeckeIs YS fw iC b j k P ((iC c)⁻¹ * embC YS iC b (hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV)) := by
  obtain ⟨hk1, hkr, hPs, hPS0⟩ := hk

  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun c => congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)
  have hres : res T0 (sg0 D A3.A) = T0.σ₀ := by
    rw [hsg]; exact res_embLL T0 fw.alg_eq fw.laws.pins.2.2.1
  have hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j :=
    fw.laws.spaceW _ (inR j) _ (base_embedding_good T0 Rl.toRealDat fw.alg_eq fw.laws.pins.2.2.1)
  have hRd := hRd' hV
  have hν : Z.ν i j b ≠ 0 := (Z.scalar i j b).ne
  have hinj : Function.Injective (Z.rd i j b) :=
    (GlobalTheory.SeriesTie.realRd_faithful D Γ Pl0 I0 T1 A3 T0.Q.c.F Rl cG S YS v₀ Z.ρ Z.good i j b (Z.ν i j b) hν hU
      hHW (Z.vec j) hK).injective

  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hPS0 (D.ntw.placesOver_subset_exceptional i 0 h)
    · exact hPS0 (D.ntw.placesOver_subset_exceptional i 1 h)
  have hoff : ¬ charAt P ∣ T0.Q.l.M' := GlobalTheory.HeckeSup.not_dvd_level fw.laws (charAt_mem P) hg
  have hso := hS P hPs hPS0
  have hsplit : P.asIdeal ⊔ P.asIdeal.map (T0.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ :=
    GlobalTheory.HeckeSup.split_of_ne hso.1
  have hSO : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.IsSplitOff T0.Q.l P.asIdeal (charAt P) :=
    ⟨P.isMaximal, hsplit, charAt_prime P, charAt_mem P, hoff⟩
  have hHP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P) :=
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsplit, charAt_prime P, charAt_mem P, hoff⟩

  have hn : (κ j).n = D.R.nV := (fw.kap j (D.eTau.symm 1)).2.2
  set cq : T0.Q.c.F := ((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2) with hcq
  set s : T0.Q.c.F := hkScal T0.Q.c cq P.asIdeal k D.R.nV with hs
  have htr : ∀ x : NX.FmK S ((j : ℕ) + 1), ∃ g ∈ T0.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) g := by
    intro x
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hHT GlobalTheory.HeckePointLaw.heckePointLaws fw.laws j hSO hkr cq
      (dom_wtA (κ j)) _ (cuspOf YS fw j x).2
    rw [show hkScal T0.Q.c cq P.asIdeal k (κ j).n = s by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose G hG hGt using htr
  let x' : NX.FmK S ((j : ℕ) + 1) → NX.FmK S ((j : ℕ) + 1) := fun x => (cuspOf YS fw j).symm ⟨G x, hG x⟩
  have hx' : ∀ x, (cuspOf YS fw j (x' x) : T0.R ((j : ℕ) + 1)) = G x := fun x => by
    simp only [x', AddEquiv.apply_symm_apply]

  obtain ⟨α₀, R₀, z₀, d₀⟩ := GlobalTheory.HeckeDatumExists.exists_isHeckeDatum D D.nd D.ntw Z.ρ Z.good i j b k P ⟨hk1, hkr, hPs, hPS0⟩
  obtain ⟨c, hc, N, hN, hcN⟩ := exists_delta_root Z.good i j b z₀
  have hPg : Bridge.SplitOff P (((Z.ρ.B i j b).G.Pg : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main Z.good i _ (fun P' hP' => by
      obtain ⟨k', hk'⟩ := Z.good.Pg i j b P' hP'
      exact D.ntw.placesOver_subset_exceptional i k' hk') P hPs hPS0
  have hdQ : Bridge.SplitOff P (((Z.ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main Z.good i _ (fun P' hP' => by
      rw [Z.good.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (GlobalTheory.SeriesTie.mem_half.1 hP').1) P hPs hPS0

  have hPgS : GlobalTheory.ExportSeries.SplitSet (Z.ρ.B i j b).G.Pg := by
    obtain ⟨Q', hPgQ, -, hQs⟩ := (Z.good.base i j b).places.split
    exact hQs.mono hPgQ
  have hde : ∀ α R z, Z.ρ.IsHeckeDatum i j b k P α R z → (((Z.ρ.B i j b).de.chi z : Circle) : ℂ) = Z.ρ.e i b c :=
    fun α R z d => by
      rw [hc, GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z (Z.pin.delta i j b) (Z.good.base i j b).de.unram
          (Z.good.base i j b).de.split hdQ d.elt d.det,
        GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (Z.pin.delta i j b) (Z.good.base i j b).de.unram
          (Z.good.base i j b).de.split hdQ d₀.elt d₀.det]
  have hchr' : ChrEq (Z.ρ.B i j b).mu0 (Rl.C.mu0 j) := by rw [Z.pin.mu0 i j b]; exact hLev.mu0 j
  have hmu0 : ∀ α R z, Z.ρ.IsHeckeDatum i j b k P α R z →
      (((Z.ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k :=
    fun α R z d => GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α z hchr' (Z.good.base i j b).unram hPgS hPg d.elt d.det
  have hrank : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hdiv : k * D.R.nV / 2 = k * (D.R.nV / 2) := Nat.mul_div_assoc _ (even_iff_two_dvd.1 (kapDom D).2)

  have hkey : ∀ (a : NX.KB S i b) (x : NX.FmK S ((j : ℕ) + 1)),
      D.nexp.hkF i _ b k P ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x)) = c⁻¹ • (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x' x) := by
    intro a x
    refine GlobalTheory.SeriesTie.HeckeTie.eq (Z.hecke i j b) hinj ⟨hk1, hkr, hPs, hPS0⟩ d₀ ?_
    intro α R z d
    have hdc := d.reps
    rw [GlobalTheory.SeriesTie.levK_eq_levG_triv Rl Z.pin i j b] at hdc
    have hset : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T0 Rl.toRealDat j P (charAt P) k α R :=
      ⟨hso, charAt_prime P, charAt_mem P, hoff, hkr, d.elt, hdc⟩
    have hread := hRd P (charAt P) k α R ⟨hso, hg, hkr, d.elt, hdc⟩ hset _ (cuspOf YS fw j x).2 _ (hG x) (hGt x)
    simp only [← GlobalTheory.HeckeSup.hkC_eq (T := T0)] at hread
    funext h
    rw [GlobalTheory.SeriesTie.Setup.hecke_apply, map_smulₛₗ]
    simp only [GlobalTheory.SeriesTie.ExportTie.rd, Pi.smul_apply, smul_eq_mul]
    rw [realRd_eq_phiC YS fw Z.good i j b (Z.ν i j b) hV hev, realRd_eq_phiC YS fw Z.good i j b (Z.ν i j b) hV hev]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx', hread, GlobalTheory.ExportSeries.Base.mu, MonoidHom.mul_apply, Circle.coe_mul, hmu0 α R z d, hde α R z d,
      show Formalism.ConjugateSelfDual.normV P = Nat.card (kP P) from rfl, hrank, ← hdiv, map_inv₀, ← Finset.mul_sum]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt]
    ring
  have hsn : ‖embC YS iC b s‖ = 1 := by
    obtain ⟨p', f', hp', hp'P, hq'⟩ := GlobalTheory.HeckeSup.exists_prime_under P
    have hl : p' ≠ D.ntw.l i := by
      rintro rfl
      exact hPS0 (D.ntw.twistExcludedPlaces_contains_residueChar i hp'P)
    have e1 : Ideal.absNorm P.asIdeal = p' ^ f' := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hq']
    have e2 : Nat.card (kP P) = p' ^ f' := hq'
    have hp1 : ‖((p' : ℕ) : ℂ_[D.ntw.l i])‖ = 1 := by
      rw [← map_natCast (algebraMap ℚ_[D.ntw.l i] ℂ_[D.ntw.l i]) p', norm_algebraMap', Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes (Fact.out : (D.ntw.l i).Prime) hp').2 (Ne.symm hl)
    rw [hs, hkScal, hcq, e1, e2]
    simp only [map_mul, map_pow, map_inv₀, map_natCast, norm_mul, norm_pow, norm_inv, Nat.cast_pow, hp1, one_pow, inv_one,
      mul_one]
  refine ⟨c, hc.trans (GlobalTheory.HeckeDetValue.chr_detAt _ _ _ _ P k α₀ z₀ (Z.pin.delta i j b) (Z.good.base i j b).de.unram
    (Z.good.base i j b).de.split hdQ d₀.elt d₀.det), ⟨N, hN, hcN⟩, hsn, ?_⟩
  intro z quot hq f
  have hfin : Finite (HkKer P.asIdeal (charAt P) k z.1) :=
    GlobalTheory.HeckePointLaw.heckePointLaws.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hHP _ z.1
  obtain ⟨y, rfl⟩ := (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm.surjective f
  rw [LinearEquiv.apply_symm_apply]
  have key : ∀ y : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      valAt YS fw j z.1 (YS.eF i _ b (Nat.le_add_left _ _) j.2
        (D.nexp.hkF i _ b k P ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y))) =
        (iC c)⁻¹ * embC YS iC b s * ∑ᶠ C, valAt YS fw j (quot C) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have e0 : (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 :=
        map_zero _
      have e1 : ∀ C, valAt YS fw j (quot C) (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 := fun C => map_zero _
      rw [e0, map_zero, map_zero, map_zero, finsum_congr e1, finsum_zero, mul_zero]
    | add y y' hy hy' =>
      have ea : (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (y + y') =
          (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y + (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y' := map_add _ _ _
      have eb : ∀ C, valAt YS fw j (quot C) (y + y') = valAt YS fw j (quot C) y + valAt YS fw j (quot C) y' :=
        fun C => map_add _ _ _
      rw [ea, map_add (f := _), map_add (f := _), map_add (f := _), hy, hy', finsum_congr eb, finsum_add_distrib (Set.toFinite _) (Set.toFinite _),
        mul_add]
    | tmul a x =>
      have ea : (YS.eF i _ b (Nat.le_add_left _ _) j.2) ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x' x)) =
          a ⊗ₜ[S.Ks] x' x := LinearEquiv.apply_symm_apply _ _
      rw [hkey, map_smul, ea]
      refine (valAt_smul YS fw j z.1 c⁻¹ _).trans ?_
      rw [valAt_tmul, hx',
        valC_geoHecke YS iC b j hHP s (cuspOf_mem_sec YS fw j x) (hGt x) z.1 quot hq]
      simp only [valAt_tmul]
      rw [← mul_finsum, map_inv₀]
      ring
  exact key y

theorem heckeGeo_of_levels (Z : GlobalTheory.SeriesTie.ExportTie YS v₀) (hev : fw.Evaluates)
    (hLev : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hHW : Rl.toRealDat.models_HW) (hU : Rl.toRealDat.LUnif) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (hRd : ∀ hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j,
      GlobalTheory.HeckeSup.ReadsCusp T0 Rl.toRealDat κ j (res T0 (sg0 D A3.A)) hV)
    (hS : ∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)))
    (hHT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform)
    (hδ : ∀ P, P ∉ D.ntw.S0 i → ∃ s : T0.Q.c.F,
      D.what₂.embLL (algebraMap T0.Q.c.F D.what₂.LL s) = (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)) :
    HeckeGeo YS fw iC b j := by
  intro k P hk
  obtain ⟨c, hc, ⟨N, hN, hcN⟩, hsn, h⟩ := heckeIs_of_levels YS fw iC b j Z hev hLev hHW hU hK hRd hS hHT hk
  obtain ⟨s₁, hs₁⟩ := hδ P hk.2.2.2
  have hs : Z.ρ.e i b (sideK YS i b (s₁ ^ k)) = Z.ρ.e i b c := by
    obtain ⟨a, rfl⟩ := (eKs YS).surjective s₁
    rw [hc, ← hs₁, map_pow, map_pow, sideK_eKs, eKs_LL, ← S.kKs_spec]
    exact congrArg (· ^ k) (Z.good.e_LL0 i b (S.kKs a))
  have hcs : embC YS iC b (s₁ ^ k) = iC c := congrArg iC ((Z.ρ.e i b).injective hs)
  have h1 : ‖iC c‖ ^ N = 1 := by rw [← norm_pow, ← map_pow, hcN, map_one, norm_one]
  have hc1 : ‖iC c‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).1 h1
  refine ⟨(s₁ ^ k)⁻¹ * hkScal T0.Q.c (((Nat.card (kP P) : T0.Q.c.F))⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV, ?_, ?_⟩
  · rw [map_mul, map_inv₀, norm_mul, norm_inv, hcs, hc1, hsn, inv_one, one_mul]
  · rw [map_mul, map_inv₀, hcs]
    exact h

end GlobalTheory.GeoTie.CuspLev

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinksInputs

theorem inputs_of_hypotheses : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, Inputs D := by
  intro hW _ hH hC D
  obtain ⟨hcart, hsd, hsp, hdim, hpet, hsm⟩ := GlobalTheory.Mem.EasyInputs.easy_inputs D
  exact
    { weil := Formalism.IndefR.WeilFull.weilExistsFull_of (hW D) (GlobalTheory.T.weil_datum_fixes_lattice_vacua_at_inert_places D) (GlobalTheory.T.weilDatum_realDerivative_fockVectors_all D)
      vac := GlobalTheory.Member.vacuum_oriented_exists D
      stepVec := GlobalTheory.PlaceDatum.stepVecExists D
      thPVec := GlobalTheory.PlaceVec.thPVecExists D
      ptStable := GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable D
      cartan := hcart
      selfDual := hsd
      vecTheta := GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta D
      measFD := Formalism.IndefR.Eqv.measFDExists_holds D
      measDef := Formalism.IndefR.Eqv.measLevDefExists_holds D
      fund := Formalism.IndefR.Eqv.fundDomExists_holds D
      sp := hsp
      lev := GlobalTheory.Mem.LevelOK.levOK_all D
      hc := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
      schur := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
      pet := hpet
      sm := hsm
      dim := hdim
      act := GlobalTheory.MultAction.actRep D }

end GlobalTheory.LinksInputs

end
end
