module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle471
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle612
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Formalism.SharpRestriction.GrowthBounds.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle617
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulPrIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle417
import Formalism.LocalToGlobal.Columns.HeckeSpCount
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle283
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle613
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle615
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.BrgRead



theorem embLL_labLL_eq {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem gram_V (X : Stages) (h : DiagSpaces X.toD7.sp) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.toD7.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem isDualPair_smul {D : D7} {θ : InfFam D} {MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)} {cX : CoefA D.sp.X'}
    {prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ} (h : IsDualPair θ MX cX prX) {c : ℂ} (hc : c ≠ 0) :
    IsDualPair θ MX cX (c • prX) := by
  refine ⟨smul_ne_zero hc h.1, fun τ g hg w v u hu => ?_⟩
  simp only [LinearMap.smul_apply]
  rw [h.2 τ g hg w v u hu]

theorem exists_coefData : ∀ (D : D7), Seed.VPos D → ∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
  ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
    (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] cX.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) →ₛₗ[D.what₂.embLL] (cV i).W),
    cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧
    (gramR = D.sp.X'.gram ∨ gramR = -D.sp.X'.gram) ∧
    Bridge.CoefMapTie D.sp.X' cX.coef c0R (rhoV (labLL D) _) ∧
    (∀ i, Bridge.CoefMapTie (Vc D i) (cV i).coef (c0L i) (rhoVr (labLL D) _)) ∧
    (∀ x y, inner ℂ (c0R x) (c0R y) = D.what₂.embLL (pairV (labLL D) _ gramR x y)) ∧
    ∀ i x y, inner ℂ (c0L i x) (c0L i y) = D.what₂.embLL (pairVr (labLL D) _
      (if D.sp.Vneg ((i : ℕ) + 1) then -(Vc D i).gram else (Vc D i).gram) x y) := by
  intro D hV θ hθ MX
  obtain ⟨cX, prX, c0R, gramR, hcX, hdual, hg, hmap, hin⟩ := GlobalTheory.CoefSpace.exists_coef_dualPair D θ MX hθ
  have hL := fun i => GlobalTheory.CoefModel.exists_coef_lift D i (hV i)
  choose cV c0L hcV hmapL hinL using hL
  obtain ⟨c, hc, hiso⟩ := GlobalTheory.PrIsoScale.exists_smul_prIso D θ MX cX prX hθ hcX hdual
  exact ⟨cX, cV, c • prX, gramR, c0R, c0L, hcX, hcV, isDualPair_smul hdual hc, hiso, hg, hmap, hmapL, hin, hinL⟩
theorem hecke_degrees : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px),
    (∀ t P, (famR X I hX U Xg tr).A.heckeR t (P, 0) = 1 ∧
      ∀ k, X.toD7.sp.X'.rank < k → (famR X I hX U Xg tr).A.heckeR t (P, k) = 0) ∧
    (∀ i t P, (famR X I hX U Xg tr).A.heckeL i t (P, 0) = 1 ∧
      ∀ k, (Vc X.toD7 i).rank < k → (famR X I hX U Xg tr).A.heckeL i t (P, k) = 0) := by
  intro X px I hX U Xg tr
  have hk3 := X.B.R.m_add_three_le_k
  refine ⟨fun t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩, fun i t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩⟩
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.X'_rank
    change X.toD7.sp.X'.rank < k at hk
    rw [e] at hk
    change _ < k
    unfold Ranks.rankX' at hk
    unfold Ranks.N
    simp only [Ranks.r] at hk ⊢
    change X.B.R.k + X.B.R.m - 1 + X.B.R.m * X.B.R.t < k at hk
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.V_rank _ (by omega) i.2
    change (X.toD7.sp.V ((i : ℕ) + 1)).rank < k at hk
    rw [e] at hk
    exact hk

theorem exists_brgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∃ (cX : CoefA X.toD7.sp.X') (cV : ∀ i, CoefA (Vc X.toD7 i)) (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ ∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ := by
  intro X px I hX U Xg tr L eG hI hV hL hG hβX hβV hsX hsV θ hθ MX
  have hVP : Seed.VPos X.toD7 := fun i => X.B.V_posDef _ (by omega) i.2
  obtain ⟨cX, cV, prX, gramR, c0R, c0L, hcX, hcV, hdual, hiso, hgram, hmapR, hmapL, hinR, hinL⟩ :=
    exists_coefData X.toD7 hVP θ hθ MX
  have hR := GlobalTheory.T.exists_rowForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hmapR hinR hβX hsX
  have hLf := fun i => GlobalTheory.T.exists_liftForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cV i (c0L i) (hcV i) (hmapL i) (hinL i) (hβV i)
    (gram_V X hI.spaces i) (hsV i)
  obtain ⟨sR, hsR, hstR⟩ := hR
  choose sL hsL hstL using hLf
  obtain ⟨hok, hon, hit, hion⟩ := GlobalTheory.Mem.R3.famR_places X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hmu, heta, hroots⟩ := GlobalTheory.Mem.R3.Brg.values X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hdR, hdL⟩ := hecke_degrees X px I hX U Xg tr
  have hrk : X.toD7.sp.X'.rank = (famR X I hX U Xg tr).A.r + X.toD7.R.m * (famR X I hX U Xg tr).A.t := X.toD7.sp.X'_rank
  have hrkL : ∀ i : Fin X.toD7.R.m, (Vc X.toD7 i).rank = (famR X I hX U Xg tr).A.r + (famR X I hX U Xg tr).A.t :=
    fun i => X.toD7.sp.V_rank _ (by omega) i.2
  let B : Seed.BType (famR X I hX U Xg tr) L cX cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) :=
    { R := sR, L := fun i t => sL i t, rankR := hrk, rankL := hrkL }
  classical
  refine ⟨cX, cV, fun P => P.1, L.Pg, B, fun Q => Q.1, L.Pg.image (fun PP => PP.under (𝓞 X.toD7.host.F)), prX,
    hcX, hcV, hdual, hiso, ?_, hstR, hstL⟩
  exact
    { red_R := fun t q => (hsR t).1 q
      red_L := fun i t q => (hsL i t).1 q
      tie := ⟨gramR, c0R, c0L,
        { ranks := ⟨rfl, rfl, rfl⟩
          v0 := rfl
          tauL_ok := fun τ => RingHom.ext fun x => embLL_labLL_eq τ x
          pl_inj := fun a b h => Subtype.ext h
          q := fun P => rfl
          S_fin := Set.toFinite _
          ok := hok
          gramR_eq := hgram
          mapR := hmapR
          mapL := hmapL
          coefR := fun t => (hsR t).2.1
          coefL := fun i t => (hsL i t).2.1 }⟩
      sb := rfl
      roots := hroots
      pl_onto := hon
      degR := hdR
      degL := hdL
      muVal := hmu
      etaVal := heta
      in_tie := hit
      in_onto := hion
      in_R := fun t => (hsR t).2.2
      in_L := fun i t => (hsL i t).2.2
      in_SF := fun v => by
        simp only [Finset.mem_image]
        refine exists_congr fun PP => and_congr_right fun _ => ?_
        rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, Ideal.under_def] }

end GlobalTheory.Mem.R3.BrgRead

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.comparison_data_steps_non_reference_tuple : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  first | exact @GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne | exact GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne | (intros; apply GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.HeightCounting.Up

theorem nonempty_gridData_allSt : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => Nonempty (GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩) := by
  intro cDep
  unfold AllSt StepW Step
  refine EvG.imp GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices fun K _ _ _ _ H => large₂.mono (fun B f T _ h hk _ _ w _ P x => ?_) H
  obtain ⟨-, -, -, -, -, -, w0, hP⟩ := h hk T w x.o.Z
  refine GlobalTheory.HeightCounting.Up.ListModel.nonempty_grid w x.o.Z x.m.z ⟨1, cDep, K.s.b⟩ fun k e => ?_
  have hd := hP.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hd
  fin_cases k
  · exact hd.1 (Or.inr (Or.inr (Or.inr e.symm)))
  · exact hd.2.1 (Or.inr (Or.inr e.symm))

end GlobalTheory.HeightCounting.Up
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamMetric

theorem inner_theta_eq_lam : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), Used0 D (Y.tup t) → ∀ x ∈ (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → ∀ x', ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t p _ x hx hW x'
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  have hK := GlobalTheory.T.liftThetaMap_orthogonalKernel_eq_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  set K := (LinearMap.ker θ)ᗮ with hKdef
  have hS := GlobalTheory.T.liftThetaMap_labelPartPreimage_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p x (hK ▸ hx) hW

  have hkerK : ∀ z, z - K.starProjection z ∈ LinearMap.ker θ := by
    intro z
    have := K.sub_starProjection_mem_orthogonal z
    rwa [Submodule.orthogonal_orthogonal] at this
  have hKperp : ∀ z, z - K.starProjection z ∈ Kᗮ := fun z => K.sub_starProjection_mem_orthogonal z

  have hgoodK : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ q ∈ K,
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ q⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), q⟫_ℂ := by
    intro a ha q hq
    rw [hK] at hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact GlobalTheory.T.liftThetaMap_inner_eq_lambda_mul_rationalVectors D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p a b ha
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add (f := _), inner_add_right, inner_add_right, h1, h2, mul_add]
    | smul c y _ h => rw [map_smul, inner_smul_right, inner_smul_right, h]; ring
  have hgood : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ x',
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ := by
    intro a ha x'
    have huK : D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) ∈ K := by rw [hK]; exact Submodule.subset_span ⟨a, rfl⟩
    have e1 : θ x' = θ (K.starProjection x') := by
      have := hkerK x'
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e2 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ = ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), K.starProjection x'⟫_ℂ := by
      have h0 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x' - K.starProjection x'⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal huK (hKperp x')
      rw [inner_sub_right, sub_eq_zero] at h0; exact h0
    rw [e1, e2]
    exact hgoodK a ha _ (K.starProjection_apply_mem x')
  clear hx hW
  induction hS using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact hgood a ha x'
  | zero => simp
  | add y z _ _ h1 h2 => rw [map_add (f := _), inner_add_left, inner_add_left, h1, h2, mul_add]
  | smul c y _ h => rw [map_smul, inner_smul_left, inner_smul_left, h]; ring

end GlobalTheory.Mem.R3.LamMetric
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.ReadIndexNumerics

theorem ijIdx_eq (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (S0 : IndefData (A.side P0 ψ0 Zs)) (Xd : DivX D)
    (jW : ∀ i : Fin D.R.m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (i : Fin D.R.m) (t : T) (eW : (Fin (S0.dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t))
    (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) =
      jW i ((S0.θ i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x)))
    (hj : ∀ x, Xd.jM ((i : ℕ) + 1) (eW x) = jW i x)
    (hl : (Xd.MjH ((i : ℕ) + 1)).L = (S0.M i).map ((eW : (Fin (S0.dW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V).restrictScalars (𝓞 D.what₂.LL)))
    (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map
      ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)))
    (w : D.what₂.places.Pl) :
    Idx.IjIdx Xd (tup t) ((i : ℕ) + 1) w = S0.Iw i t (D.plEq w) := by
  have hPE : ∀ z, lPrj D A P0 ψ0 Zs i t *ᵥ (lZ0 D A P0 ψ0 Zs i t *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec]; erw [hP.1]; exact Matrix.one_mulVec z
  have hth : Idx.thTj Xd (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (S0.θ i t) ((A.side P0 ψ0 Zs).Tl i t)).map
      ((eW : (Fin (S0.dW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V).restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    have key : y ∈ Idx.thTj Xd (tup t) ((i : ℕ) + 1) ↔ ∃ x ∈ Idx.TjL D (tup t) ((i : ℕ) + 1),
        Xd.jM ((i : ℕ) + 1) y = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) x) := Iff.rfl
    rw [key, hT]
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hx
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
      refine Submodule.mem_map.2 ⟨S0.θ i t *ᵥ z, Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
      apply Idx.jM_inj Xd
      have h1 := hθ (lZ0 D A P0 ψ0 Zs i t *ᵥ z)
      erw [hPE] at h1
      refine (hj _).trans ?_
      rw [hxy]
      exact h1.symm
    · intro hy
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
      refine ⟨eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ z), Submodule.mem_map.2 ⟨lZ0 D A P0 ψ0 Zs i t *ᵥ z,
        Submodule.mem_map.2 ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      have h1 := hθ (lZ0 D A P0 ψ0 Zs i t *ᵥ z)
      erw [hPE] at h1
      refine (hj _).trans ?_
      exact h1.symm
  unfold Idx.IjIdx
  rw [hth, hl, SkeletonIndexLemmas.lidx_map _ _ eW.injective]
  rfl

theorem numTie_of_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → NumTie D A3.A (A3.indefDown (s0Of R F)) Y.tup := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd JM hP hH hM hI
  obtain ⟨-, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hZ0 := GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hok := hH.ok.ok2
  have hB : ∀ i t, BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.fam.v0 1 :=
    fun i t => ⟨hok.conj, hok.irr, hok.lifts i t⟩
  have hOP : ∀ i t, Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) :=
    fun i t => BlockDat.lf_l_proj (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (hB i t)
  have hT := fun i t => GlobalTheory.T.lattice_Tj_eq_image_of_coordinate_lattice D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt i t (hOP i t) (Y.formsL i t) (Y.latL i t)
    (hZ0 i t) (fun x => by
      have e : ∀ v, lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ v) = v :=
        fun v => by rw [Matrix.mulVec_mulVec]; erw [(hOP i t).1]; exact Matrix.one_mulVec v
      have h2 := hθ i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x))
      erw [e] at h2
      exact (hθ i t x).trans h2.symm)
  refine ⟨fun i t w => ?_, fun i t w => ?_, fun i w => ?_⟩
  · rw [hI.Ij_def _ _ _ (by omega) (by omega)]
    exact ijIdx_eq D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt (A3.indefDown (s0Of R F)) Xd Z.jW i t (JM.eW i)
      (hOP i t) (hθ i t) (hM.j_eq i) (hM.hlat i).lat (hT i t) w
  · rw [hI.jw_def _ _ _ (by omega) (by omega)]
    refine GlobalTheory.T.lattice_jw_index_eq_concrete_lift_index D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt i t (hOP i t) (Y.formsL i t)
      (BlockDat.lf_lE_form (hB i t)) ?_ (hT i t) w
    classical
    let K := D.what₂.LL
    let B := A3.A.fam.L i t
    let S := B.S
    let ℓ := A3.A.fam.lvlA F.P0 F.ψ0
    let Zl := (A3.fam3.toSub2 (zsOf R F)).Zl i t
    have hGood := (hB i t).ok.good
    change Submodule.span K (↑(B.Tl ℓ Zl) : Set (Fin (B.dZ ℓ Zl) → K)) = ⊤
    apply top_unique
    intro z _
    let x := (B.fE ℓ Zl).mulVec z
    have hdenom (c : S.Cl) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • S.I x c ∈ S.Nab c := by
      obtain ⟨g, hg⟩ := (hGood.nab_lat c).fg
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) g
        (fun y => S.pair y (S.I x c))
      refine ⟨d, nonZeroDivisors.coe_ne_zero d, ?_⟩
      have hdual : (d : 𝓞 K) • S.I x c ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab c) := by
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        refine Submodule.span_induction
          (p := fun y _ => S.pair y ((d : 𝓞 K) • S.I x c) ∈ (1 : Submodule (𝓞 K) K))
          ?_ ?_ ?_ ?_ (hg.symm ▸ hy)
        · intro y hy
          rw [LinearMap.map_smul_of_tower, Submodule.mem_one]
          exact hd y hy
        · simp
        · intro y y' _ _ hy hy'
          rw [map_add, LinearMap.add_apply]
          exact add_mem hy hy'
        · intro a y _ hy
          obtain ⟨a', ha'⟩ := Formalism.DivisionValues.exponent_index_lattice.hstar (K := K) a
          rw [← algebraMap_smul K a y, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
          change star (algebraMap (𝓞 K) K a) • _ ∈ (1 : Submodule (𝓞 K) K)
          rw [← ha', algebraMap_smul]
          exact Submodule.smul_mem _ _ hy
      exact hGood.del_le c (by simpa using hGood.dual_le c _ hdual)
    choose d hd0 hd using hdenom
    let a := ∏ c, d c
    have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd0 c
    have hax : a • x ∈ S.nabLat := by
      apply (Formalism.DivisionValues.ValuationLatticeField.mem_valLatF S.I S.Nab _).2
      intro c
      rw [LinearMap.map_smul_of_tower, Pi.smul_apply]
      obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ c)
      rw [show a = d c * b from hb, mul_comm, mul_smul]
      exact (S.Nab c).smul_mem b (hd c)
    have haz : a • z ∈ B.Tl ℓ Zl := by
      apply BlockDat.lf_cutZ_le (hB i t)
      change (B.fE ℓ Zl).mulVec (a • z) ∈ S.nabLat
      rwa [Matrix.mulVec_smul]
    have haK : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
    have hmem : (a : K) • z ∈ Submodule.span K (↑(B.Tl ℓ Zl) : Set _) := by
      rw [algebraMap_smul K a z]
      exact Submodule.subset_span haz
    exact inv_smul_smul₀ haK z ▸ (Submodule.span K _).smul_mem (a : K)⁻¹ hmem
  · rw [Z.etaJ]
    by_cases h : D.plEq w ∈ R.twPl
    · rw [if_pos h, if_pos (show D.plEq w ∈ (A3.indefDown (s0Of R F)).Tw from h)]; rfl
    · rw [if_neg h, if_neg (show D.plEq w ∉ (A3.indefDown (s0Of R F)).Tw from h)]

end GlobalTheory.Mem.ReadIndexNumerics

end
end
