module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle186
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.K2Hermitian
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle002
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.Bundle001
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.CompInjLocJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle336
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle074

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.DelB

theorem delPolAt_of_frames_scal : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (c : ℂ_[p]) (F g₀ : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; FrInv fd → KapLawLt X ℂ_[p] (thFOf X pos F) → let Y := pendT X E hfin hst hLT pos F; ∀ (σ : D.what₂.LL →+* X.G.Kf) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc) (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Y.Kc →ₗ[Y.Kc] XspC (X.Pj (j + 1)) Y.Kc) (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc) (sO : ∀ j, X.Lt j → Y.Kc) (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) (j : ℕ) (_ : j < X.mm) (cK : Y.Kc) (hN : RankTie X D j), (∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → F j La La' = linSub (fun x y => c * subBG E.toCEmb pos fd j La La' x y) (g₀ j La La')) → MoveH Y u μ cmp (fun j La => glInv X j (BOf fd j La)) Gm j → TieOpS (Y := Y) t u μ cls Gm sO j (eIdx X D pos j hN) (Φ₀ j) → KernelEntryDegreeCondition (Y := Y) t u μ cls j (eIdx X D pos j hN) → TieSerH Y t u μ cls κ ι (fun j La La' => resV (kapOf X pos j) (g₀ j La La')) sH j (eIdx X D pos j hN) → TieChiH Y t u μ cls κ ι sc sH (fun j La => Formalism.L2.G.Pend.cA X Y.Kc j (BOf fd j La) * sO j La) j cK → DelYEqH Y (fun j La' => VOf Y.Kc fd c j La') τ j → DelPolAt (Y := Y) t u μ cls cmp κ (phiH D Φ₀ τ sc) (srOf Y) j cK := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ p _ X _ E hfin hst g hLT pos fd c F g₀
  intro hFr hK Y σ cls cmp κ ι Φ₀ τ sc sH sO Gm j hj cK hN hF hMv hOp hDeg hSer hChi hYEq
  intro La hLa x Q hQ c' L' hL'
  letI := Formalism.L2.G.Pend.wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  have hTh : Y.ThF j La (c', L') = Formalism.L2.G.Pend.thFOf X pos F j La (c', L') :=
    (GlobalTheory.TwU.pendT_ThF_lt_of_kapLawLt p X E hfin hst g hLT D.what₂.Tau pos F hK).1 j ‹_› La (c', L') (Y.Rep_lat j La hLa) hL'
  have hsr : srOf Y j La (c', L') = (Y.eS j La * (Y.eT j (c', L'))⁻¹ : X.G.Kf) •
      linSub (fun z y => ∑ w, VOf Y.Kc fd c j (c', L') z w * Formalism.L2.G.Pend.LkB X Y.Kc j (BOf fd j La) w y)
        (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L'))) := by
    unfold srOf
    rw [hTh]
    congr 1
    show resV (Formalism.L2.G.Pend.kapOf X pos j) (F j La (c', L')) = _
    rw [hF La (c', L') (Y.Rep_lat j La hLa) hL']
    rw [rename_linear _ _ _ _ (kapOf_bij X pos j)]
    congr 1
    funext z y
    exact substitution_split p X D E.toCEmb pos fd _ hFr j La (c', L') z y
  obtain ⟨hMe, hG, hO⟩ := hMv La hLa x
  beta_reduce at hMe
  have hc := chain_core X Y.Kc j (VOf Y.Kc fd c j (c', L'))
    (blockDiag_VOf X Y.Kc j fd _ (c', L')) (glInv X j (BOf fd j La)) (Gm j La x) hG hO (τ j c' L')
    (hYEq c' L' hL' (Gm j La x) hG hO) (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L')))
  rw [glAt_glInv] at hc
  have hPD := pairing_dictionary p X Y.Kc j D (D.R.N j) (D.R.N (j + 1)) ι (eIdx X D pos j hN) (eIdx_injective X D pos j hN) (Φ₀ j)
    (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))
    ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L'))
    (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L'))) (sH j La (c', L'))
    (hDeg La hLa x Q hQ) (fun α hα => hSer La hLa c' L' hL' α (hDeg La hLa x Q hQ α hα))
  have hOS := pairD_lin X Y.Kc j (sO j La • LinearMap.id)
    (trDY X Y.Kc j D (eIdx X D pos j hN) (Φ₀ j) (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1))))
    (Formalism.L2.G.Pend.polDel X Y.Kc j (Gm j La x)) (fun n => hOp La hLa x Q hQ n)
    (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L')))
  show sc j c' L' • τ j c' L' (Φ₀ j (_ • pairR D (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))
      ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L')))) =
    cK • Formalism.L2.G.Pend.pairD X Y.Kc j (Formalism.L2.G.Pend.polDel X Y.Kc j (cmp j x La.1 La.2)) (srOf Y j La (c', L'))
  rw [hsr, Formalism.L2.G.Pend.pairD_smul_right, ← hMe, hc, hOS, hPD, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.map_smulₛₗ, map_smul, map_smul, map_smul,
    ← algebraMap_smul Y.Kc (Y.eS j La * (Y.eT j (c', L'))⁻¹), smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [← hChi La hLa c' L' hL']
  ring

end GlobalTheory.TwV.DelB
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem wG_succ_eq_shift (R : Ranks) (z : ℤ) (j : ℕ) :
    Formalism.BasicNotions.wG R (z : ℚ) (j + 1) = ((z - ((j * (R.t + 1) / 2 : ℕ) : ℤ) - ((R.N (j + 1) / 2 : ℕ) : ℤ) : ℤ) : ℚ) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  have h1 : j * (R.t + 1) / 2 = j * (b + 1) := by
    rw [hb, show j * (2 * b + 1 + 1) = 2 * (j * (b + 1)) by ring]; omega
  have h2 : R.N (j + 1) / 2 = a + (j + 1) * (b + 1) := by
    show (R.k + (j + 1) * (R.t + 1)) / 2 = _
    rw [hb, ha, show a + a + (j + 1) * (2 * b + 1 + 1) = 2 * (a + (j + 1) * (b + 1)) by ring]; omega
  rw [h1, h2]
  unfold Formalism.BasicNotions.wG
  rw [ha, hb]
  push_cast
  ring



theorem fillAt_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ j (hj : j < D.R.m), (sysS H X std).Lv.comp (j + 1) → FillAt (hT := hT) (H := H) (X := X) std j hj) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c
  have hj' : j + 1 ≤ D.R.m := hj
  have c' : Lv.comp (j + 1) := c
  have hW := (H.core j hj' ((I.at' j hj').st.eC.symm c').1).wt
  rw [J.pos j hj'] at hW
  have ht : (Gl.Fl u w hg).t = D.R.t := X.fl_t
  have hk := hT.gat_k u w hg
  have rk := rk_of hT w hg (Gl.Fl u w hg) ht j
  intro e he v s
  show (Gl.Fl u w hg).w v (j + 1) s = e (hT.gat_pos u w hg ⟨v, s⟩) - ((j * ((Gl.Fl u w hg).t + 1) / 2 : ℕ) : ℤ) -
      (((((Gl.Fl u w hg).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)
  have hlt : (D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) < ((Gl.Fl u w hg).Pj (j + 1)).m + 1 := by
    show _ < (D.gat u w hg).P.m + (j + 1) * ((Gl.Fl u w hg).t + 1) + 1
    nlinarith
  have h := hW v s ⟨_, hlt⟩
  have h0 := (congrArg (fun z : ℤ => (z : ℚ)) h).trans (((I.at' j hj').M).lam_eq (j + 1) hj' (hT.gat_pos u w hg ⟨v, s⟩) _)
  have hi : ¬ (D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) < D.R.k := by omega
  have hq : ((D.gat u w hg).P.m + 1 + j * ((Gl.Fl u w hg).t + 1) - D.R.k) / (D.R.t + 1) = j := by
    rw [← hk, ← ht, Nat.add_sub_cancel_left]; exact Nat.mul_div_cancel _ (Nat.succ_pos _)
  simp only [finCongr_apply, Fin.coe_cast] at h0
  rw [dite_eq_right hi] at h0
  simp only [hq] at h0
  have hL : ((Gl.Fl u w hg).Pj (j + 1)).lam0 v s ⟨_, hlt⟩ = -((Gl.Fl u w hg).w v (j + 1) s) := by
    show liftWt (Gl.Fl u w hg).t (D.gat u w hg).P.m ((D.gat u w hg).P.lam0 v s) (fun a => (Gl.Fl u w hg).w v a s) (j + 1) ⟨_, hlt⟩ = _
    unfold liftWt
    rw [dite_eq_right (Nat.not_lt.mpr (Nat.le_add_right _ _))]
    congr 2
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.mul_div_cancel _ (Nat.succ_pos _)]
  rw [hL, Int.cast_neg, neg_inj, D.hcW_e, ← he] at h0
  rw [rk, ht]
  apply Int.cast_injective (α := ℚ)
  rw [h0]
  exact wG_succ_eq_shift D.R _ j

end GlobalTheory.TwV.Xc

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc



theorem frM_fd_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), (J.fd std).frM j (c, La) = (J.fd std).frM j (c, Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j c La Lb
  funext v
  cases j with
  | zero =>
    simp only [Joint.fd, fdAtL, fdAt, fdOfCharts, cpAt, chAt]
    rfl
  | succ i => exact Formalism.MainNotions.G.KAat.frM_comp i c La Lb v

end GlobalTheory.TwV.Xc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Port



theorem site_labels_with_stepZero_classMap : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), Fl.mm = D.R.m → SiteGood Z → (∀ j, j < D.R.m → (Tw.fm u μ).KRat j) → (D.chTw u μ).DGam ∣ (D.mem u).C.DGam → ∀ (one : OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y) (e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0), ∃ X : LabIn (Z.inTw Fl ht Gt), ∀ a (La : (D.gat u w hg).P.Tup), X.c0.cls a La = e0 (levelZeroClass one a La) := by
  intro D Gt c g u w hg Tw μ Z Fl ht hm G rat dgam one e0
  refine ⟨labOf ⟨fun _ _ => rfl, fun j hj => chX_stepInOf hj (Z.Fo j hj) (Z.loc Fl ht j hj) (Gt.gat_pos u w hg) (Z.sameU Fl ht j hj)
    (Z.frRat Fl ht j hj) (hypTJC_site Z Fl ht G.siteGood_prime_torsion j hj), fillOK_of_empty (Z.lv_empty Fl ht)⟩ ht hm
    (clsAt0Of one e0 (fun c => Formalism.L2.G.Triv.card_stab (g.herm.lev0 u) D.host.g_prime D.host.g_ne c) _) rat dgam, fun a La => rfl⟩

end GlobalTheory.Port
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.siteAdmissible_indep_divisionLattices : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.SiteAdm D u w hg Fl Lv Ch → GlobalTheory.TwU.SiteAdm (setDiv D N h) u w hg Fl Lv Ch := by
  first | exact @GlobalTheory.TwU.siteAdm_setDiv | exact GlobalTheory.TwU.siteAdm_setDiv | (intros; apply GlobalTheory.TwU.siteAdm_setDiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.latticeChainComparison_indep_divisionLattices : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.CmpLite D c Tw u μ w hg Ch → GlobalTheory.TwU.CmpLite (setDiv D N h) (cmpTr N h c) (twTr N h Tw) u μ w hg Ch := by
  first | exact @GlobalTheory.Svd.cmpLite_setDiv | exact GlobalTheory.Svd.cmpLite_setDiv | (intros; apply GlobalTheory.Svd.cmpLite_setDiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.fontaineParameter_twist_potentiallySemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw c → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) → GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) = (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpChar (GlobalTheory.Pst.wdAt P ι Bw h hj c) := by
  first | exact @GlobalTheory.TwistParamAbove.wdAt_twist | exact GlobalTheory.TwistParamAbove.wdAt_twist | (intros; apply GlobalTheory.TwistParamAbove.wdAt_twist <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace GlobalTheory.DrinLev.HT.HeckePt

section Pull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem ext_of_left {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {b : B'.left ⟶ B.left}
    (hb : IsGrpPullback B' B f b) {T : Over S'} {u v : T ⟶ B'} (h : u.left ≫ b = v.left ≫ b) : u = v := Over.OverMorphism.ext (hb.1.hom_ext h (by rw [Over.w u, Over.w v]))

variable {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}

def pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) : A' ⟶ B' :=
  Over.homMk (hb.1.lift (a ≫ ψ.left) A'.hom (by rw [Category.assoc, Over.w ψ, ha.1.w])) (hb.1.lift_snd _ _ _)

theorem pullMor_left (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) :
    (pullMor ha hb ψ).left ≫ b = a ≫ ψ.left := by
  simp only [pullMor, Over.homMk_left]
  exact hb.1.lift_fst _ _ _

private theorem pushHom_left_satake_parameters {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') : (pushHom h T x).left = x.left ≫ φ := by
  rfl

theorem push_pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) (T : Over S')
    (x : T ⟶ A') : pushHom hb T (x ≫ pullMor ha hb ψ) = pushHom ha T x ≫ ψ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, pushHom_left_satake_parameters, Category.assoc, pullMor_left]

private theorem isMonHom_of_comp_mul {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C} [GrpObj G] [GrpObj H]
    (g : G ⟶ H) (hg : ∀ (T : C) (x y : T ⟶ G), (x * y) ≫ g = x ≫ g * y ≫ g) : IsMonHom g := by
  constructor
  · have h1 := hg (𝟙_ C) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ C ⟶ G) ≫ g = 1 := mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)
    simpa [Hom.one_def, toUnit_unit] using h2
  · have h := hg _ (fst G G) (snd G G)
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1
    ext <;> simp

theorem isMonHom_pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) [IsMonHom ψ] :
    IsMonHom (pullMor ha hb ψ) := by
  refine isMonHom_of_comp_mul _ fun T x y => ext_of_left hb ?_
  rw [← pushHom_left_satake_parameters hb, ← pushHom_left_satake_parameters hb, push_pullMor, map_mul, map_mul, push_pullMor, push_pullMor,
    MonObj.mul_comp]

theorem pow_id_left (ha : IsGrpPullback A' A f a) (n : ℕ) : ((𝟙 A') ^ n).left ≫ a = a ≫ ((𝟙 A) ^ n).left := by
  have h1 := pushHom_left_satake_parameters ha A' ((𝟙 A') ^ n)
  rw [map_pow] at h1
  rw [← h1]
  have h2 : pushHom ha A' (𝟙 A') ^ n = pushHom ha A' (𝟙 A') ≫ (𝟙 A) ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [h2]
  simp only [Over.comp_left, pushHom_left_satake_parameters, Over.id_left, Category.id_comp]

theorem pullMor_comp_eq_pow (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) (ψ' : B ⟶ A)
    (n : ℕ) (h : ψ ≫ ψ' = (𝟙 A) ^ n) : pullMor ha hb ψ ≫ pullMor hb ha ψ' = (𝟙 A') ^ n := by
  apply ext_of_left ha
  rw [Over.comp_left, Category.assoc, pullMor_left hb ha ψ', ← Category.assoc, pullMor_left ha hb ψ, Category.assoc,
    ← Over.comp_left, h, pow_id_left ha n]

end Pull

end GlobalTheory.DrinLev.HT.HeckePt
end
end
