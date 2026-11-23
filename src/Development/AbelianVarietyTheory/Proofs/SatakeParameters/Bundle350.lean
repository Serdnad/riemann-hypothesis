module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle216
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle338
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle294
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle327
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle307
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle309
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IteratedFDerivConstSmulOfNe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle186
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiExThetaGeneral
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Outright
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.MatFrames



theorem frames_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j < D.R.m), j ≤ t.m2 → ∀ (β : (St j hj.le).Ch) (x x₁ : UA D j hj.le) (κ : ((St j hj.le).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj.le β x p → IsPtAd A a j hj.le β x₁ p₁ →
    ∃ (k : GLQ t.X.E (D.R.N j) (SB t μ)) (c : SB t μ → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * ((k P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (k P) (c P)) ∧
      ((((St j hj.le).K β).lev.chi κ : ℂˣ) : ℂ) = t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) ∧
      ∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE ((LinearEquiv.det ((k P)⁻¹).1 : t.X.Eˣ) : t.X.E)) - 1))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie j hj hjm β x x₁ κ hx p p₁ hp hp₁
  classical
  have hok := t.idx_ok μ
  obtain ⟨hLe, -, hChi⟩ := hTie.levMid j hj hjm β
  have hLoc : ∀ P : SB t μ, ∃ g z, A.midRel j hj β P g z ∧ InFrame t.seam (A.fb j hj.le β) (t.cst μ).D P κ.1 g := by
    intro P
    have hv : IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    have hU := (((St j hj.le).K β).lev.U_eq κ.1).1 κ.2
    exact hLe P _ hv κ.1 hU.1 (hU.2 _)
  choose g z hgz using hLoc
  have hpr : ∀ P, g P ∈ prCat (Pr := t.Pr) (t.cst μ).sharp j P.1 ((t.idx μ).h j (A.ib j hj β) P) := fun P =>
    (exists_midLev_iff t.Ch t.sel (t.tup μ) (t.cst μ) j P _ (g P)).1 ⟨z P, (hgz P).1⟩
  let gg : ∀ P : SB t μ, GLint t.X.E (D.R.N j) P.1 := fun P => ⟨g P, hok.int j _ P (hpr P)⟩
  have hB := fun P => GlobalTheory.T.frames_of_right_translate_point_principal_congruence A a j hj.le β x x₁ κ.1 hx p p₁ hp hp₁ P (gg P) (hgz P).2
  choose C hCp hCc hCf using hB
  have hD : ∀ P : SB t μ, 1 ≤ (t.cst μ).D P := fun P => hok.cst_ok.D_pos P
  have hc : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P
      (gg P * C P)⁻¹ c ∧ (c : t.X.K) = (z P)⁻¹ := by
    intro P
    obtain ⟨r, hr, hrx, hz⟩ := (hgz P).1
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hH : redGL _ P.1 (gg P) ∈ ((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).H :=
        (hok.grpG j _ ⟨P.1, hP⟩ _).2 ⟨g P, hpr P, fun y hy => redV_redGL (gg P) hy⟩
      have hlam := hok.chrG j _ ⟨P.1, hP⟩ ⟨_, hH⟩ (g P) r hr hrx (fun y hy => redV_redGL (gg P) hy)
      have hred : redGL _ P.1 (gg P * C P)⁻¹ = (redGL _ P.1 (gg P))⁻¹ := by
        rw [map_inv, map_mul, GlobalTheory.TopStep.redGL_of_prinCong (hD P) (hCp P), mul_one]
      refine ⟨(((t.idx μ).levG j (A.ib j hj β) ⟨P.1, hP⟩).lam ⟨_, hH⟩)⁻¹, ⟨fun hP' => ⟨hred ▸ inv_mem hH, ?_⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
      · rw [← map_inv]
        congr 1
        exact Subtype.ext hred.symm
      · rw [Units.val_inv_eq_inv_val, hlam, hz]
    · have hQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.mp P.2).resolve_left hP
      obtain ⟨r', hr', hr'x, hr'1⟩ := GlobalTheory.T.principal_congruence_subgroup_mem_level_twist_prime hPin.fields.ok t.pr_ok hok (j := j) hjm (A.ib j hj β) P hP (C P) (hCp P)
      have hgH : gg P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 (hpr P)
      have hCH : C P ∈ ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H := by
        rw [hok.grpQ]
        exact Subgroup.mem_subgroupOf.2 ⟨r', hr', hr'x⟩
      have hlg := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨gg P, hgH⟩ r hr hrx
      have hlC := hok.chrQ j _ ⟨P.1, hQ⟩ ⟨C P, hCH⟩ r' hr' hr'x
      have hC1 : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨C P, hCH⟩ = 1 := Units.ext (hlC.trans hr'1)
      refine ⟨(((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).lam ⟨gg P, hgH⟩)⁻¹,
        ⟨fun hP' => absurd hP' hP, fun hQ' _ => ⟨inv_mem (mul_mem hgH hCH), ?_⟩⟩, ?_⟩
      · have e : (⟨(gg P * C P)⁻¹, inv_mem (mul_mem hgH hCH)⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) =
            ((⟨gg P, hgH⟩ : ((t.idx μ).levQ j (A.ib j hj β) ⟨P.1, hQ⟩).H) * ⟨C P, hCH⟩)⁻¹ := Subtype.ext (by simp)
        rw [e, map_inv, map_mul, hC1, mul_one]
      · rw [Units.val_inv_eq_inv_val, hlg, hz]
  choose c hcL hcz using hc
  refine ⟨fun P => (gg P * C P)⁻¹, c, fun P => ?_, hcL, ?_, fun P => ?_⟩
  · rw [inv_inv]
    exact hCf P
  · have h1 := hChi κ g z hgz
    have h2 : (((∏ P, c P : t.X.Kˣ)) : t.X.K) = (∏ P, z P)⁻¹ := by
      rw [Units.coe_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun P _ => hcz P
    rw [h2, map_inv₀]
    exact eq_inv_of_mul_eq_one_left h1
  · rw [inv_inv]
    exact GlobalTheory.T.det_inv_mul_frame_reading_congruent_one_mod_norm t.seam (A.fb j hj.le β) (t.cst μ).D P (hD P) κ.1 (g P) (C P).1 (hgz P).2 (hCc P)

end GlobalTheory.MatFrames

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain



theorem GlobalTheory.Svd.Part.kerTie : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → O.ex.tw = w.tw Z ∧ O.ex.errX.piG = w.px.piG ∧ O.ex.errX.piT = w.px.piT ∧ TC.QpIs w.I O.X.Qp ∧ ∃ t : KerEntTied O.ex, TC.StdKer w.I w.l Z t ∧ t.Adapted ∧ t.TopPinned := by
  intro B f T w Z O P
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨pin, col, hErr, tp, hxi, qp, ker0, ker_eq, kt⟩ := P
  dsimp only [ofObj, extraObj] at hErr ker_eq qp kt
  cases ker_eq
  subst hErr
  have hpi := GlobalTheory.T.errorData_generators_eq_columnPreDatum B f T w Z col
  refine ⟨rfl, hpi.1, hpi.2, qp, ?_⟩
  refine Exists.imp (by intro t h; exact ⟨(StdModel.stdKer_iff w.I w.l Z t).2 h.1, h.2.2.2.1, h.2.2.2.2⟩)
    (GlobalTheory.Mem.Col2.TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z _ _ _ _ _ _ _ _ kt.O kt.E qp kt.std kt.unf kt.ok (by exact kt.served))
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem kernelSite_seriesData_below_lastStep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hP hPos hSc
  refine ⟨?_, ?_, ?_, hSc, J.rho std, ?_, ?_, ?_⟩
  · intro j hj L0 hL0 La' hLa'
    exact (hP j hj L0 La' (repOf_lat _ _ j L0 hL0) hLa').1
  · obtain ⟨hpos, hS⟩ := GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors t std J
    exact ⟨hpos, fun hd => GlobalTheory.T.site_residue_char_not_mem_bad_primes t std J (hS _ Fact.out hd)⟩
  · exact ⟨(t.O u μ).S, GlobalTheory.T.site_residue_char_not_mem_bad_primes t std J, fun j _ L0 _ La' _ y => GlobalTheory.T.intOff_xi0_of_joint t std J S j L0 La' y⟩
  · exact GlobalTheory.TwU.lamPosG_of_lamPos _ S.E D _ _ _ hPos
  · exact fun j La v => GlobalTheory.isUnit_det_frameMatrix_ofCharts _ _ _ j La v
  · refine GlobalTheory.T.orthonormal_local_bases_carry_witt_lattices _ S.hfin D (J.fd std) (J.rho std) (halfDiffInv_integral_at_split D _ _ hg) ?_
    intro j hj La La' h1 h2
    have q := hP j hj La La' h1 h2
    exact ⟨q.1, fun v => ⟨(q.2.2.2.2.2.2.2 v).2.2.1, (q.2.2.2.2.2.2.2 v).2.2.2⟩⟩

end GlobalTheory.TwV

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.TwU

theorem xiM_datLoc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hjm La La' hLa hLa'
  have hm : (sysS H X std).mm = D.R.m := by
    first | rfl | exact X.fl_m
  have hj : j + 1 ≤ D.R.m := by omega
  obtain ⟨⟨h1, -⟩, -, hK1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨⟨h2, -⟩, -, hK2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun z =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
    funext z
    exact GlobalTheory.T.moved_pair_datum_eq_adelic_datum t std J S.Xi j hj h1 h2 La La' z
  rw [hx]
  exact datLoc_homRe D t.cc (ssRec t u μ) (t.rd u μ).lev h1 h2 _ _ _ _ _ hK1 hK2
    (S.law.loc j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
      (J.pt std (j + 1) hj La'))

end GlobalTheory.TwU
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.latticeTuplePairScalar_mem_algebraicClosure_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' ∈ TaylorLogMetric.Qbar := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hj La La' hLa hLa'
  have hjm : j < D.R.m := lt_of_lt_of_eq hj X.fl_m
  have hj' : j + 1 ≤ D.R.m := hjm
  have hχ := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).1
  have h1 : S.muT (j + 1) ((J.fd std).dt j La) ∈ TaylorLogMetric.Qbar := by
    rw [(hD j hjm.le La hLa).2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D j hjm.le _)
  have h2 : S.muT (j + 1) ((J.fd std).dt (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    rw [(hD (j + 1) hj' La' hLa').2.2.2]
    exact S.law.mu_alg j hjm _ (det_unitary_adelic_point_gram_step_norm_one D (j + 1) hj' _)
  have k1 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD j hjm.le La hLa
  have k2 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD (j + 1) hj' La' hLa'
  exact mul_mem (mul_mem (mul_mem h2 (inv_mem h1)) (zpow_mem (hχ _ _ k1.1 k1.2) _)) (zpow_mem (hχ _ _ k2.1 k2.2) _)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem site_law_xiIn : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pair → S.Pos → S.Move → S.Away → S.Law ∧
    Lt.LawInLt (sysS H X std) S.hfin S.E S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev
      (J.xi0 std S.Xi) S.muT ∧
    AdmLoc.XiIn (sysS H X std) S.E S.hfin S.hst S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev
      (J.xi0 std S.Xi) S.muT) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPair hPos hMove hAway
  obtain ⟨hδ, hLat, hVec, hEq⟩ := GlobalTheory.TieBase.base_data t
  obtain ⟨hcl, hSS⟩ := GlobalTheory.BadPrimes.lev_pos_and_noConj J.A J.dtU J.a J.pins J.tie
  have hmm : (sysS H X std).mm = D.R.m := (DelB.sysS_ranks S).1
  have hLaw : S.Law :=
    GlobalTheory.TwU.LawAll.kapLawLt_frecG D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev hcl hSS
      (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam (J.xi0 std S.Xi) S.muT (J.rho std)
      (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT) hPair hPos hMove
  refine ⟨hLaw, ?_, ?_⟩
  · intro j hj c L0 La' ε hrep hL' hε
    letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
    letI := algKfC S.E.toCEmb
    exact GlobalTheory.TwU.KapLawLt.stab (h := hLaw) (hj := hj) c L0 La' ε (repOf_lat _ S.hfin j (c, L0) hrep) hL' hε
  · intro v j hj
    have hRB := GlobalTheory.TwU.pendT_ThF_lt_of_kapLawLt (D.what₂.places.resChar w) (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau
      (hT.gat_pos u w hg)
      (Formalism.L2.PairingIndexBounds.F.FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
        (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT)) hLaw
    exact hRB.2 v j hj
      (GlobalTheory.XiGen.xiEx_theta_general D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq
        (Formalism.L2.PairingIndexBounds.Rec.model_at_split_places_holds D) (Formalism.L2.PairingIndexBounds.Rec.split_place_moves_compose D) (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev hcl hSS
        (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam (J.xi0 std S.Xi) S.muT (J.rho std)
        (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT) hPair v j hj (hAway v j (hmm ▸ hj)))

end GlobalTheory.TwV
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), ∃ κ : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.U, (J.pt std 0 (Nat.zero_le _) La).1 = ratA D.host.F γ * ((J.St 0 (Nat.zero_le _)).y (clsAt X H 0 La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La hLa
  obtain ⟨-, hA⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La
  have hb := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa
  obtain ⟨hγ, κ, hκ⟩ := pt00 J.one La.1 La.2 _ hb _ hA
  have hc : clsAt X H 0 La.1 La.2 = J.e0 (levelZeroClass J.one La.1 La.2) := J.cls0 La.1 La.2 hLa

  obtain ⟨κ', hκ'⟩ := (J.y0 (levelZeroClass J.one La.1 La.2)).imp fun _ h => h.1
  have hU := (J.lev0 (J.chart std 0 (Nat.zero_le _) La)).2.2.1
  have hm : κ'.1⁻¹ * κ.1 ∈ (J.Gd.forms u).cls0.lev.U := Subgroup.mul_mem _ (Subgroup.inv_mem _ κ'.2) κ.2
  refine ⟨rationalElementZero J.one La.1 La.2, hγ, ⟨κ'.1⁻¹ * κ.1, by rw [hU]; exact hm⟩, ?_⟩
  rw [hc, hκ', hκ]
  show _ = _ * _ * (κ'.1⁻¹ * κ.1)
  simp only [mul_assoc, mul_inv_cancel_left]
  rfl
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.Joint.pt_succ_coset : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj), ∃ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  have hb := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J (j + 1) La hLa
  obtain ⟨-, -, hU, -, hy⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).2
  obtain ⟨hc, κ, hγ, e⟩ := kaAt_pt H j hj ((I.at' j hj).st.eC.symm La.1).1 ((I.at' j hj).st.eC.symm La.1).2 La.2 _
    (fun v => hb v) (J.pt std (j + 1) hj La) hp
  have ea : (I.at' j hj).st.eC ⟨((I.at' j hj).st.eC.symm La.1).1, ((I.at' j hj).st.eC.symm La.1).2⟩ = La.1 :=
    Equiv.apply_symm_apply _ _
  have hc' : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1 := by
    rw [ea] at hc; exact hc
  refine ⟨_, hγ, ⟨κ.1, (SetLike.ext_iff.1 hU κ.1).2 κ.2⟩, ?_⟩
  rw [hy hc']
  have e2 : ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ =
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc'⟩ :=
    congrArg _ (Subtype.ext (congrArg (fun a => clsOf (S := (I.at' j hj).st) (H.core j hj) a La.2) ea))
  rw [← e2]
  exact e
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTupleSuccLevel_point_isComponentPointInChart : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v), (∀ v, La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g v).1) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g (J.pt std (j + 1) hj La).1) := by
  first | exact @GlobalTheory.TwV.DelA.ptS_isPt | exact GlobalTheory.TwV.DelA.ptS_isPt | (intros; apply GlobalTheory.TwV.DelA.ptS_isPt <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepTwist_at_classRep_eq_charPow_det : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (c : {c // (I.at' j hj).st.chOf c = β}), ((I.at' j hj).st.tw β).ch (((I.at' j hj).st.K β).y c) = D.chiD ((t.O u μ).dt (j + 1) (castCls (X.onCh j hj) (j + 1) c.1)) ^ cTw D (j + 1)) := by
  first | exact @GlobalTheory.TwV.tw_at_rep | exact GlobalTheory.TwV.tw_at_rep | (intros; apply GlobalTheory.TwV.tw_at_rep <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_prod_cmType_embeddings_norm_one_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖ι (∏ τ, TaylorLogMetric.embT D τ z)‖ = 1) := by
  first | exact @GlobalTheory.TwV.prod_embT_norm_one | exact GlobalTheory.TwV.prod_embT_norm_one | (intros; apply GlobalTheory.TwV.prod_embT_norm_one <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_site_coordinate_scale_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ‖ltC S.g S.hLT‖ = 1) := by
  first | exact @GlobalTheory.TwU.ScaleUnit.norm_ltC_eq_one | exact GlobalTheory.TwU.ScaleUnit.norm_ltC_eq_one | (intros; apply GlobalTheory.TwU.ScaleUnit.norm_ltC_eq_one <;> assumption)
end
