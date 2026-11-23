module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle213
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle346
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.Joint.locSp_kerN_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa v
  obtain ⟨-, -, hker, -⟩ := hD (j + 1) hj La hLa
  obtain ⟨hTT, hLb, -⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  obtain ⟨-, hpt⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La
  have hbas := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J (j + 1) La hLa v
  rw [hLb] at hker
  have hcop : Nat.Coprime (I.at' j hj).st.T (D.what₂.places.resChar w) := by
    rw [hTT]
    exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  have hT0 : 0 < (I.at' j hj).st.T := by
    rcases Nat.eq_zero_or_pos (I.at' j hj).st.T with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop
      exact absurd hcop hp.one_lt.ne'
    · exact h0
  have hun := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have horth : ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (j + 1) hj) co :=
    ⟨_, GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ _ (J.pins.crd_orth (j + 1) hj)⟩
  have hK := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1) J.a horth (J.alg j hj _) (H.core j hj _).int (J.lbB j hj _) hT0
    _ _ (J.pt std (j + 1) hj La) hpt v hun
  have hR := @GlobalTheory.TwV.locSp_reindex _ _ _ (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (_) (_) (_) _ _ _
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk _ _ _ _ _ hker hK
  have hch := (dif_pos hj : chAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om I
    (lev0At J.Gd u w hg).A (lev0At J.Gd u w hg).J (lev0At J.Gd u w hg).Lb (lev0At J.Gd u w hg).Uloc (j + 1) La = _)
  have hJ := congrArg PtCh.J hch
  have hB := congrArg PtCh.B hch
  have hi := congrArg (fun c => PtCh.iw c v) hch
  have hfr : (J.fd std).frM (j + 1) La v = _ :=
    congrArg (fun M => Matrix.submatrix M (finCongr rfl) (finCongr rfl))
      (congr (congrArg Matrix.map (congr (congrArg HMul.hMul (congrArg (fun Q => LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) Q).toLinearMap) hJ))
        (congrArg Units.val hB))) (congrArg DFunLike.coe hi))
  rw [hfr, hbas]
  have hiw : J.rho std v = ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).iw v := (J.iw j hj _ v).symm
  rw [hiw]
  exact hR
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV



theorem Joint.locSp_kerN_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD La hLa v
  obtain ⟨-, -, hK, -⟩ := hD 0 (Nat.zero_le _) La hLa
  rw [(J.lev0 _).1] at hK
  have hcop : Nat.Coprime (D.mem u).A.T (D.what₂.places.resChar w) := (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hT0 : 0 < (D.mem u).A.T := by
    rcases Nat.eq_zero_or_pos (D.mem u).A.T with h | h
    · rw [h, Nat.coprime_zero_left] at hcop
      exact absurd hcop (Fact.out : (D.what₂.places.resChar w).Prime).one_lt.ne'
    · exact h
  have hU := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have ho := GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (J.pins.crd_orth 0 (Nat.zero_le _))
  have hs := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint (J.Gd.forms u).cls0.lev (lev0At J.Gd u w hg).A J.a ⟨_, ho⟩ J.alg0 J.one.int J.lb0 hT0 La.1 _
    (J.pt std 0 (Nat.zero_le _) La) (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).2 v hU
  rw [GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa v]
  exact locSp_reindex (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ _ (lev0At J.Gd u w hg).A.rk _ _ _ _ _ hK hs

end GlobalTheory.TwV
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.TwV.KerSucc

theorem latK_of_renamed {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N n : ℕ} (h : N = n) (hr : n = N) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb Lb₁ : Submodule (𝓞 E) (Fin N → E))
    (J' : Matrix (Fin n) (Fin n) E) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb' : Submodule (𝓞 E) (Fin n → E))
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (hy : x = Formalism.L2.PairingIndexBounds.F.reGL (finCongr hr) y)
    (hLb : Lb' = Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E))) (h₁ : Lb₁ = Lb) :
    HEq ((latK sp J' a y Lb').map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a x Lb₁) := by
  have h1 := (GlobalTheory.reindex_rename_point_det_latK sp hr J' a y Lb').1
  have h3 := (GlobalTheory.reindex_rename_point_det_latK sp h J a x Lb).2.2
  have hy' : y = Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) x := by rw [hy]; exact h1.symm
  rw [hJ, hLb, h₁, hy']
  exact h3

section Unfold

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem gram_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).J (i + 1) La =
      (Formalism.L2.Forms.gramN D (i + 1) hi).reindex (finCongr hr) (finCongr hr) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).J = _
  rw [chAt, dite_eq_left hi]

theorem base_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).Lb (i + 1) La =
      ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb.map
        ((reE (E := D.host.E) hr).toLinearMap.restrictScalars (𝓞 D.host.E)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).Lb = _
  rw [chAt, dite_eq_left hi]

end Unfold

end GlobalTheory.TwV.KerSucc

theorem GlobalTheory.TwV.Joint.kerN_succ_heq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → HEq ((J.fd std).kerN (j + 1) La) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La).1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  obtain ⟨hr, hx⟩ := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).1
  have hLb := (GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa).2.1
  have hJ : (J.cp std).J (j + 1) La = (gramN D (j + 1) hj).reindex (finCongr hr.symm) (finCongr hr.symm) :=
    GlobalTheory.TwV.KerSucc.gram_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  have hL : (J.cp std).Lb (j + 1) La = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb.map
      ((reE (E := D.host.E) hr.symm).toLinearMap.restrictScalars (𝓞 D.host.E)) :=
    GlobalTheory.TwV.KerSucc.base_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  exact GlobalTheory.TwV.KerSucc.latK_of_renamed D.sp hr.symm hr _ J.a _ _ _ _ _ _ hJ hx hL hLb
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.kerN_zero_eq_latK_pt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), HEq ((J.fd std).kerN 0 La) (latK D.sp (gramN D 0 (Nat.zero_le _)) J.a (J.pt std 0 (Nat.zero_le _) La).1 ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La
  obtain ⟨⟨hr, hx⟩, -⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La
  have hre := GlobalTheory.reindex_rename_point_det_latK D.sp (lev0At J.Gd u w hg).A.rk.symm (gramN D 0 (Nat.zero_le _)) J.a
    (Classical.epsilon fun x => (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (lev0At J.Gd u w hg).Lb
  have hpt : (J.pt std 0 (Nat.zero_le _) La).1 = (Classical.epsilon fun x => (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [hx]
    exact hre.1
  have hLb : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb = (lev0At J.Gd u w hg).Lb := (J.lev0 _).1
  rw [hpt, hLb]
  exact hre.2.2
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.det_orthonormalCoords_mul_basis_localUnit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v)) → ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v ((J.A.crd j hj).1.det * B.1.det) = algebraMap _ _ (y : (sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.LatDet.crd_mul_det_unit | exact GlobalTheory.TwV.LatDet.crd_mul_det_unit | (intros; apply GlobalTheory.TwV.LatDet.crd_mul_det_unit <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_derivation_generators_eq_one_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ τ, ‖ι ((t.O u μ).dgen τ)‖ = 1) := by
  first | exact @GlobalTheory.TwV.DelB.dgen_unit | exact GlobalTheory.TwV.DelB.dgen_unit | (intros; apply GlobalTheory.TwV.DelB.dgen_unit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd



theorem modelsAt_tr : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  intro D O N h H hT hk
  obtain ⟨h0, LC, hLC⟩ := H hT hk
  refine ⟨h0, LC, fun μ hμ u w hg hq => ?_⟩
  obtain ⟨c1, c2⟩ := hLC μ hμ u w hg hq
  exact ⟨GlobalTheory.T.latticeChainComparison_indep_divisionLattices D N h _ _ u μ w hg _ _ _ c1, GlobalTheory.T.siteAdmissible_indep_divisionLattices D N h u w hg _ _ _ c2⟩

end GlobalTheory.Svd
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem bAt_orth_lev : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j), cT (sigD D : D.host.E →+* D.host.E) (bAt J j hj a).1 * gramN D j hj * (bAt J j hj a).1 = 1 ∧ ∀ a', bAt J j hj a' = bAt J j hj a) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj a
  cases j with
  | zero =>
    refine ⟨?_, fun a' => rfl⟩
    exact J.Gd.cmp.B_std.1
  | succ j =>
    refine ⟨(H.core j hj _).std, fun a' => J.oneB j hj _ _⟩

end GlobalTheory.TwV.DelA
end
