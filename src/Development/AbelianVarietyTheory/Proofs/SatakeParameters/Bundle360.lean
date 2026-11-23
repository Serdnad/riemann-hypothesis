module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle348
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle339
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle332
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle338
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle302
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle353
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle356
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle227
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatPt

theorem isPtAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) ×
          GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp
  exact ⟨GlobalTheory.T.pointLattice_moved_rational_isometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp, GlobalTheory.T.chartPointFrames_move_rationalIsometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp,
    GlobalTheory.T.levelPrimeFunctionals_move_rationalIsometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp⟩

theorem xiPt_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi
  rcases lt_trichotomy i t.m2 with h | h | h
  · exact GlobalTheory.T.matrixStepDatum_equivariant_rational_unitary A dtU a hP hTie i hi h
  · exact GlobalTheory.T.firstCoupledStepDatum_rationalUnitary_equivariant A dtU a hP hTie i hi h
  · exact GlobalTheory.T.lastStepDatum_equivariant_rationalUnitary A dtU a hP hTie i hi h

theorem ratLaw_of_tie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → (∀ i hi, PtAway A a i hi) → RatLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hAw
  intro i hi β β' x x' x₁ x₁' γ hγ γ' hγ' h₁ h₁' z
  obtain ⟨g, hg⟩ := GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry A dtU a hP hTie i (Nat.le_of_succ_le hi) γ hγ
  obtain ⟨g', hg'⟩ := GlobalTheory.T.rationalUnitary_orthonormalCoords_isColumnIsometry A dtU a hP hTie (i + 1) hi γ' hγ'
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  have hq := isPtAd_rat A dtU a hP hTie i (Nat.le_of_succ_le hi) β x x₁ γ hγ h₁ g hg p hp
  have hq' := isPtAd_rat A dtU a hP hTie (i + 1) hi β' x' x₁' γ' hγ' h₁' g' hg' p' hp'
  have hE1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' := ⟨⟨_, hq⟩, ⟨_, hq'⟩⟩
  have hE0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  have a1 := hAw i hi β β' x₁ x₁' x₁ x₁' _ _ _ _ hq hq' hE1.1.choose_spec hE1.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  have a0 := hAw i hi β β' x x' x x' _ _ _ _ hp hp' hE0.1.choose_spec hE0.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  unfold xiAd
  rw [dite_eq_left hE1, dite_eq_left hE0, a1, a0, GlobalTheory.T.orthonormalChange_intertwines_rationalIsometries A dtU a hP hTie i hi γ γ' g g' hg hg' z]
  rw [xiPt_smul A dtU a hP hTie i hi β β' x x' p p' hp hp' g g']

end GlobalTheory.RatPt

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SiteEx



theorem siteD_exists : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ J hQ
  have hfr := GlobalTheory.Ggeo.FracLocal.isFractionRing_gat Gl u w hg
  have hrat := GlobalTheory.TwUChiRat.chiRatAll_of_adTie t u μ J.St J.A J.Hh.dt J.a J.tie J.kin
  have hpT : ∀ i (hi : i ≤ D.R.m), ¬ D.what₂.places.resChar w ∣ (J.St i hi).T := fun i hi => by
    rw [J.tie.T_eq i hi]; exact hg.2.2.2.2.2
  have hψ : ∀ i hi, PsiEx (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) := fun i hi =>
    psiEx_of (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) hfr (fun β => hrat (i + 1) hi β)
      (fun β => J.ord (i + 1) hi β)
  let Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ) :=
    { Fo := foOf J.Hh J.St J.val
      chFin := fun i hi => J.fin (i + 1) hi
      S := fun i hi =>
        { B := (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹
          B_lat := fun β => GlobalTheory.T.inv_coords_isBasisAt_baseLattice_of_std_companion J.Gd.herm u w hg hi ((J.St (i + 1) hi).K β).lev (J.A.crd (i + 1) hi) J.a
            (hpT (i + 1) hi) (J.base (i + 1) hi β)
          ψ := fun β => (hψ i hi β).choose
          fin := fun β => fin_of _ β _ } }
  refine ⟨Z, rfl, ⟨fun i hi => hpT (i + 1) hi, fun i hi w' hw' => ?_, fun i hi => trivial⟩, ⟨fun i hi => ?_, fun i hi β => ?_, fun i hi β cl => ?_⟩,
    fun i hi => ?_⟩
  · exact GlobalTheory.TwU.not_mem_underSB_of_gIdx t u w hg μ hQ w' (J.tie.bad (i + 1) hi w' hw')
  · show cT (sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 * gramN D (i + 1) hi *
      (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 = 1
    rw [MulEquiv.apply_symm_apply]
    exact std_of_C _ _ _ (J.pins.crd_orth (i + 1) hi)
  · exact (hψ i hi β).choose_spec
  · exact chRat_ofChiD J.chiD _ _ _
  · show Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹) = _
    exact MulEquiv.apply_symm_apply _ _

end GlobalTheory.SiteEx
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem stdG_one_apply {D : D7} {N : ℕ} (J : Matrix (Fin N) (Fin N) D.host.E) (v : Fin N → D.host.E) :
    stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J 1 v = v := by
  have h : ∀ w : Fin N → D.host.E, toLE (1 : GL (Fin N) D.host.E) w = w := by
    intro w
    simp [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]
  show (stdCo _ J) (toLE 1 ((stdCo _ J).symm v)) = v
  rw [h, LinearEquiv.apply_symm_apply]

theorem inFr_stdG_homRe {D : D7} {a b N N' : ℕ} (hr : a = N) (hr' : b = N') (J : Matrix (Fin N) (Fin N) D.host.E)
    (J' : Matrix (Fin N') (Fin N') D.host.E) (g : GL (Fin N) D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    Formalism.L2.Col.inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1) (homRe hr hr' x) =
      homRe hr hr' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) J g)) := by
  subst hr hr'
  apply LinearMap.ext
  intro v
  have h1 : ∀ w, (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1).symm w = w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, stdG_one_apply]
  simp only [Formalism.L2.Col.inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, homRe, eMat]
  congr 2
  ext i
  simp [Matrix.toLin'_apply, LinearMap.toMatrix'_mulVec]

end GlobalTheory.TwV.Xc



theorem GlobalTheory.TwV.Xc.xiM_smul_moveBy : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar ∧ ∀ x, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' x = (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, La) La' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLa hM La'
  have hj' : j + 1 ≤ D.R.m := hj
  have hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := (GlobalTheory.TwV.DelB.sysS_ranks S).2.2.1 (j + 1)
  obtain ⟨hg, hpt, -, r, hr0, -⟩ := hM
  have hκU := ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U_eq κ.1).1 κ.2).1

  have hdet : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) := det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, hκU⟩
  refine ⟨?_, fun x => ?_⟩
  · have hmu := S.law.mu_alg j hj _ hdet
    have hchi : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
      rw [← hr0]
      exact (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) r).algHom (D.what₂.embLL.toRatAlgHom))
    exact mul_mem hmu (inv_mem hchi)
  · have e1 := GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj' hr hr' (c, ((sysS H X std).Lv.lev j c).smul γ La) La' x
    have e2 := GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj' hr hr' (c, La) La'
      (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))
    have hch := GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j hj.le c (((sysS H X std).Lv.lev j c).smul γ La) La
      (GlobalTheory.GO.CmpMem.isLatTup_smul _ γ hLa) hLa
    rw [e1, e2, hch]
    have hx0 : (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)).1 * κ.1⁻¹ ∈
        UPts (sigD D) (gramN D j hj.le) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      mul_mem (J.pt std j hj.le _).2 (inv_mem hκU)
    have hlev := S.law.lev j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La')
      (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)) (J.pt std (j + 1) hj' La') κ 1
      (by show _ = _ * _ * _; group) (by simp) (homRe hr hr' x)
    have hrat := S.law.rat j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') (J.pt std j hj.le (c, La))
      (J.pt std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La') g hg 1 (one_mem _)
      (by show _ * _ = _; rw [hpt]; group) (by simp) (homRe hr hr' x)
    rw [inFr_stdG_homRe] at hrat
    rw [hrat] at hlev
    simp only [OneMemClass.coe_one, map_one, (S.law.mu_mul j hj).1, one_mul, Units.val_one, mul_one] at hlev
    have hc : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    linear_combination hlev
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc



theorem smulLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {a N : ℕ} (hr : a = N) (σ : E →+* E) (Jm : Matrix (Fin N) (Fin N) E)
    (g : GL (Fin N) E) (A A' : Submodule (𝓞 E) (Fin a → E)) (B B' : Submodule (𝓞 E) (Fin N → E)) (hA : HEq A B) (hA' : HEq A' B')
    (hB : B' = SDLat.smulLat (eMat rfl σ Jm g) B) : A' = SDLat.smulLat (eMat hr σ Jm g) A := by
  subst hr
  cases eq_of_heq hA
  cases eq_of_heq hA'
  exact hB

theorem kerN_smul : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLat hMove
  have hLat' : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLat
  have hch : J.chart std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) = J.chart std j hj.le (c, La) :=
    GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j hj.le c _ _ hLat' hLat
  have h1 := (hD j hj.le (c, La) hLat).2.2.1
  have h2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hLat').2.2.1
  obtain ⟨hg, hpt, -, -⟩ := hMove
  rw [hch, hpt] at h2
  exact smulLat_of_heq hr _ _ g _ _ _ _ h1 h2 (latK_rat_mul_lev D _ _ _ _ _ _ _ _ κ g hg)

end GlobalTheory.TwV.Xc
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB



theorem scalAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.ScalAt S j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d j hj La La' hLa hLa'
  obtain ⟨hmm, ht, hN, -⟩ := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hj0 : j ≤ D.R.m := hj.le
  have hj1 : j + 1 ≤ D.R.m := hj
  have hdt0 := (hD j hj0 La hLa).2.2.2
  have hdt1 := (hD (j+1) hj1 La' hLa').2.2.2
  have e0 := d.eq j hj0 La hLa
  have e1 := d.eq (j+1) hj1 La' hLa'
  have M0 := GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj j hj0 (clsAt X H j La.1 La.2) (J.pt std j hj0 La) (d.gam j hj0 La) (d.mem j hj0 La) (d.kap j hj0 La) e0
  have M1 := GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj (j+1) hj1 (clsAt X H (j+1) La'.1 La'.2) (J.pt std (j+1) hj1 La') (d.gam (j+1) hj1 La') (d.mem (j+1) hj1 La') (d.kap (j+1) hj1 La') e1
  have C0 := GlobalTheory.T.character_detIdeal_kernelLattice_latticeTuple S hD d j hj0 La hLa
  have C1 := GlobalTheory.T.character_detIdeal_kernelLattice_latticeTuple S hD d (j+1) hj1 La' hLa'
  have eN0 : (((sysS H X std).Pj j).m + 1) / 2 = D.R.N j / 2 := by rw [hN]
  have eN1 : (((sysS H X std).Pj (j + 1)).m + 1) / 2 = D.R.N (j + 1) / 2 := by rw [hN]
  have R0 : ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) =
      (((t.O u μ).mt (j + 1) ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ)⁻¹ *
        ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ (-(((D.R.N (j + 1) / 2 : ℕ) : ℤ))) := by
    simp [GL3Theta.rhoOf]
  have R1 : ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) =
      (((t.O u μ).mt (j + 1) ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) *
        ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ ((((D.R.N j / 2 : ℕ) : ℤ))) := by
    simp [GL3Theta.rhoOf']
  simp only [Dec.sC, Dec.sP, Dec.uS, Dec.uT, scal0, Base.chiFac, dif_pos hj1, dif_pos hj0]
  rw [R0, R1, hdt0, hdt1, M0.1, M1.1, C0.1, C1.1, eN0, eN1, ht]
  exact GlobalTheory.T.pullback_contraction_scalars_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cTw D j) (cTw D (j + 1)) (Units.ne_zero _) (Units.ne_zero _) M0.2.1 M1.2.1 M0.2.2 M1.2.2
    (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _) C0.2 C1.2

end GlobalTheory.TwV.DelB
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ i (hi : i + 1 ≤ D.R.m) (c : (sysS H X std).Lv.comp (i + 1)) (La : ((sysS H X std).Pj (i + 1)).Tup) (γ : ((sysS H X std).Lv.lev (i + 1) c).Γ), ((sysS H X std).Pj (i + 1)).IsLatTup La → ∃ g κ, MoveBy std J (i + 1) hi c La γ g κ) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_succ | exact GlobalTheory.TwV.Xc.moveBy_succ | (intros; apply GlobalTheory.TwV.Xc.moveBy_succ <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_normalisingCharPow_values_in_coeffField : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), (sysS H X std).Lv.comp j → ∀ x ∈ U1 (sigD D), ∃ r : D.what₂.LL, D.what₂.embLL r = chiI J x ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
  first | exact @GlobalTheory.TwV.Xc.chiI_pow_rat | exact GlobalTheory.TwV.Xc.chiI_pow_rat | (intros; apply GlobalTheory.TwV.Xc.chiI_pow_rat <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem dec_update : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (γ : GL (Fin (D.R.N (j + 1))) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) → ∀ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = GlobalTheory.TwU.ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 → ∃ d : Dec J std, d.gam (j + 1) hj La = γ ∧ d.kap (j + 1) hj La = κ) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S hD j hj La hLa γ hγ κ hκ
  obtain ⟨d0⟩ := GlobalTheory.T.exists_adelic_latticeTuple_decomposition S hD
  have key : ∀ k (hk : k ≤ D.R.m) (Lb : (sysS H X std).Lt k), ∃ (g : GL (Fin (D.R.N k)) D.host.E)
      (c : ((J.St k hk).K (J.chart std k hk Lb)).lev.U),
      g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk) ∧
      (((sysS H X std).Pj k).IsLatTup Lb.2 →
        (J.pt std k hk Lb).1 = GlobalTheory.TwU.ratA D.host.F g * ((J.St k hk).y (clsAt X H k Lb.1 Lb.2)).1 * c.1) ∧
      (∀ _ : k = j + 1, HEq Lb La → HEq g γ ∧ HEq c κ) := by
    intro k hk Lb
    by_cases h : k = j + 1 ∧ HEq Lb La
    · obtain ⟨rfl, h2⟩ := h
      obtain rfl := eq_of_heq h2
      exact ⟨γ, κ, hγ, fun _ => hκ, fun _ _ => ⟨HEq.rfl, HEq.rfl⟩⟩
    · exact ⟨d0.gam k hk Lb, d0.kap k hk Lb, d0.mem k hk Lb, d0.eq k hk Lb, fun e hL => absurd ⟨e, hL⟩ h⟩
  choose g c hm he hh using key
  exact ⟨⟨g, c, hm, he⟩, eq_of_heq (hh (j + 1) hj La rfl HEq.rfl).1, eq_of_heq (hh (j + 1) hj La rfl HEq.rfl).2⟩

end GlobalTheory.TwV.DelA
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.PtOrd

theorem det_reGL' {R : Type} [CommRing R] {a b : ℕ} (e : Fin a ≃ Fin b) (x : GL (Fin a) R) :
    Matrix.GeneralLinearGroup.det (reGL e x) = Matrix.GeneralLinearGroup.det x := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_reindex_self e _

theorem det_bc' {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m] (φ : A →+* B) (x : GL m A) :
    ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc φ x) : Bˣ) : B) = φ ((Matrix.GeneralLinearGroup.det x : Aˣ) : A) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

theorem det_castGL' {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin a) R) :
    ((Matrix.GeneralLinearGroup.det (castGL h R g) : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) := by
  subst h
  simp [castGL, Matrix.GeneralLinearGroup.val_det_apply]

theorem phiA_det_eps {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n k p : ℕ} {G : GAtP p}
    (A : LocAt F E n G) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (S : Set (GL (Fin n) (AfE F E)))
    (hex : ∃ x, A.IsPt i g x ∧ x ∈ S) (e : Fin n ≃ Fin k) (v : Fin G.P.nV) :
    phiA A v ((Matrix.GeneralLinearGroup.det (reGL e (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ S)) : (AfE F E)ˣ) : AfE F E) =
      (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)).det := by
  rw [det_reGL']
  have hx := (Classical.epsilon_spec hex).1
  have h := congrArg (fun y => ((Matrix.GeneralLinearGroup.det y : _ˣ) : (A.pl v).1.adicCompletion F)) (hx.2 v)
  have e : ∀ (a b : ((A.pl v).1.adicCompletion F)ˣ), a * b * a⁻¹ = b := fun a b => by
    rw [mul_comm a b, mul_inv_cancel_right]
  simp only [map_mul, map_inv] at h
  rw [det_bc', det_bc'] at h
  have h2 : A.ph v (prV (E := E) (A.pl v).1 ((Matrix.GeneralLinearGroup.det (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ S) : _ˣ) : _)) =
      A.eQ v ((Matrix.GeneralLinearGroup.det (g v) : _ˣ) : _) := by
    rw [h, e, det_bc', det_castGL']
    rfl
  show (A.eQ v).symm (A.ph v (prV (E := E) (A.pl v).1 _)) = _
  rw [h2, RingEquiv.symm_apply_apply, Matrix.GeneralLinearGroup.val_det_apply]

end GlobalTheory.TwV.Xc.PtOrd

noncomputable section
namespace GlobalTheory.TwV.Xc.PtOrd

open Formalism.L2.KerInert.SecondKernelInstances

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

theorem latAt_bases (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) ((basesAt Ch std vp unif eO eO_spec dG dG_spec om j Lt v : GL _ _) : Matrix _ _ _) := by
  have hx : ∃ g : GL (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1)) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v), (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (g : Matrix _ _ _) := by
    cases j with
    | zero =>
      obtain ⟨g, hg, hLg⟩ := hL v
      exact ⟨Matrix.nonsingInvUnit g hg, hLg⟩
    | succ i =>
      obtain ⟨g, hg, hLg⟩ := hL v
      exact ⟨Matrix.nonsingInvUnit g hg, hLg⟩
  exact Classical.epsilon_spec hx

theorem len_bases (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    len (sysAt Ch std vp unif eO eO_spec dG dG_spec om) v j Lt = -ordP ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w)
      ((Matrix.GeneralLinearGroup.det (basesAt Ch std vp unif eO eO_spec dG dG_spec om j Lt v) : _ˣ) : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v) := by
  have hS := (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.setting v
  have := hS.frac_alt
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  cases j with
  | zero =>
    unfold len
    show lenLat ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v 0 Lt) = _
    rw [latAt_bases Ch std vp unif eO eO_spec dG dG_spec om 0 Lt hL v,
      lenLat_colSpan hS.p_unif _ ((Matrix.isUnit_iff_isUnit_det _).1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om 0 Lt v).isUnit)]
  | succ i =>
    unfold len
    show lenLat ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt) = _
    rw [latAt_bases Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt hL v,
      lenLat_colSpan hS.p_unif _ ((Matrix.isUnit_iff_isUnit_det _).1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt v).isUnit)]

theorem cpAt_y_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).y (i + 1) La =
      reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
          (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).y = _
  simp only [chAt, dif_pos hi]

end GlobalTheory.TwV.Xc.PtOrd
end
namespace GlobalTheory.TwV.Xc



theorem latticeTuplePoint_det_normOne_order_eq_neg_length : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → (J.fd std).dt j La ∈ U1 (sigD D) ∧ ∀ v : (sysS H X std).Pl, ordA (A0 J) v ((J.fd std).dt j La) = -len (sysS H X std) v j La.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj La hLa
  obtain ⟨⟨hr, hpt⟩, -, -, hdt⟩ := hD j hj La hLa
  refine ⟨hdt ▸ Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) _ (J.pt std j hj La).2, fun v => ?_⟩
  rw [PtOrd.len_bases (chainAt H hT) std _ _ _ _ _ _ _ j La.2 hLa v, neg_neg, hdt]
  unfold ordA
  rw [hpt]
  erw [PtOrd.det_reGL']
  cases j with
  | zero =>
    exact congrArg _ (PtOrd.phiA_det_eps (A0 J) La.1 _ _ (let hG := J.one.good; ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩) _ v)
  | succ i =>
    have hP := (GlobalTheory.T.stepCharts_places_firstFactor_eq_stepZero S hD hS i hj ((I.at' i hj).st.eC.symm La.1).1 v).2
    rw [PtOrd.cpAt_y_succ (chainAt H hT) std _ _ _ _ _ _ _ I _ _ _ _ i hj La, ← hP]
    exact congrArg _ (PtOrd.phiA_det_eps _ _ _ _ (let hG := (H.core i hj ((I.at' i hj).st.eC.symm La.1).1).good; ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩) _ v)

end GlobalTheory.TwV.Xc
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_good_chart_lastStep_allTuples : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a B.R.m).Cl → Ch) (Kc : Fam I l Z u a B.R.m le_rfl (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a B.R.m le_rfl chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.chart_last_good | exact GlobalTheory.TwU.AtTrue.chart_last_good | (intros; apply GlobalTheory.TwU.AtTrue.chart_last_good <;> assumption)
end
