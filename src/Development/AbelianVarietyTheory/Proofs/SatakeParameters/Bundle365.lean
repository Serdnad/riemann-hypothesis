module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle359
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle304
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle310
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle172
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle358
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle176
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.ChartPosEqOfIw
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle360
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle361
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.joint_dict : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  intro j hj La hLa
  cases j with
  | zero =>
    have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).1
    exact ⟨hp, GlobalTheory.T.stepZero_point_mem_doubleCoset_classRep t std J La hLa, GlobalTheory.T.stepZero_kernelLattice_eq_pointKernelLattice t std J La, GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det t std J 0 hj La _ hp⟩
  | succ j =>
    have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).1
    exact ⟨hp, GlobalTheory.T.succStep_point_mem_doubleCoset_classRep t std J j hj La hLa, GlobalTheory.T.succStep_kernelLattice_eq_pointKernelLattice t std J j hj La hLa, GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det t std J (j + 1) hj La _ hp⟩
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc



theorem lambdaCharacter_norm_eq_p_pow_of_pos : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m), FillAt (hT := hT) (H := H) (X := X) std j hj → ∀ x ∈ U1 (sigD D), ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * ordA (A0 J) v x)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hSpl hPos j hj hFill x hx
  have hsc : ∀ y, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  have hσ : ∀ a, sigD D (sigD D a) = a := fun a => by rw [hsc a]; exact Formalism.L2.PairingIndexBounds.F.sigD_conj D a
  obtain ⟨m, z, k, hm, hz, hkU, hkI, hxm⟩ := exists_pow_normOne_idele_eq_principal_mul_integralUnit _ _ (sigD D) hσ x hx
  have hz' : (z : D.host.E) * D.host.conj (z : D.host.E) = 1 := by rw [← hsc]; exact hz
  have hzU := GlobalTheory.TwV.MuLawPf.rationalIdele_mem_normOne_of_norm_eq_one z hz'
  have hmul := S.law.mu_mul j hj
  have hpow : ∀ n : ℕ, S.muT (j + 1) (x ^ n) = S.muT (j + 1) x ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, hmul.1]
    | succ n ih => rw [pow_succ, pow_succ, hmul.2 _ (pow_mem hx n) _ hx, ih]
  have hsplit : S.muT (j + 1) x ^ m = S.muT (j + 1) (ratId D.host.F D.host.E z) * S.muT (j + 1) k := by
    rw [← hpow, hxm, hmul.2 _ hzU _ hkU]
  obtain ⟨e, he, hrat⟩ := S.law.mu_rat j hj

  obtain ⟨y, hy⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hkU
  obtain ⟨n, hn, hroot⟩ := GlobalTheory.TieFinOrd.mt_finite_order J.A J.dtU J.a J.pins J.tie j hj y (by rw [hy]; exact hkI)
  have hkroot : S.muT (j + 1) k ^ n = 1 := by
    rw [← hy, S.law.mu_read j hj y, ← Units.val_pow_eq_pow_val, hroot, Units.val_one]

  have ha := S.law.mu_alg j hj x hx
  have hb := S.law.mu_alg j hj _ hzU
  have hc := S.law.mu_alg j hj k hkU
  have hlamC : ∀ (a : ℂ) (h : a ∈ TaylorLogMetric.Qbar), TaylorLogMetric.lamC S.lam a = S.lam ⟨a, h⟩ := fun a h => by
    unfold TaylorLogMetric.lamC; rw [dite_eq_left h]
  have eQ : (⟨S.muT (j + 1) x, ha⟩ : TaylorLogMetric.Qbar) ^ m = ⟨_, hb⟩ * ⟨_, hc⟩ := Subtype.ext (by push_cast; exact hsplit)
  have eQk : (⟨S.muT (j + 1) k, hc⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by push_cast; exact hkroot)
  have hnormk : ‖S.lam ⟨_, hc⟩‖ = 1 := by
    have h1 := congrArg (fun q => ‖S.lam q‖) eQk
    simp only [map_pow, norm_pow, map_one, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
  have hnorm_m : ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ ^ m = ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) (ratId D.host.F D.host.E z))‖ := by
    have h1 := congrArg (fun q => ‖S.lam q‖) eQ
    simp only [map_pow, norm_pow, map_mul, norm_mul, hnormk, mul_one] at h1
    rw [hlamC _ ha, hlamC _ hb]
    exact h1
  have hratN := GlobalTheory.TwU.RatNorm.norm_lamC_type_normOne D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std) hPos e (z : D.host.E) hz'
  rw [← hrat z hz'] at hratN

  have hvm : ∀ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) = ∑ s : Fin ((sysS H X std).G.P.n' v), (if IsOddPos s then -1 else 1) * e (hT.gat_pos u w hg ⟨v, s⟩) := by
    intro v
    refine vm_shift_cancels _ (sysS H X std) v (j + 1) (fun s => e (hT.gat_pos u w hg ⟨v, s⟩))
      (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)) (fun s => ?_)
    rw [hFill e he v s, sub_sub]

  have hord : ∀ v : (sysS H X std).Pl, (m : ℤ) * ordA (A0 J) v x = ordP ((sysS H X std).G.P.W v) (D.what₂.places.resChar w) (J.rho std v (z : D.host.E)) := by
    intro v
    obtain ⟨hadd, hint, hratO, -⟩ := OrdA.ordA_props _ _ _ _ _ (A0 J) J.one.int hSpl.1 v
    have hp : ∀ n : ℕ, ordA (A0 J) v (x ^ n) = n * ordA (A0 J) v x := by
      intro n
      induction n with
      | zero =>
        have h1 := hadd 1 1
        rw [mul_one] at h1
        rw [pow_zero, Nat.cast_zero, zero_mul]
        linarith
      | succ n ih => rw [pow_succ, hadd, ih]; push_cast; ring
    rw [← hp, hxm, hadd, hratO, hint k hkI, add_zero]
  rw [← pow_left_inj₀ (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _) hm.ne', hnorm_m, hratN, ← zpow_natCast, ← zpow_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hvm v, ← hord v]
  ring

end GlobalTheory.TwV.Xc

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.ChiHom

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} {t : KerEntTied ex}

theorem chiI_det (J : Joint t H X) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold chiI
  rw [dite_eq_left h]
  have e : h.choose = y := Subtype.ext (GlobalTheory.TwV.MuLawPf.generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]



theorem carries_std_of_int (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) (hy : Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E) :
    Formalism.L2.Herm.Carries y.1 (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) := by
  have hu := (Submonoid.mem_units_iff _ _).1 hy
  intro v
  show v ∈ latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E 1) ↔
    _ ∈ latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E 1)
  rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std]
  have e1 : Units.val ((y.1)⁻¹) 0 0 = Units.val ((Matrix.GeneralLinearGroup.det y.1)⁻¹) := by
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have e2 : ∀ i : Fin 1, (Matrix.mulVec (Units.val ((y.1)⁻¹)) v) i = Units.val ((Matrix.GeneralLinearGroup.det y.1)⁻¹) * v 0 := by
    intro i
    fin_cases i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
    rw [← e1]; rfl
  simp only [e2]
  constructor
  · intro h i
    exact mul_mem hu.2 (h 0)
  · intro h i
    fin_cases i
    have := mul_mem hu.1 (h 0)
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this



theorem dtU_mem_UO (J : Joint t H X) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hy : Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E) : J.dtU y ∈ D.UO := by
  have h := J.rel 1 ⟨_, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D 1⟩ ⟨_, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D 1⟩ y.1 y.2
    (carries_std_of_int y hy) y rfl
  exact (QuotientGroup.eq_one_iff _).1 (h.symm.trans (D.relDet_self _ _))

end GlobalTheory.TwV.Xc.ChiHom

namespace GlobalTheory.TwV.Xc


open GlobalTheory.TwV.Xc.ChiHom in

theorem chiI_hom : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), chiI J (x * y) = chiI J x * chiI J y) ∧ (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E → chiI J x = 1) ∧ (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ)) ∧ ∀ x ∈ U1 (sigD D), ∃ 𝔞, TaylorLogMetric.N1 D 𝔞 ∧ chiI J x = t.χ 𝔞) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _
  refine ⟨?_, ?_, fun y => chiI_det J y, ?_⟩
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hy
    have e : Matrix.GeneralLinearGroup.det x'.1 * Matrix.GeneralLinearGroup.det y'.1 =
        Matrix.GeneralLinearGroup.det (x' * y').1 := by
      rw [Subgroup.coe_mul, map_mul]
    rw [e, chiI_det, chiI_det, chiI_det, map_mul, map_mul, Units.val_mul]
  · intro x hx hint
    obtain ⟨y, rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    rw [chiI_det, D.chiD_UO _ (dtU_mem_UO J y hint), Units.val_one]
  · intro x hx
    obtain ⟨y, rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    refine ⟨t.idl (QuotientGroup.mk (J.dtU y)), (t.idl_ok.2.1 _).2 ⟨_, rfl⟩, ?_⟩
    rw [chiI_det, t.χ_rec, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
    rfl

end GlobalTheory.TwV.Xc

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_comparisonSiteData_over_chainCharts : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  first | exact @GlobalTheory.SiteEx.siteD_exists | exact GlobalTheory.SiteEx.siteD_exists | (intros; apply GlobalTheory.SiteEx.siteD_exists <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelLattice_movedLatticeTuple : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  first | exact @GlobalTheory.TwV.Xc.kerN_smul | exact GlobalTheory.TwV.Xc.kerN_smul | (intros; apply GlobalTheory.TwV.Xc.kerN_smul <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → (J.fd std).dt j La ∈ U1 (sigD D) ∧ ∀ v : (sysS H X std).Pl, ordA (A0 J) v ((J.fd std).dt j La) = -len (sysS H X std) v j La.2) := by
  first | exact @GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length | exact GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length | (intros; apply GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedDatum_movedLatticeTuple : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar ∧ ∀ x, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' x = (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, La) La' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))) := by
  first | exact @GlobalTheory.TwV.Xc.xiM_smul_moveBy | exact GlobalTheory.TwV.Xc.xiM_smul_moveBy | (intros; apply GlobalTheory.TwV.Xc.xiM_smul_moveBy <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTupleDecomposition_occurs_in_family : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (γ : GL (Fin (D.R.N (j + 1))) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) → ∀ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = GlobalTheory.TwU.ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 → ∃ d : Dec J std, d.gam (j + 1) hj La = γ ∧ d.kap (j + 1) hj La = κ) := by
  first | exact @GlobalTheory.TwV.DelA.dec_update | exact GlobalTheory.TwV.DelA.dec_update | (intros; apply GlobalTheory.TwV.DelA.dec_update <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTuplePairScalar_eq_characterProduct : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.ScalAt S j) := by
  first | exact @GlobalTheory.TwV.DelB.scalAt_all | exact GlobalTheory.TwV.DelB.scalAt_all | (intros; apply GlobalTheory.TwV.DelB.scalAt_all <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf (D.what₂.places.resChar w) ((sysS H X std).G.P.W v) (J.rho std v) P → ∀ j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → GL3Theta.EqOff D P ((J.fd std).kerN j La) ((J.fd std).kerN j Lb)) := by
  first | exact @GlobalTheory.TwV.Xc.eqOff_kerN_of_sameAway | exact GlobalTheory.TwV.Xc.eqOff_kerN_of_sameAway | (intros; apply GlobalTheory.TwV.Xc.eqOff_kerN_of_sameAway <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedDatum_eq_of_latticeTuples_agreeAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j < D.R.m) (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j Lb Lb') := by
  first | exact @GlobalTheory.TwV.Xc.xiM_eq_of_sameAway | exact GlobalTheory.TwV.Xc.xiM_eq_of_sameAway | (intros; apply GlobalTheory.TwV.Xc.xiM_eq_of_sameAway <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frM_eq_map_crd_mul_gam_inv_mul_basis : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) La v, d.fd2.frM j La v = (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr) * ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La))).map (J.rho std v)) := by
  first | exact @GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis | exact GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis | (intros; apply GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis <;> assumption)
end
