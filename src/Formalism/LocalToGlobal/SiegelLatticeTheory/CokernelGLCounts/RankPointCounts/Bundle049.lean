module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CongAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameEntry
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealPhaseFrames
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem g_mem_qq : ((Lat.gS D : ℕ) : D.host.E) ∈
    ((Formalism.L2.SG.Pf.StabIntSh.qq D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
  (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mem_span_singleton_self _, by simp⟩

theorem g_mul_mem {k : ℕ} {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    ((Lat.gS D : ℕ) : D.host.E) * x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k :=
  FractionalIdeal.mul_mem_mul g_mem_qq hx

theorem o_mem_ddPow (k : ℕ) (o : 𝓞 D.host.E) : (o : D.host.E) ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have h := (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ o ((FractionalIdeal.mem_coe).2 (one_mem_ddPow (D := D) k)))
  rwa [Algebra.smul_def, mul_one] at h

theorem cong_glob {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hX : XLam Λ F = XS D F.fl) (hX' : XLam Λ F' = XS D F'.fl) (hz : F.fl.z ∈ Λ) (hz' : F'.fl.z ∈ Λ)
    (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    uu j i - uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D ((i : ℕ) - (j : ℕ)) := by
  have h1 : uu j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) := frame_entry F Λ hX hz s hs uu huu hfr j i hji
  have h2 : uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) :=
    frame_entry F' Λ hX' hz' s hs uu' huu' hfr' j i hji
  have hd : uu j i - uu' j i ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D ((i : ℕ) - (j : ℕ)) :=
    (FractionalIdeal.mem_coe).1 (Submodule.sub_mem _ ((FractionalIdeal.mem_coe).2 h1) ((FractionalIdeal.mem_coe).2 h2))
  refine (FractionalIdeal.mem_coe).1 (mem_of_loc _ _ fun P => ?_)
  by_cases hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨t, ht, o, ho⟩ := cong_at F F' Λ hc hc' hz' hadm s hs uu uu' huu huu' hfr hfr' P hgP j i hji
    refine ⟨t, ht, ?_⟩
    rw [ho]
    exact (FractionalIdeal.mem_coe).2 (g_mul_mem (o_mem_ddPow _ o))
  · refine ⟨((Lat.gS D : ℕ) : 𝓞 D.host.E), hgP, ?_⟩
    have e : (((Lat.gS D : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Lat.gS D : ℕ) : D.host.E) := by simp
    rw [e]
    exact (FractionalIdeal.mem_coe).2 (g_mul_mem hd)

end Formalism.L2.SG.Pf.ZsVolLat

end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB

variable {D : Formalism.BasicNotions.D7}

theorem orbCut_all {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : OrbCut M a c := by
  haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  exact Formalism.L2.SG.Pf.LocOrbCut.orbitDecomposition_of_integrand M hOK a c (Formalism.L2.SG.Pf.LocOrbCut.val M hOK a c)

theorem localOrbitSum_holds (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (hA : ∀ p, Agree δ M p) :
    LocOrbSum M δ u u' :=
  locOrbSum_of M δ u u' (fun p w => modShift_holds δ _ _ p w)
    (fun p a c => orbCut_all (M p) (hA p).1 a c)
    (fun p => nAutNe_of M p (hA p).1)

end Formalism.L2.SG.Pf.LocOrbSumPf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def yT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : MatP D p :=
  CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p

def LocClsE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p,
    IntP M p (yT M δ u u' F0 what₂ γ p) ∧ InOrbP δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)

def PhCls : Prop :=
  ∀ (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y Y' : MatP D p), (M p).OK →
    IntP M p Y → InOrbP δ T T' p w Y → InOrbP δ T T' p w Y' → Y' ∈ kkOrb M p Y →
    phL M δ T T' p w Y' = phL M δ T T' p w Y

def PhaseProd : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)).Finite ∧
    PairVal.phaseAt γ w = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)

def VolProd : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    (Function.mulSupport fun p =>
      (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)).Finite ∧
    (PairVal.vRdef D u u' F0 what₂ δ M γ : ℂ) =
      ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) *
        ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)

end Steps

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem repL_spec' {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {O : Set (MatP D p)}
    (h : IsLCls M δ T T' p w O) :
    IntP M p (repL M δ T T' p w O) ∧ InOrbP δ T T' p w (repL M δ T T' p w O) ∧ O = kkOrb M p (repL M δ T T' p w O) := by
  unfold repL; rw [dite_eq_left h]; exact h.choose_spec

theorem wtL_congr {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {Y Y' : MatP D p}
    (h : kkOrb M p Y = kkOrb M p Y') : wtL M δ T T' p w Y = wtL M δ T T' p w Y' := by
  unfold wtL; rw [h]

theorem hL_at {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {Y : MatP D p}
    (hPC : PhCls M δ) (hOK : (M p).OK) (hY : IntP M p Y) (hO : InOrbP δ T T' p w Y) :
    hL M δ T T' p w (kkOrb M p Y) = phL M δ T T' p w Y * (wtL M δ T T' p w Y : ℂ) := by
  have hcls : IsLCls M δ T T' p w (kkOrb M p Y) := ⟨Y, hY, hO, rfl⟩
  obtain ⟨-, hrO, hrE⟩ := repL_spec' hcls
  unfold hL
  rw [if_pos hcls]
  generalize repL M δ T T' p w (kkOrb M p Y) = R at hrO hrE ⊢
  have hmem : R ∈ kkOrb M p Y := by
    rw [hrE]; exact PCount.mem_kkOrb_self p R
  rw [hPC T T' p w Y R hOK hY hO hrO hmem, wtL_congr hrE.symm]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coefProd_of (hA : ∀ p, Agree δ M p) (hC : LocClsE M δ u u' F0 what₂) (hPC : PhCls M δ) (hP : PhaseProd M δ u u' F0 what₂)
    (hV : VolProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ := by
  intro γ w hγ
  obtain ⟨hPf, hPe⟩ := hP γ w hγ
  obtain ⟨hVf, hVe⟩ := hV γ w hγ
  have hfac : ∀ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p) =
      phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) *
        (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) := by
    intro p
    obtain ⟨hyI, hyObP⟩ := hC γ w hγ p
    show hL M δ (D.mem u).A.T (D.mem u').A.T p w (kkOrb M p (yT M δ u u' F0 what₂ γ p)) = _
    exact hL_at hPC (hA p).1 hyI hyObP
  unfold PairVal.cAt
  rw [hPe, hVe, finprod_congr hfac, finprod_mul_distrib hPf hVf]
  ring

end Assembly

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal.PgLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_F {D : D7} (X : HidaSetting D) : Module.finrank ℚ X.B.I.F = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  omega

theorem one_factor (k b g : ℝ) (f : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b) (hg : (k * b) ^ 8 ≤ g) (hf : (f : ℝ) ≤ k) :
    (1 + 3 / g) ^ f ≤ Real.exp (1 / 4) := by
  have hk0 : 0 ≤ k := by linarith
  have hkb : 2 * k ≤ k * b := by nlinarith
  have hkb2 : 2 ≤ k * b := by linarith
  have h7 : (2:ℝ) ^ 7 ≤ (k * b) ^ 7 := by gcongr
  have h9 : (k * b) * 2 ^ 7 ≤ (k * b) * (k * b) ^ 7 := mul_le_mul_of_nonneg_left h7 (by linarith)
  have h8 : (k * b) ^ 8 = (k * b) * (k * b) ^ 7 := by ring
  have hg12 : 12 * (f : ℝ) ≤ g := by nlinarith
  have hgpos : 0 < g := by nlinarith
  have hx : 1 + 3 / g ≤ Real.exp (3 / g) := by
    have := Real.add_one_le_exp (3 / g)
    linarith
  have h0 : 0 ≤ 1 + 3 / g := by positivity
  calc (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := by gcongr
    _ = Real.exp (f * (3 / g)) := (Real.exp_natCast_mul f _).symm
    _ ≤ Real.exp (1 / 4) := by
        apply Real.exp_le_exp.mpr
        have he : (f : ℝ) * (3 / g) = 3 * f / g := by ring
        rw [he, div_le_iff₀ hgpos]
        linarith

theorem exp_quarter_mul_exp_quarter_le_two : Real.exp (1 / 4) * Real.exp (1 / 4) ≤ 2 := by
  rw [← Real.exp_add]
  have h : Real.exp (1 / 4 + 1 / 4) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := Real.exp_one_lt_d9
  have hpos := Real.exp_pos (1 / 4 + 1 / 4)
  nlinarith

theorem pgLeC_of (hS : Formalism.L2.SG.Pf.SatGramLoc.SplitPrimeLoc) (hRC : Formalism.L2.SG.Pf.SatGramLoc.RedCore) : PgLeC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y hH => ?_⟩
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' hS hRC Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (1 / 4) * Real.exp (1 / 4) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 2 := exp_quarter_mul_exp_quarter_le_two

end Formalism.L2.SG.KappaOffDiagonal.PgLe
end
end

section

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def RealDecompC : Prop :=
  ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), t.relevant → t.G ≠ 0 →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ) ∧
      ∀ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ →
        ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u', t.pt.1 = g * γ * g'⁻¹

theorem isPtRep_gamW {w : Point D.host.E (D.R.rS + 1)} (h : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    Formalism.L2.SG.RealObj.IsPtRep X u u' w (Formalism.L2.SG.RealObj.gamW X u u' w) := by
  unfold Formalism.L2.SG.RealObj.gamW
  rw [dite_eq_left h]
  exact h.choose_spec

theorem realDecompC_gamW (h : RealDecompC X Y u u')
    (t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hrel : t.relevant) (hG : t.G ≠ 0) :
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) * g'⁻¹ := by
  obtain ⟨hex, hall⟩ := h t hrel hG
  exact ⟨hex, hall _ (isPtRep_gamW X u u' hex)⟩

theorem realDecomp_G_ne (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (h : (Y.tO u u').G s ≠ 0) : s.G ≠ 0 := by
  intro h0
  apply h
  show Formalism.L2.SG.TermOp.Gt s = 0
  simp [Formalism.L2.SG.TermOp.Gt, h0]

theorem liftDecompC_of_real (h : RealDecompC X Y u u') : LiftDecompC X Y u u' κ := by
  intro R ρ s hrel
  exact realDecompC_gamW X Y u u' h s.1 hrel (realDecomp_G_ne X Y u u' s.1 s.2.1)

end Formalism.L2.SG.Pf.RowForm
end
end

section

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.FinitePhase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftCellC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : Formalism.L2.SG.Pf.RowForm.LiftT X Y u u' κ R ρ),
    s.1.relevant →
    ∃ L U : Formalism.L2.SG.PairVal.MatR D, IsLoUni L ∧ IsUpUni U ∧
      ZhatOM (ZhatL (lf D (X.Fu u)) s.1.frame) = L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U ∧
      ∀ v, Formalism.L2.SG.RealObj.ZhatO (Formalism.L2.SG.RealObj.ZX X u u' 1 s.1.pt.1 v) =
        (L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U).map (fun x => X.B.I.φ v (X.ιE.symm x))

def FinPhaseC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : Formalism.L2.SG.Pf.RowForm.LiftT X Y u u' κ R ρ),
    s.1.relevant → ∀ L U : Formalism.L2.SG.PairVal.MatR D, IsLoUni L → IsUpUni U →
      ZhatOM (ZhatL (lf D (X.Fu u)) s.1.frame) = L * ptMat (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * U →
      Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) * Formalism.L2.SG.PairVal.phasePair (gS D) L U =
        Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

theorem phaseTieC_of (hC : LiftCellC X Y u u' κ) (hF : FinPhaseC X Y u u' κ) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ := by
  intro R ρ s hrel g hg g' hg' hdec
  obtain ⟨L, U, hL, hU, hrat, hreal⟩ := hC R ρ s hrel
  have hex := Formalism.L2.SG.RealObj.RealPointRepresentatives.exists_ptRep X u u' s.1.pt.1 _ L U hL hU hreal
  have hPt : Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) := by
    unfold Formalism.L2.SG.RealObj.gamW
    rw [dite_eq_left hex]
    exact hex.choose_spec
  rw [Formalism.L2.SG.RealObj.RealPhaseFrames.realPhase X u u' hg hg' hdec _ hPt L U hL hU hreal]
  exact hF R ρ s hrel L U hL hU hrat

end Formalism.L2.SG.Pf.FinitePhase
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def GlobSet (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) :
    Set (Submodule (𝓞 D.host.E) (VS D).V) :=
  {Λ₂ | Submodule.IsFullLattice D.host.E Λ₂ ∧
    ∀ p, lattice₂ D Zd.M p Λ₂ ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p)}

variable (u u' F0 what₂)

def FStarC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∃ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z ∧ (∀ p, φ p = LinearEquiv.refl _ _) ∧
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) ∧
    (∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ₀ ∧
      {p | locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) ≠ {lattice₂ D Zd.M p Λ₀}}.Finite) ∧
    Nonempty (frPart γ Z ≃ GlobSet Zd γ F'₂ φ φ')

def PatchC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z →
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) →
    (∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ₀ ∧
      {p | locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) ≠ {lattice₂ D Zd.M p Λ₀}}.Finite) →
    Nat.card (GlobSet Zd γ F'₂ φ φ') = ∏ᶠ p, Nat.card (locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p))

variable {u u' F0 what₂}

theorem frGlob_of (hA : FStarC Zd u u' F0 what₂) (hB : PatchC Zd u u' F0 what₂) : FrGlob Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ
  obtain ⟨F'₂, φ, φ', hF, -, hT, hC, ⟨e⟩⟩ := hA γ w hγ w' hG' hk Z hZ
  refine ⟨F'₂, φ, φ', hF, hT, ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr e]
  exact hB γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT hC

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end
