module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle026
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsEv Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ConcAt0 (D : D7) (T : TermTie D) where
  X : HidaSetting D
  Y : Full X
  hF : FinX Y
  hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF)
  jt : JtPin hF hI T
  wr : WRowPin hF hI T
  fc : FibreCount Y

section TransportedAlt

theorem loop_evaluation_threshold_zero (hLC : PN.LoopCores) (hSub : PB.SubFamily) (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio)
    (Cg cb Cw cT CT C0 A C₀ : ℝ) :
    ∃ C'₀ Cl₀ : ℝ, ∀ {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
      (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
      (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt0 (Fm.D x i) (At x hx i)),
      (∀ C : ℝ, C₀ ≤ C → OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A →
          Formalism.MainNotions.BridgeLemma.RowsND (At x hx i) (Yt x hx i u u') C ∧ Formalism.MainNotions.BridgeLemma.RowsDeg (At x hx i) (Yt x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (At x hx i) (Yt x hx i u u') C) →
      (OwnEv Fm fun C' Cl x i =>
        Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cw cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) →
      OwnEv Fm fun C' Cl x i => C'₀ ≤ C' → Cl₀ ≤ Cl →
        ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
          Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie (Cc x hx i).X (Cc x hx i).Y →
          ((Cc x hx i).Y.tO u u').AbsConv →
          ((Cc x hx i).Y.tO u u').RowBig (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') ∧
          ((Cc x hx i).Y.tO u u').RowNotScalar (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
  obtain ⟨C₃, _, HX⟩ := xiSizesC_of hS Cg cb Cw cT CT C0 A
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max C₀ C₃) (max CT 1) := ⟨_, rfl⟩
  have hCC₀ : C₀ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_left _ _)
  have hCC₃ : C₃ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_right _ _)
  have hCT : CT ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_left _ _)
  have hC : 1 ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_right _ _)
  obtain ⟨K₀, hJ⟩ := Formalism.L2.SG.RowsOther.rowLoops_of_input hLC hSub C hC
  obtain ⟨a3, b3, HX'⟩ := HX C hCC₃
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = max 1 C0 := ⟨_, rfl⟩
  have hA₀1 : 1 ≤ A₀ := by rw [hA₀]; exact le_max_left _ _
  refine ⟨max a3 K₀, max b3 (max 4 (3 + 6 * Real.log (3 * A₀))), ?_⟩
  intro eps Fm C1 At Yt Cc HR hFo
  refine (OwnEv.and (HR C hCC₀) hFo).mono ?_
  rintro C' Cl x i ⟨H1, H2⟩ hC' hCl hx u u' hH hT hA
  have ha3 : a3 ≤ C' := le_trans (le_max_left _ _) hC'
  have hK₀ : K₀ ≤ C' := le_trans (le_max_right _ _) hC'
  have hb3 : b3 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl4 : 4 ≤ Cl := le_trans (le_max_of_le_right (le_max_left _ _)) hCl
  have hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl := le_trans (le_max_of_le_right (le_max_right _ _)) hCl
  obtain ⟨hn, hd, h1⟩ := H1 hx u u' hH
  have hFo' := H2 hH.1 u
  have hGP : GamPin (Cc x hx i).Y := gammaFixed_of_hypotheses (Cc x hx i).Y hH.1
  have hXiH := HX' C' Cl ha3 hb3 (Fm.D x i) (Fm.L x i) u u' hH
  have hP := params_at hH.1 (Cc x hx i).X u hCl4 hCT hC hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b (Fm.D x i) (Fm.L x i)
  have hb0 : (0 : ℝ) < (Fm.L x i).sc.b := by linarith
  have hk0 : (0 : ℝ) < (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < (Fm.D x i).R.k)
  have hg : 0 < ((Cc x hx i).X.B.g : ℝ) := by
    have h5 : (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 ≤ ((Cc x hx i).X.B.g : ℝ) := hP.2.2.2.2.1
    have h8 : 0 < (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 := by positivity
    linarith
  have hv : 0 ≤ (Fm.D x i).host.v := by linarith [hP.2.2.2.2.2.2.1]
  have hC0' : (0 : ℝ) ≤ C := by linarith
  have hGam : 0 ≤ GamS (Fm.D x i) (Fm.L x i) := by unfold GamS; exact (Real.exp_pos _).le
  have HS : ∀ s, 2 ≤ s → s ≤ (Fm.D x i).R.k →
      ClassLe ((Cc x hx i).Y.tO u u') (bigS ((Cc x hx i).Y.tO u u') s)
        (A₀ * rowS C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f s (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
          (Fm.D x i).host.v (GamS (Fm.D x i) (Fm.L x i)) (Formalism.MainNotions.BridgeLemma.XiB (Fm.D x i) (Fm.L x i) u C) *
          ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    intro s h2 hk
    have hX0 := xi_nonneg hXiH s h2 hk
    rw [hA₀]
    exact rowsSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      hH C hn hd s h2 hk (ndRow_nonneg hC0' hb0 hg hv hGam hX0) (degRow_nonneg hC0' hb0 hg hv hGam hX0)
  have H1' : ClassLe ((Cc x hx i).Y.tO u u') (((Cc x hx i).Y.tO u u').nsc ((Cc x hx i).Y.tO u u').genSet)
      (A₀ * oneT C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
        (GamS (Fm.D x i) (Fm.L x i)) * ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    rw [hA₀]
    exact oneSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      C0 C hC0' h1
  obtain ⟨Al, NT', Gam, Xi, hAl, hP', hX', h6, hAmp⟩ :=
    loopsAmp_at hH hT hA hC hCT hK₀ hA₀1 hCl4 hClA hXiH HS H1'
  exact hJ _ _ _ _ _ ((Cc x hx i).Y.tO u u') (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f Al (Fm.L x i).sc.b
    ((Cc x hx i).X.B.g : ℝ) (Fm.D x i).host.v NT' Gam Xi (ddC (Cc x hx i).X (Cc x hx i).Y u u')
    hAl hP' hX' h6 (dd_nonneg hT u u') hA
    (Formalism.L2.SG.RowsOther.loopsInput_of_amp _ hA.2.2.le _ _ _ _ _ _ _ _ _ _ _ hAmp)

end TransportedAlt

section Fam5

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (_root_.Formalism.L2.SG.PackageTie2.sOf (hF x hx i)))
  (hCT : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcTie (X x hx i) (Y x hx i))


end Fam5

end Formalism.L2.SG.LoopsTies
end
end

section

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FibreCounting

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

theorem smul_cov (r χ χ' b : ℂ) (hχ : ‖χ‖ = 1) (O O' : V' →L[ℂ] V) (U : V' →L[ℂ] V') (hO : O' = b • O.comp U) :
    r • (χ' • O') = (χ' * b * χ⁻¹) • (r • (χ • O)).comp U := by
  have hχ0 : χ ≠ 0 := by intro h; rw [h, norm_zero] at hχ; exact zero_ne_one hχ
  rw [hO]
  simp only [ContinuousLinearMap.smul_comp, smul_smul]
  congr 1
  field_simp

theorem norm_cov (χ χ' b : ℂ) (hχ : ‖χ‖ = 1) (hχ' : ‖χ'‖ = 1) (hb : ‖b‖ = 1) : ‖χ' * b * χ⁻¹‖ = 1 := by
  rw [norm_mul, norm_mul, norm_inv, hχ, hχ', hb]; norm_num

end Gen

section Amp

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}



theorem oot_cov (hR : RatPt) (hC : ChiTrivialC) {s s' : _root_.Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) :
    ∃ (b : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖b‖ = 1 ∧ OOt s' = b • (OOt s).comp (cl U) := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  obtain ⟨hl, n, hn, ν, hν, c, hc, hg, hfix, he⟩ := fib_dec h
  have hm : s.lam' = s'.lam' := lam'_eq h
  obtain ⟨xn, hxn⟩ := hR D X n (nlam_isom hn)
  obtain ⟨xν, hxν⟩ := hR D X ν (nlam_isom hν)
  obtain ⟨xc, hxc⟩ := hR D X c hc
  have hpt : s'.pt = xn * s.pt * xν * xc :=
    ratLink_unique X s'.rep.2.1
      (ratLink_congr (ratLink_mul X (ratLink_mul X (ratLink_mul X hxn s.rep.2.1) hxν) hxc) he.symm)
  have hIA : IsAutLam (VS D) s.lam' c := ⟨hc, gmap_congr hg hm.symm⟩
  have hset : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν) :=
    (roset_congr hl.symm hm.symm he).trans (roset_c _ hIA hfix)
  have hconj : ∀ y, y ∈ ROinf s ↔ xn.1 * y * xn.1⁻¹ ∈ ROinf s' := fun y =>
    (roset_conj X hn hν hxn y).trans (Set.ext_iff.1 hset.symm _)
  have hex : (∃ Ω, IsSFund X.B.I (ROinf s) Ω) ↔ (∃ Ω, IsSFund X.B.I (ROinf s') Ω) := by
    constructor
    · rintro ⟨Ω, hΩ⟩
      refine ⟨_, isSF_image_mul xn.1 (fun y => ?_) hΩ⟩
      have e : xn.1 * (xn.1⁻¹ * y * xn.1) * xn.1⁻¹ = y := by group
      rw [hconj, e]
    · rintro ⟨Ω, hΩ⟩
      refine ⟨_, isSF_image_mul xn.1⁻¹ (fun y => ?_) hΩ⟩
      rw [inv_inv]
      exact hconj y
  by_cases hE : ∃ Ω, IsSFund X.B.I (ROinf s') Ω
  · have hE0 := hex.2 hE
    have hΩp : IsSFund X.B.I (ROinf s) (FundOf s) := by
      unfold FundOf; rw [dite_eq_left hE0]; exact hE0.choose_spec
    have hΩq : IsSFund X.B.I (ROinf s') (FundOf s') := by
      unfold FundOf; rw [dite_eq_left hE]; exact hE.choose_spec
    have key := oo_rel nLamNinf_holds hC Y s.mem s.mem' s.rep hn hν hxn hxν hΩp (isSFund_congr hset hΩq)
    have hsinv : xc.1⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' (sinf_of_fix hxc hfix)
    have hB : ∀ x, X.Wu u' (xc.1⁻¹ * x) =
        X.psiInfU u' xc.1⁻¹ • (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv) (X.Wu u' x) :=
      fun x => (X.Wu_spec u').1 _ hsinv x
    have e1 : OOt s' = conj (X.psiInfU u' xc.1⁻¹) •
        (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') (xn * s.pt * xν).1).comp
          ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv :
            X.Vpi u' →L[ℂ] X.Vpi u') := by
      unfold OOt
      rw [hpt, Prod.fst_mul]
      exact OO_right _ _ _ _ _ xc.1 _ _ hB
    refine ⟨conj (X.psiInfU u' xc.1⁻¹) * (X.psiInfU u xn.1 * X.psiInfU u' xν.1),
      (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm, ?_, ?_⟩
    · rw [norm_mul, RCLike.norm_conj, norm_mul, psiInfU_norm, psiInfU_norm, psiInfU_norm]; norm_num
    · have key' : OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') (xn * s.pt * xν).1 =
          (X.psiInfU u xn.1 * X.psiInfU u' xν.1) • OOt s := key
      rw [e1, key']
      have hU : ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv :
          X.Vpi u' →L[ℂ] X.Vpi u') = cl (Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm := by
        ext x; rfl
      rw [hU, ContinuousLinearMap.smul_comp, smul_smul]
  · have hE0 : ¬ ∃ Ω, IsSFund X.B.I (ROinf s) Ω := fun h0 => hE (hex.1 h0)
    have h1 : OOt s' = 0 := by
      unfold OOt FundOf; rw [dite_eq_right hE]; exact OO_empty _ _ _ _
    have h2 : OOt s = 0 := by
      unfold OOt FundOf; rw [dite_eq_right hE0]; exact OO_empty _ _ _ _
    refine ⟨1, LinearIsometryEquiv.refl ℂ _, norm_one, ?_⟩
    rw [h1, h2]
    simp

theorem ampCov_of (hR : RatPt) (hC : ChiTrivialC) (Y : Full X) : AmpCov Y := by
  intro u u' t s s'
  have h : s.1.toTerm = s'.1.toTerm := s.2.trans s'.2.symm
  obtain ⟨b, U, hb, hO⟩ := oot_cov hR hC h
  unfold amp ampN
  refine ⟨_, U, ?_, smul_cov _ _ _ b (norm_chiN _) (OOt s.1) (OOt s'.1) (cl U) hO⟩
  exact norm_cov _ _ b (norm_chiN _) (norm_chiN _) hb

end Amp

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ker

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem mem_orth_iff {U : Submodule D.host.E (VS D).V} {x : (VS D).V} : x ∈ orth (VS D) U ↔ x ∈ perpS (VS D) U := by
  unfold orth perpS
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  first
    | exact Iff.rfl
    | (constructor <;> intro h <;> exact h)

theorem act_of_dec (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (q : {Λ // Λ ∈ Y.what₂ u'})
    {s s' : _root_.Formalism.L2.SG.PackageTie2.TT Y u u'} (hq : s.lam' = q.1) (hl : s.lam = s'.lam) (hl' : s.lam' = s'.lam')
    {n ν c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam s.lam (lf D (X.Fu u)))
    (hν : ν ∈ NLam s.lam' (lf D (X.Fu u'))) (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hg : Formalism.HermitianLatticesTheory.gmap c s.lam' = s.lam') (hfix : ∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a)
    (he : s'.lin = n * s.lin * ν * c) :
    ∃ γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q, s' = act Y q γ s ∧
      ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - (Formalism.L2.SG.Pf.Act.isoG γ.1)⁻¹ y ∈ (X.Fu u').X := by
  obtain ⟨Λ', hΛ'⟩ := q
  simp only at hq
  subst hq
  have hst := Formalism.L2.SG.Pf.FibreCounting.stabF_of_fix (X.Fu u') hc hfix
  obtain ⟨g, hgq⟩ := (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s.lam', hΛ'⟩).2
    ⟨Formalism.L2.SG.Pf.Act.indW c hst, Formalism.L2.SG.Pf.Act.indW_mem s.lam' c hst hg⟩
  have hW : (Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) (Formalism.L2.SG.Pf.Act.isoG_stab g.1) :
      Formalism.MainNotions.S.WbQ D (X.Fu u') → Formalism.MainNotions.S.WbQ D (X.Fu u')) = Formalism.L2.SG.Pf.Act.indW c hst :=
    congrArg Subtype.val hgq
  have hq : ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - Formalism.L2.SG.Pf.Act.isoG g.1 y ∈ (X.Fu u').X := by
    intro y hy
    have e := congrFun hW.symm (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [Formalism.L2.SG.Pf.Act.indW_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq] at e
    simpa using e
  have hfixg : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [FlagG.fvec, Fin.snoc_last]
      rw [X.flagZVector u']
      exact Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)
    · simp only [FlagG.fvec, Fin.snoc_castSucc]
      rw [X.Fu_e u']
      exact Formalism.L2.SG.Pf.Act.isoG_e g.1 i
  have hA : IsAutLam (VS D) s.lam' c := ⟨hc, hg⟩
  have hA' : IsAutLam (VS D) s.lam' (Formalism.L2.SG.Pf.Act.isoG g.1) :=
    ⟨(Formalism.L2.SG.Pf.Act.isoG_stab g.1).1, Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s.lam', hΛ'⟩ g⟩
  have hm := Formalism.L2.SG.Pf.FibreCounting.nlam_of_sub (X.Fu u') hA hA' hfix hfixg hq
  have hkinv : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' g.1⁻¹ * (Y.cs u').h ((Y.cs u').base s.lam'))
      ∈ X.B.I.Kset := by
    rw [← Formalism.L2.SG.Pf.Act.aK_eq]
    have h1 := K_inv X.B.I (kB_mem (Y := Y) ⟨s.lam', hΛ'⟩ g)
    unfold Formalism.L2.SG.Pf.SatGramActL.kB at h1
    rw [map_inv]
    convert h1 using 1
    push_cast
    group
  let γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', hΛ'⟩ := ⟨g.1⁻¹, hkinv⟩
  have hxg := (isoG_lift Y ⟨s.lam', hΛ'⟩ g).1
  have hxi : RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := by
    have := Formalism.L2.SG.Pf.ratLink_inv X hxg
    simpa [γ] using this
  have hiso : Formalism.L2.SG.Pf.Act.isoG γ.1 = (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := (eq_isoG hxi).symm
  refine ⟨γ, ?_, fun y hy => by rw [hiso, inv_inv]; exact hq y hy⟩
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) :=
    (isoG_lift Y ⟨s.lam', hΛ'⟩ γ).2
  have hcls := Formalism.L2.SG.Pf.SatGramActR.tmap_cls (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
    Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', hΛ'⟩ γ).1 s hβt
  set G := Formalism.L2.SG.Pf.Act.isoG g.1 with hG
  have hGA : G⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) := by rw [← hiso]; exact hβt
  have hν2 : G⁻¹ * ν * G⁻¹⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.SatGramActL.nlam_conj hGA hν
  have hν3 : (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.nlamPf_mul hν2 (Formalism.L2.SG.Pf.nlamPf_inv hm)
  rcases s' with ⟨k, hk, k', hk', q'⟩
  simp only at hl hl' he
  subst hl hl'
  show (⟨s.lam, hk, s.lam', hk', q'⟩ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') =
    ⟨s.lam, s.mem, s.lam', s.mem', (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
      Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', hΛ'⟩ γ).1 s).cls⟩
  rw [hcls]
  congr 1
  rw [← Quot.out_eq q']
  refine (Quot.sound ⟨n, hn, (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹, hν3, ?_⟩).symm
  show GTerm.lin (⟨s.lam, hk, s.lam', hk', q'⟩ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') =
    n * (GTerm.lin s * (Formalism.L2.SG.Pf.Act.isoG γ.1)⁻¹) * ((G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹)
  rw [he, hiso]
  group

theorem nlam_frame (s : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hm : m ∈ NLam s.lam s.frame) :
    s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) := by
  have hm' : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap s.lin s.lam')
      (Formalism.L2.SG.Saturated.mapL s.lin (Formalism.L2.SG.Pf.FibreCounting.lin_isom s) (lf D (X.Fu u'))) := by
    rw [Formalism.L2.SG.Pf.FibreCounting.lin_gmap s, ← Formalism.L2.SG.Pf.FibreCounting.frame_eq s]; exact hm
  exact (Formalism.L2.SG.Pf.mem_NLam_map _ (Formalism.L2.SG.Pf.FibreCounting.lin_isom s) s.lam' (lf D (X.Fu u')) m).1 hm'

theorem fix_of_ez {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (he : ∀ a, c ((X.Fu u').e a) = (X.Fu u').e a)
    (hz : c (X.Fu u').z = (X.Fu u').z) : ∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
  intro a
  unfold Formalism.MainNotions.S.FlagG.fvec
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Fin.snoc_last]
    exact hz
  · simp only [Fin.snoc_castSucc]
    exact he i

theorem iotaKer_core (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC)
    (s₁ s₂ t₁ t₂ : _root_.Formalism.L2.SG.PackageTie2.TT Y u u') (n₁ n₂ m₁ m₂ c₁ c₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hs2 : s₂.lam = s₁.lam) (ht1 : t₁.lam = s₁.lam) (ht2 : t₂.lam = s₁.lam)
    (hs2' : s₂.lam' = s₁.lam') (ht1' : t₁.lam' = s₁.lam') (ht2' : t₂.lam' = s₁.lam')
    (hn₁ : n₁ ∈ NLam s₁.lam (lf D (X.Fu u))) (hn₂ : n₂ ∈ NLam s₁.lam (lf D (X.Fu u)))
    (hm₁ : m₁ ∈ NLam s₁.lam s₁.frame) (hm₂ : m₂ ∈ NLam s₁.lam s₂.frame)
    (hc₁ : c₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hc₂ : c₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hg₁ : Formalism.HermitianLatticesTheory.gmap c₁ s₁.lam' = s₁.lam') (hg₂ : Formalism.HermitianLatticesTheory.gmap c₂ s₁.lam' = s₁.lam')
    (he₁ : ∀ a, c₁ ((X.Fu u').e a) = (X.Fu u').e a) (he₂ : ∀ a, c₂ ((X.Fu u').e a) = (X.Fu u').e a)
    (hz₁ : c₁ (X.Fu u').z = (X.Fu u').z) (hz₂ : c₂ (X.Fu u').z = (X.Fu u').z)
    (hl₁ : t₁.lin = n₁ * m₁ * s₁.lin * c₁) (hl₂ : t₂.lin = n₂ * m₂ * s₂.lin * c₂)
    (hι : iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂)
    (hι' : iotaOf Y.TR (Y.cs u) (Y.cs u') t₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') t₂) :
    ∀ x ∈ orth (VS D) (X.Fu u').X, (c₂ * c₁⁻¹) x - x ∈ (X.Fu u').X := by
  let q : {Λ // Λ ∈ Y.what₂ u'} := ⟨s₁.lam', s₁.mem'⟩
  have hfix₁ := fix_of_ez he₁ hz₁
  have hfix₂ := fix_of_ez he₂ hz₂
  have hμ₁ := nlam_frame s₁ hm₁
  have hm₂' : m₂ ∈ NLam s₂.lam s₂.frame := by rw [hs2]; exact hm₂
  have hμ₂ := nlam_frame s₂ hm₂'
  have e₁ : t₁.lin = n₁ * s₁.lin * (s₁.lin⁻¹ * m₁ * s₁.lin) * c₁ := by rw [hl₁]; group
  have e₂ : t₂.lin = n₂ * s₂.lin * (s₂.lin⁻¹ * m₂ * s₂.lin) * c₂ := by rw [hl₂]; group
  have hn₂' : n₂ ∈ NLam s₂.lam (lf D (X.Fu u)) := by rw [hs2]; exact hn₂
  have hg₂' : Formalism.HermitianLatticesTheory.gmap c₂ s₂.lam' = s₂.lam' := by rw [hs2']; exact hg₂
  obtain ⟨γ₁, hγ₁, hq₁⟩ := act_of_dec hN q rfl ht1.symm ht1'.symm hn₁ hμ₁ hc₁ hg₁ hfix₁ e₁
  obtain ⟨γ₂, hγ₂, hq₂⟩ := act_of_dec hN q hs2' (hs2.trans ht2.symm) (hs2'.trans ht2'.symm) hn₂' hμ₂ hc₂ hg₂'
    hfix₂ e₂
  have i₁ := iota_act hIR q γ₁ s₁ rfl
  have i₂ := iota_act hIR q γ₂ s₂ hs2'
  rw [← hγ₁] at i₁
  rw [← hγ₂] at i₂
  rw [i₁, i₂, hι] at hι'
  have hlev : levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ₁.1) =
      levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ₂.1) := inv_injective (mul_left_cancel hι')
  have hγ : γ₁ = γ₂ := by
    apply (Formalism.L2.SG.Pf.Act.gamL_levi_bij (Y.cs u') Y.TR Y.hK hN q).1
    apply Subtype.ext
    show levi Y.TR (colD ((Y.cs u').h ((Y.cs u').base q.1)) (iotaF X u' γ₁.1 * (Y.cs u').h ((Y.cs u').base q.1))) =
      levi Y.TR (colD ((Y.cs u').h ((Y.cs u').base q.1)) (iotaF X u' γ₂.1 * (Y.cs u').h ((Y.cs u').base q.1)))
    rw [← Formalism.L2.SG.Pf.Act.aK_eq, ← Formalism.L2.SG.Pf.Act.aK_eq]
    exact hlev
  subst hγ
  intro x hx
  rw [mem_orth_iff] at hx
  have hinv := Formalism.L2.SG.Pf.FibreCounting.inv_fix (X.Fu u') hfix₁
  have hc₁i : c₁⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.inv_mem _ hc₁
  have hy : c₁⁻¹ x ∈ perpS (VS D) (X.Fu u').X := Formalism.L2.SG.Pf.FibreCounting.perp_maps (X.Fu u') hc₁i hinv x hx
  have d₁ := hq₁ _ hy
  have d₂ := hq₂ _ hy
  have e3 : (c₂ * c₁⁻¹) x - x = (c₂ (c₁⁻¹ x) - (Formalism.L2.SG.Pf.Act.isoG γ₁.1)⁻¹ (c₁⁻¹ x)) -
      (c₁ (c₁⁻¹ x) - (Formalism.L2.SG.Pf.Act.isoG γ₁.1)⁻¹ (c₁⁻¹ x)) := by
    simp only [LinearEquiv.mul_apply]
    have : c₁ (c₁⁻¹ x) = x := by
      show c₁ (c₁.symm x) = x
      exact c₁.apply_symm_apply x
    rw [this]; abel
  rw [e3]
  exact sub_mem d₂ d₁

end Ker

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end
