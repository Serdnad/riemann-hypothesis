module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WeilJacquetShalikaLaw
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CubicPeriodConstant
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralVecSmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableInnerIBlkU
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

section PK7

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.UG Formalism.L2.Host

theorem local_unramified_of : JacquetShalikaLocal.L7 → JacquetShalikaLocal.lift_levelP_alt₂ → jumpWindows.G0 → jumpWindows.G5 → K7 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc
  refine ⟨WeilJacquetShalikaLaw.psiW ψ w, WeilJacquetShalikaLaw.psiOK hψ hc, fun y => rfl, ?_⟩
  intro z φ hφ hsat h hh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · have h0 : ∀ g, Wh ψ (0 : XB E a) g = 0 := fun g => by
      obtain ⟨Λ, hΛ'⟩ := hΛ g
      rw [← hΛ' 0 hφ, map_zero]
    rw [h0, h0, zero_mul]
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w (n := a), Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = Wh ψ φ h := by
    change Wh ψ φ (h * fl a w 1) = _
    rw [map_one, mul_one]
  by_cases h0 : vs = 0
  · have e : ∀ x, (vs : GL (Fin a) (w.adicCompletion E) → ℂ) x = 0 := fun x =>
      congrFun (congrArg Subtype.val h0) x
    have e1 : Wh ψ φ (h * fl a w u) = 0 := e u
    rw [e1, ← hv1, e 1, zero_mul]
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w (n := a),
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w (n := a))
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1] at this
  exact this

end PK7

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace BlockInfGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem blk_infGL {j : ℕ} {c : GL (Fin k) (Cinf E)} (hc : GlobalTheory j c) : GlobalTheory j (infGL E k c) := fun i l hil => by
  change (cornerGL k (sInf E) c).val i l = _
  rw [GlobalTheory.CuspRep.cornerGL_apply_loctri, hc i l hil, sub_add_cancel]

end BlockInfGL

open BlockInfGL jumpWindows.CharacterNondegenerate in
theorem infinite_place_step_of : jumpWindows.S7 → jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → jumpWindows.G5 → jumpWindows.G5b → P2 → InfinitePlaceStep := by
  intro hS7 hS10 hG0 hG5 _ hP2 E _ _ _ k wt ρ J hW ψ hψ S Y hY n m hn _ U hU x C hxY hsm hlev hBump
  obtain ⟨hcI, hcLI, hcIf, -, -, -, hcomm, -, hb, -, -, -, -, -, hcontI⟩ := hG0 E k
  obtain ⟨hΛ, hRt, hGood, hlaw⟩ := hG5 E k ψ hψ
  obtain ⟨hdec, -, -, hBlk1, -⟩ := hS10 (Cinf E) k (n + 1)
  obtain ⟨hP2u, -, hU01, hPre0, -, hGP, -⟩ := hP2 E k ψ hψ
  obtain ⟨hCc, hCS, ⟨t₀, ht₀, hW1⟩, hB⟩ := hBump
  have hU' : infGL E k ⁻¹' U ∈ 𝓝 (1 : GL (Fin k) (Cinf E)) :=
    hcontI.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)
  obtain ⟨η, r, hη1, hr1, hmir, hnn, ⟨C', hC'c, hC'U, hC'B, hC'd⟩, hv⟩ :=
    hS7 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly n hn (chi ψ)
      (continuous_chi hψ) (fun z => hψ.norm _) (chi_nondeg hψ) _ hU'
  obtain ⟨x', hsm', hvP⟩ := hv x hsm

  let ZY : Submodule ℂ (XB E k) := Submodule.comap (J : XB E k →ₗ[ℂ] XB E k) Y
  have hZYc : IsClosed (ZY : Set (XB E k)) := hY.closed.preimage J.continuous
  have hZYi : ∀ g, ∀ y ∈ ZY, (ρ.comp (infGL E k)) g y ∈ ZY := by
    intro g y hy
    show J (ρ (infGL E k g) y) ∈ Y
    rw [hW.inter]
    exact hY.stable _ (fun w _ => hcLI w g) _ hy
  obtain ⟨hx'Y, hvΛ⟩ := hvP ZY hZYc hZYi hxY
  have whB : ∀ φ : XB E k, Good ψ (k - 1) φ → ∀ (y : UnipotentBlockColumnIndex k (n + 1) (n + 1) → Cinf E) (g : GA E k),
      Wh ψ φ (infGL E k (blkU y) * g) = chi ψ (lastE (n + 1) y) * Wh ψ φ g := by
    intro φ hφ y g
    rw [hb, chi_apply, sInf_lastE]
    exact (hlaw φ hφ).2.2 (n + 1) n.succ_pos _ g
  have lawOf : ∀ g' : GA E k, cInf g' = 1 → ∀ Λ : XB E k →L[ℂ] ℂ,
      (∀ φ : XB E k, Good ψ (k - 1) φ → Λ φ = Wh ψ φ g') →
      ∀ y ∈ ZY, ∀ y' : UnipotentBlockColumnIndex k (n + 1) (n + 1) → Cinf E,
        (Λ.comp J) ((ρ.comp (infGL E k)) (blkU y') y) = chi ψ (lastE (n + 1) y') * (Λ.comp J) y := by
    intro g' hg' Λ hΛg y hy y'
    have hy' : Good ψ (k - 1) (J y) := hY.good _ hy
    change Λ (J (ρ (infGL E k (blkU y')) y)) = _ * Λ (J y)
    rw [hW.inter, hΛg _ (hGood _ _ hy'), hΛg _ hy', hRt, hcomm g' hg', whB _ hy']
  have conv : ∀ (g' : GA E k) (Λ : XB E k →L[ℂ] ℂ), (∀ φ : XB E k, Good ψ (k - 1) φ → Λ φ = Wh ψ φ g') →
      ∀ v : XB E k, J v ∈ Y → ∀ h, (Λ.comp J) ((ρ.comp (infGL E k)) h v) = Wh ψ (J v) (g' * infGL E k h) := by
    intro g' Λ hΛg v hv h
    change Λ (J (ρ (infGL E k h) v)) = _
    rw [hW.inter, hΛg _ (hGood _ _ (hY.good _ hv)), hRt]
  have goodx : Good ψ (k - 1) (J x) := hY.good _ hxY
  have goodx' : Good ψ (k - 1) (J x') := hY.good _ hx'Y
  have hW10 : Wh ψ (J x) 1 ≠ 0 := by rw [hW1]; exact Complex.ofReal_ne_zero.2 ht₀.ne'
  have pre0 : Pre ψ 0 (whit ψ (k - 1) (J x)) := hPre0 (k - 1) (by omega) _ (hGP (k - 1) _ goodx)
  have law0 : ∀ u, UU 0 u → ∀ g, Wh ψ (J x) (u * g) = psN ψ u * Wh ψ (J x) g :=
    fun u hu g => hP2u 0 _ pre0 u (hU01 u hu) g
  refine ⟨x', infGL E k '' C', ?_, hx'Y, hsm', ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hC'U hc
  ·
    intro w hw
    refine Filter.mem_of_superset (hlev w hw) fun u hu => ?_
    have hu' : Rt E k (fl k w u) (J x) = J x := hu
    let T : XB E k →L[ℂ] XB E k := (Rt E k (fl k w u)).comp J - J
    have key : ∀ y, T y = 0 ↔ Rt E k (fl k w u) (J y) = J y := fun y => by simp [T, sub_eq_zero]
    have hk := (hvP (LinearMap.ker (T : XB E k →ₗ[ℂ] XB E k)) T.isClosed_ker (fun g y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        refine (key _).2 ?_
        have hy' := (key y).1 hy
        have hc : ∀ φ : XB E k, Rt E k (fl k w u) (Rt E k (infGL E k g) φ) =
            Rt E k (infGL E k g) (Rt E k (fl k w u) φ) := fun φ => by
          rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm _ (hcIf w u), map_mul,
            ContinuousLinearMap.mul_apply]
        show Rt E k (fl k w u) (J (ρ (infGL E k g) y)) = J (ρ (infGL E k g) y)
        rw [hW.inter, hc, hy'])
      (LinearMap.mem_ker.2 ((key x).2 hu'))).1
    rw [LinearMap.mem_ker] at hk
    exact (key x').1 hk
  · rintro _ ⟨c, hc, rfl⟩
    exact blk_infGL (hC'B c hc)
  refine ⟨hCc.mul (hC'c.image hcontI), ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, _, ⟨c, _, rfl⟩, rfl⟩ w hw
    rw [map_mul, hcLI, mul_one]
    exact hCS a ha w hw
  · obtain ⟨Λ₁, hΛ₁⟩ := hΛ 1
    have e1 := hvΛ (Λ₁.comp J) (lawOf 1 (map_one _) Λ₁ hΛ₁) 1 hBlk1
    rw [conv 1 Λ₁ hΛ₁ x' hx'Y, conv 1 Λ₁ hΛ₁ x hxY, hr1, map_one, one_mul] at e1
    obtain ⟨s, hs, hηs⟩ := hnn 1
    have hs' : 0 < s := lt_of_le_of_ne hs fun h0 => hη1 (by rw [hηs, ← h0, Complex.ofReal_zero])
    exact ⟨s * t₀, mul_pos hs' ht₀, by rw [e1, hηs, hW1, Complex.ofReal_mul]⟩
  · intro g hg hWg
    obtain ⟨hgI, hgL⟩ := hg
    obtain ⟨y, h, hh, hyh⟩ := hdec (cInf g) hgI
    obtain ⟨g', hg'⟩ : ∃ g' : GA E k, g' = (infGL E k (cInf g))⁻¹ * g := ⟨_, rfl⟩
    have hg'1 : cInf g' = 1 := by rw [hg', map_mul, map_inv, hcI, inv_mul_cancel]
    have hgeq : g = infGL E k (blkU y) * (g' * infGL E k h) := by
      rw [hcomm g' hg'1 h, ← mul_assoc, ← map_mul, ← hyh, hg', mul_inv_cancel_left]
    obtain ⟨Λ, hΛg⟩ := hΛ g'
    have e := hvΛ (Λ.comp J) (lawOf g' hg'1 Λ hΛg) h hh
    rw [conv g' Λ hΛg x' hx'Y, conv g' Λ hΛg x hxY] at e
    have hWg' : Wh ψ (J x') g = chi ψ (lastE (n + 1) y) * (η h * Wh ψ (J x) (g' * infGL E k (r h))) := by
      rw [hgeq, whB _ goodx', e]
    rw [hWg'] at hWg ⊢
    have hη : η h ≠ 0 := fun h0 => hWg (by rw [h0, zero_mul, mul_zero])
    have hW0 : Wh ψ (J x) (g' * infGL E k (r h)) ≠ 0 := fun h0 => hWg (by rw [h0, mul_zero, mul_zero])
    obtain ⟨c, hc, hhc⟩ := hC'd h hh hη
    obtain ⟨s, hs, hηs⟩ := hnn h
    have hOm : Om n m (g' * infGL E k (r h)) := by
      refine ⟨?_, fun w => ?_⟩
      · rw [map_mul, hg'1, one_mul, hcI]
        exact hmir h hh hη
      · rw [map_mul, hcLI, mul_one, hg', map_mul, map_inv, hcLI, inv_one, one_mul]
        exact hgL w
    obtain ⟨n₀, c₁, hc₁, t₁, hn₀, hn₀S, heq₀, ht₁, hWeq⟩ := hB _ hOm hW0
    have huu : UU 0 (infGL E k (blkU y) * n₀) := cubicPeriodConstant.unipotent_zero_mul (by rw [hb]; exact cubicPeriodConstant.blkU_unipotent_zero _) hn₀
    have hpsN : psN ψ (infGL E k (blkU y) * n₀) = chi ψ (lastE (n + 1) y) * psN ψ n₀ := by
      have e1 := law0 _ huu 1
      have e2 := law0 n₀ hn₀ 1
      have e3 := whB (J x) goodx y n₀
      rw [mul_one] at e1 e2
      rw [e1, e2] at e3
      exact mul_right_cancel₀ hW10 (by rw [e3, mul_assoc])
    have hih : infGL E k h = infGL E k (r h) * infGL E k c := by rw [← map_mul, ← hhc]
    refine ⟨infGL E k (blkU y) * n₀, c₁ * infGL E k c, Set.mem_image2_of_mem hc₁ (Set.mem_image_of_mem _ hc),
      s * t₁, huu, fun w hw => ?_, ?_, mul_nonneg hs ht₁, ?_⟩
    · rw [map_mul, hcLI, one_mul]
      exact hn₀S w hw
    · rw [hgeq, hih, ← mul_assoc g', heq₀]
      simp only [mul_assoc]
    · rw [hWeq, hηs, hpsN]
      push_cast
      ring

end PositivityTheory.AdelicQuotientData

end
end

section

namespace PositivityTheory.AdelicQuotientData

theorem nm_agrees_with_twisted_norm_sigmaGL : D0 → jumpWindows.G0 → N2 := @GlobalTheory.CompanionTheory.UnipotentNormalizer.main

end PositivityTheory.AdelicQuotientData
end

section

namespace PositivityTheory.AdelicQuotientData

theorem one_more_column_of : D0 → N0 → N1 → N3 → ColumnConjugationMeasure → OneMoreAdelicColumn := @GlobalTheory.CompanionTheory.RS.ColN.one_more_column

end PositivityTheory.AdelicQuotientData
end
