module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle739
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle909
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle926
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle777
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle529
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle918
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle890
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle894
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle394
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle939
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle509
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle892
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle763
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwLevPow

theorem val_pow {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (a : ℕ) (v) :
    (χ ^ a).val v = χ.val v ^ a :=
  GlobalTheory.ConjExt.locK_pow χ a v _

theorem twLev_pow : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → ∀ a b : ℕ, (χ ^ a) ^ b = χ →
      GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ ^ a) (xi ^ a) Q (fun PP => xiR PP ^ a) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC χ xi Q xiR h a b hab

  have hQ0 : ∀ PP, PP ∉ R.Q A.μ0 := fun PP hPP =>
    ((hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP)) (by rw [hC.lev.xi_base]; intro x _; rfl)
  refine
    { xi := GlobalTheory.ConjExt.chrEq_pow h.xi a
      xi_fin := ?_
      xi_triv := GlobalTheory.ConjExt.trivOn_pow h.xi_triv a
      xi_tame := fun v x h1 h2 => by
        rw [GlobalTheory.ConjExt.loc_pow, h.xi_tame v x h1 h2, one_pow]
      Q_pl := h.Q_pl
      Q_off := h.Q_off
      Q_de := h.Q_de
      Q_ram := fun PP => Iff.trans
        (not_congr ⟨fun hu => hab ▸ GlobalTheory.ConjExt.unrAt_pow hu b, fun hu => GlobalTheory.ConjExt.unrAt_pow hu a⟩) (h.Q_ram PP)
      xiR := fun PP hP c k u h1 h2 => by
        show (xiR PP ^ a) u = (χ ^ a).locK PP k
        rw [GlobalTheory.ConjExt.locK_pow, MonoidHom.pow_apply, h.xiR PP hP c k u h1 h2]
      roots := h.roots
      muVal := ?_
      half := h.half
      guard := h.guard }
  · obtain ⟨n, hn, ho⟩ := h.xi_fin
    refine ⟨n, hn, ?_⟩
    show (χ ^ a) ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, show χ ^ n = 1 from ho, one_pow]
  · intro i P hP
    obtain ⟨x, hx⟩ := h.muVal i P hP
    have hP0 : Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q A.μ0 : Set (Pl D.host.E))) := by
      refine ⟨hP.1, fun hm => ?_, fun Q' hQ' => ?_⟩
      · rcases hm with hm | hm
        · exact hP.2.1 (Or.inl hm)
        · exact hQ0 _ hm
      · rcases hQ' with hQ' | hQ'
        · exact hP.2.2 Q' (Or.inl hQ')
        · exact absurd hQ' (hQ0 _)
    obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
    have hy := hC.fam.muVal i A.μ0 P ((ht.ok A.μ0 P).2 hP0)
    rw [hC.lev.xi_base, mul_one] at hy
    set y : D.what₂.LLˣ := A.muVal i A.μ0 P
    refine ⟨y * (y⁻¹ * x) ^ a, ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, map_mul, map_pow, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hx, hy, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_mul, val_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [inv_mul_cancel_left₀ (Units.ne_zero _)]

end GlobalTheory.TwLevPow
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSCell

theorem exists_isUnifV : ∀ (E : Type) [Field E] [NumberField E], ∃ ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ, ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E) := by
  intro E _ _
  refine ⟨fun w => GroundTheory.Global.uniformizerUnit w, fun w => ?_⟩
  have h := GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  rw [zpow_one] at h
  exact h



theorem lintegral_unfolded_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (ℓ : ℕ) + 1 = a ∧
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E a)), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit φ.1) (GlobalTheory.JSW.whit φ.1) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
            ENNReal.ofReal (H x) * GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, π₀, ω, hα, hmk, hωu, hω, hπ₀, hsat⟩ := GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary E (m + 1) π hπ T hT
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV E
  obtain ⟨F, hF, l₀, hl₀, ⟨U, hUo, hU⟩, hK, hW0, ⟨C, hC, hCp⟩, hprof⟩ := GlobalTheory.T.exists_shifted_vector_shintani_formula_ramified E m T π₀ hπ₀ α hsat ϖ hϖ
  have hSm : F ∈ Sm E (m + 1) := (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ₀ hF : GlobalTheory.MSpanDecay.Good F).mem_Sm
  let φ : Sm E (m + 1) := ⟨F, hSm⟩
  have hFc : Continuous F := by
    refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E (m + 1) φ
      (GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hUo.mem_nhds U.one_mem) fun k hk => ?_))
    exact Subtype.ext (funext fun g => hU k hk g)
  obtain ⟨hWc, hWN⟩ := GlobalTheory.T.globalWhittakerCoefficient_continuous_norm_invariant E (m + 1) F hFc (GlobalTheory.T.cuspFormRapidKernelSmoothSpan_left_invariant E (m + 1) π₀ F hF)
  obtain ⟨Φ, J, hΦs, hΦc, hΦr, hΦreal, hΦ1, hJ0, horb⟩ := GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit E (m + 1) (Fin.last m) T U hUo
  have hWU : ∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g := fun u hu g => by
    rw [GlobalTheory.JSW.whit_mul_right]
    exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hU u hu z)
  have hWK : ∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g :=
    fun k hk h1 h2 g => by
      rw [GlobalTheory.JSW.whit_mul_right]
      exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hK k hk h1 h2 z)
  let αc : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ := fun w i => ((α w i : ℂˣ) : ℂ)
  have hpw := GlobalTheory.T.cell_identity_rankinSelberg_torus_translate E m T ϖ hϖ αc F l₀ U Φ J hl₀ hWU hWK hWN hprof hΦr hJ0
    (fun y hy => (horb y hy).imp fun κ hκ => ⟨hκ.1, hκ.2.2⟩)
  obtain ⟨K, hKc, hKp⟩ := GlobalTheory.T.cell_decomposition_lattice_integral_unfolding E m T ϖ hϖ F l₀ U Φ J C hC hl₀ hWU hWK hWN hCp hΦc hΦr hJ0 horb
  obtain ⟨hBc, hBN, hBtop⟩ := GlobalTheory.T.unfoldedRankinSelbergIntegrand_continuous_invariant E (m + 1) (Fin.last m) (by simp) F Φ J (Pi.single (Fin.last m) 1) hWc hWN
    hΦs.continuous hΦr
  have hΦ1' : Φ (Pi.single (Fin.last m) 1) ≠ 0 := fun h => by rw [h] at hΦ1; simp at hΦ1
  have hone := GlobalTheory.T.unfoldedRankinSelbergIntegrand_ne_zero_identity E m T ϖ F Φ J l₀ hl₀ hW0 hΦ1'
  refine ⟨α, Fin.last m, Φ, J, Pi.single (Fin.last m) 1, π₀, ω, φ, by simp, hα, hmk, hωu, hω, Or.inr hF, ?_, hΦs,
    hΦc, hΦr, hΦreal, fun h => hΦ1' (congrFun h _), ?_⟩
  · intro h
    apply hW0
    have e : F = 0 := congrArg Subtype.val h
    rw [e]
    simp [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  intro μ _ 𝓕₀ h𝓕

  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → GA E (m + 1) → ℝ, B = fun x g =>
      (GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g)).toReal :=
    ⟨_, rfl⟩
  have hB1 : Continuous (Function.uncurry B) := by
    have h1 : Continuous fun p : ℝ × GA E (m + 1) => (p.1, GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) :=
      continuous_fst.prodMk (continuous_const.mul continuous_snd)
    have h2' := hBc.comp h1
    have h2 : Continuous fun p : ℝ × GA E (m + 1) => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) p.1
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) := h2'
    have h3 := ENNReal.continuousOn_toReal.comp_continuous h2 fun p => hBtop _ _
    subst hBdef
    exact h3
  have hBg : ∀ (x : ℝ) (h : GA E (m + 1) → GA E (m + 1)), Continuous h →
      Continuous fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (h g) := by
    intro x h hh
    have h2 := hBc.comp (continuous_const.prodMk hh : Continuous fun g => (x, h g))
    exact h2
  have hB2 : ∀ x g, 0 ≤ B x g := fun _ _ => by rw [hBdef]; exact ENNReal.toReal_nonneg
  have hB3 : ∀ x, 0 < B x 1 := fun x => by
    rw [hBdef]
    refine ENNReal.toReal_pos ?_ (hBtop _ _)
    rw [mul_one]
    exact hone x
  have hB4 : ∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B x (u * g) = B x g := fun x u hu g => by
    rw [hBdef]
    beta_reduce
    have e : GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * (u * g) =
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * u * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1)⁻¹) * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) := by
      group
    rw [e, hBN x _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu)]
  have hB5 : ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ x g, g ∈ GlobalTheory.CellDec.C0 E (m + 1) T → B x g ≠ 0 →
      ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K :=
    ⟨K, hKc, fun x g hg h => hKp x g hg fun h0 => h (by rw [hBdef]; simp only; rw [h0]; rfl)⟩
  obtain ⟨hI, hIc⟩ := GlobalTheory.T.lintegral_unipotentCell_pos_lt_top_continuous E (m + 1) μ T 𝓕₀ h𝓕 B hB1 hB2 hB3 hB4 hB5
  have hd : 0 < GlobalTheory.CellDec.dinv (m + 1) l₀.1 := by
    unfold GlobalTheory.CellDec.dinv
    refine Finset.prod_pos fun w _ => zpow_pos ?_ _
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    unfold Formalism.UG.qV
    exact_mod_cast (zero_lt_one.trans this)

  have key : ∀ x : ℝ, ∫⁻ g in 𝓕₀, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g ∂μ =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) αc x *
        (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ) := by
    intro x
    have hmeas : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, Measurable fun g =>
        GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) := fun l =>
      (hBg x _ (continuous_const.mul continuous_id)).measurable
    have hnm : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T) μ :=
      h𝓕.nullMeasurableSet.inter (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) T).measurableSet.nullMeasurableSet
    have hmx : Measurable fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g :=
      (hBg x (fun g => g) continuous_id).measurable
    rw [GlobalTheory.CellDec.cell_lintegral μ T ϖ hϖ 𝓕₀ h𝓕 _ hmx
      (hBN x), ← GlobalTheory.T.tsum_schurSquareCellProduct_eq_eulerProduct E (m + 1) T αc x l₀, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun l => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have e1 : ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
          GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ENNReal.ofReal (B x g) * GlobalTheory.RSCell.cellProd T αc x (l.1 - l₀.1) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem₀ hnm] with g hg
      rw [hpw x g hg.2 l, hBdef, ENNReal.ofReal_toReal (hBtop _ _)]
    have hm2 : Measurable fun g => ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * ENNReal.ofReal (B x g) := by
      rw [hBdef]
      exact measurable_const.mul (ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp (hmeas l₀)))
    rw [e1, lintegral_mul_const _ hm2, mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
    ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal, ?_, ?_, fun x _ => ⟨?_, ?_⟩⟩
  · have e : (fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal) =
        fun x => GlobalTheory.CellDec.dinv (m + 1) l₀.1 * (∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal := by
      funext x
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le]
    rw [e]
    exact (continuous_const.mul hIc).continuousWithinAt
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI 1).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI 1).2.ne)
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI x).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne)
  · rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne), mul_comm]
    exact key x

end GlobalTheory.RSCell
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSbLayer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult




section Raw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_sb_raw (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (YS : NExpRealS Rl cG (ratDatR Rl cG kKs hk)) (H : NExpRealH Rl cG (ratDatR Rl cG kKs hk) YS)
    (hX : NExpHeckeRowX Rl cG _ YS H fun _ => LinearMap.id) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hne : Nonempty D.ntw.Tw)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) :
    ∃ Sb' : Finset (PlE D.host), Sb ⊆ Sb' ∧ (∀ i, Sb' ⊆ D.ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low D Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd Rl cG kKs hk Sb' H.hL := by
  classical
  obtain ⟨i₀⟩ := hne
  refine ⟨(D.ntw.S0 i₀).filter (fun P => ∀ i, P ∈ D.ntw.S0 i), fun P hP => Finset.mem_filter.2 ⟨hSb i₀ hP, fun i => hSb i hP⟩,
    fun i P hP => (Finset.mem_filter.1 hP).2 i, ?_, ?_⟩
  · intro P hP
    have hall : ∀ i, P ∈ D.ntw.S0 i := by
      intro i
      rw [Nat.cast_mul, Nat.cast_mul] at hP
      rcases P.isPrime.mem_or_mem hP with h | h
      · exact hS02 i h
      · rcases P.isPrime.mem_or_mem h with h | h
        · exact D.ntw.placesOver_subset_exceptional i 0 h
        · exact D.ntw.placesOver_subset_exceptional i 1 h
    exact Finset.mem_filter.2 ⟨hall i₀, hall⟩
  · intro j k P α Rr h1 h2 hd x
    have hi' : ∃ i', P ∉ D.ntw.S0 i' := by
      by_contra hc
      push_neg at hc
      exact hd.offS (Finset.mem_filter.2 ⟨hc i₀, hc⟩)
    obtain ⟨i', hi'⟩ := hi'
    obtain ⟨-, -, -, -, hso, -, -, -⟩ :=
      GlobalTheory.ConjPlaceOff.exists_conj_off D (D.ntw.S0 i') Rl.Sb P (hS0c i') (hS02 i') (hS0b i') hd.split hi'
    have hj : (idxOf D j : ℕ) + 1 = j := by simp only [idxOf]; omega
    let y : (ratDatR Rl cG kKs hk).WL ((idxOf D j : ℕ) + 1) := (YS.fi (idxOf D j)).e.symm x
    have hy : (YS.fi (idxOf D j)).e y = x := LinearEquiv.apply_symm_apply _ _
    have key : ∀ n (hn : n = j) (z : (ratDatR Rl cG kKs hk).WL n), HEq z x → HEq (H.hL n k P z) (H.hL j k P x) := by
      intro n hn z hz
      subst hn
      rw [eq_of_heq hz]
    have h3 : HEq ((YS.fi (idxOf D j)).e (H.hL ((idxOf D j : ℕ) + 1) k P y)) (H.hL j k P x) :=
      (hfi _ _).trans (key _ hj y ((hy ▸ hfi _ y).symm))
    have ht := hX.tie (idxOf D j) k P hd.split hso ⟨i', hi'⟩ hd.odd hd.le α Rr hd.elt hd.reps y rfl
    rw [eq_of_heq h3, hy] at ht
    exact ht

end Raw

end GlobalTheory.HeckeSbLayer

namespace GlobalTheory.HeckeSbLayer

end GlobalTheory.HeckeSbLayer

end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.ThetaSumDescent

theorem exists_cusp_thetaSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → l.A = 1 → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (T : Type) [Fintype T] (cs : T → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : T → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : T → MvPolynomial (LtN Dw n) c.F), Dom a n → LastPos Dw a → dδ.IsLev → dδ.l₂.A = 1 → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → SumInv dδ cs w P → ∃ f ∈ cusp Xo c U a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) ∧ ∀ f' ∈ sec Xo c a n, (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : T → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f' y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → f' = f := by
  intro E _ _ _ H Dw l Xo c r U hr hU hA _ a n N d La T _ cs e w P hD hL hlev hA₂ hnab hun hT hO he hcs hP hinv
  obtain ⟨f, hf, hval⟩ := exists_sec_thetaSum d hlev hnab La N hun hT hO a cs w P (fun t => (hcs t).1) hP hinv
  refine ⟨f, ?_, hval, fun f' hf' hval' => ?_⟩
  · rw [← Formalism.L2.PjFree.cusp_ofPj]
    exact mem_cusp_of_thetaSum d (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
      (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hU σ hσ)) hA hlev hA₂ hnab La N hun hT hO a hD hL cs e he w P hcs hP
      f hf hval
  · refine GlobalTheory.ClassSumUnique.sec_eq_of_geometric hf' hf fun k _ _ _ y => ?_
    letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
      show algebraMap c.F k (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    obtain ⟨y₂, hy⟩ := hlev.2.2.2.2.2.2.1 k hk y
    obtain ⟨v, hv, e₁⟩ := hval k hk y y₂ hy
    obtain ⟨v', hv', e₂⟩ := hval' k hk y y₂ hy
    rw [e₁, e₂]
    unfold thLaValAt at hv hv'
    exact sum_values_eq d.nab₂ hnab La N hun hT hO a _
      (fun t => (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP t)) _ _ 1 y₂ _ _ _ _ hv hv' fun _ _ => rfl

section Shift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A]

end Shift

section Marks

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {A : Type} [AddCommGroup A] [DecidableEq A]

end Marks

end GlobalTheory.ThetaSumDescent
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem GlobalTheory.InertiaEigenvalues.theoremT_all_records :
    GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal →
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  intro hBS hFon hBK hTD hEC D HW F Cm C hC
  exact GlobalTheory.T.liftingStep_theoremT_of_bhattScholze_fontaine (GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices hBS) hFon C hC D HW F (GlobalTheory.T.localLifting_admittedHypotheses_all hBK hTD hEC D HW F Cm)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.symplectic_pairing_half_lattices_eq_prod_primitive : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ x : WO S T, IsHalf (cA D e) x → IsIntM (frMapAdj S T βS βT x) → ∀ u : WO S T, IsHalf e u → IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → ψ (symplO S T x u) = ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (redM PP.1 (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) * redM PP.1 (frMapAdj S T βS βT x))) := by
  first | exact @GlobalTheory.FlatPairing.pairing_eq_prod | exact GlobalTheory.FlatPairing.pairing_eq_prod | (intros; apply GlobalTheory.FlatPairing.pairing_eq_prod <;> assumption)
end
