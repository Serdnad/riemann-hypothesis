module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle015
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.SplitROfSteps
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle004
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules


theorem modelqlink_pf : ModelQLinkStep := by
  intro D HW F Cm CA CB CK hA hML l hpf hl K LL hG π' E hR h' hh' T hT hJ c
  have hL := hML l hl K LL hG π' E hR h' hh' T hT hJ c
  obtain ⟨hL1, -, -, hL4, hL5, -, -⟩ := hL
  have h1 : adm1 D HW F Cm := hA.1
  have hs : 1 ≤ sK l K := by
    have := frobpin_sK_pos hl K LL hG
    omega
  obtain ⟨-, -, -, -, -, -, -, -, hπu, hπΔ, -⟩ := gradNPf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT hs
  obtain ⟨w₁, hw₁⟩ := hR.2.2.1
  obtain ⟨w₂, hw₂⟩ := hR.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨hcard, -, -⟩ := h9W T hT hs1 hp
  obtain ⟨-, ⟨π'₀, E₀, -, hm₀⟩, -⟩ := h9W T hT hs1 hp
  obtain ⟨r, b, hbΔ, hbu, hbe⟩ := hm₀.1
  haveI hdvr : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  obtain ⟨bL⟩ := MQ.basis_L ((HW l).W K 1 LL hG) T π' (sK l K) hs w₁ hw₁ hR.2.1 b hbΔ hbu hbe c
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hcpos : 0 < ((HW l).W K 1 LL hG).DelF.card := by
    refine Finset.card_pos.2 ⟨1, ((HW l).W K 1 LL hG).DelF_def 1 |>.2 ⟨1, one_pos, one_pow _⟩⟩
  have hclt : ((HW l).W K 1 LL hG).DelF.card < l := by
    rw [hcard, hpl]
    have := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hΔu : IsUnit ((((HW l).W K 1 LL hG).DelF.card : ℕ) : ↥(OL LL)) :=
    gradNPf_unit_nat ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hpf.out hlv _
      (Nat.not_dvd_of_pos_of_lt hcpos hclt)
  have hpP : ((D.loc l).PD K).p.Prime := by rw [hpl]; exact hpf.out
  haveI hcompl : IsAdicComplete (Ideal.span {(((D.loc l).PD K).p : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact FrobeniusSpanLemma.phib_OL_complete LL
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    show ∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π'
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply,
      show ((HW l).W K 1 LL hG).γ₀ δ (π' i) = π' i from congrFun (hπΔ δ hδ) i]
  have hEe : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' = ((w₂⁻¹ : (LetA ↥(OL LL) _)ˣ) : LetA ↥(OL LL) _) * ((HW l).W K 1 LL hG).q := by
    rw [hw₂, ← mul_assoc, Units.inv_mul, one_mul]
  have hEu : IsUnit (algebraMap _ ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
    rw [hEe, map_mul]
    exact ((w₂⁻¹).isUnit.map _).mul (MQ.q_unit ((HW l).W K 1 LL hG) hpP)
  obtain ⟨D', S, hdiv⟩ := MQ.div_at ((HW l).W K 1 LL hG) hpP (sK l K) h' π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') w₁ w₂ hw₁ hw₂
    hΔu.unit hΔu.unit_spec hR.1 hEΔ c
  have hp0 : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := by
    intro h0
    have : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (((D.loc l).PD K).p : ↥(OL LL))) = 1 := by
      rw [map_natCast, hpl]; exact hlv
    rw [h0, map_zero, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  have hpu : ¬ IsUnit (((D.loc l).PD K).p : ↥(OL LL)) := by
    intro hU
    obtain ⟨bb, hbb⟩ := hU.exists_right_inv
    have e := congrArg (fun z => (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 z)) hbb
    simp only [map_mul, map_one, AddValuation.map_mul, AddValuation.map_one] at e
    rw [map_natCast, hpl, hlv] at e
    have hb0 : 0 ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 bb) := (hRv _).2 ⟨bb, rfl⟩
    revert e hb0
    generalize (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 bb) = z
    intro e hb0
    induction z using WithTop.recTopCoe with
    | top => simp at e
    | coe q =>
      have e' : (1 + q : ℚ) = 0 := by exact_mod_cast e
      have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hb0
      linarith
  refine ⟨MQ.finite_of (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c hEu hL4
    (MQ.finite_L ((HW l).W K 1 LL hG) T π' (sK l K) hs w₁ hw₁ hR.2.1 b hbΔ hbu hbe c) D' S hdiv, ?_⟩
  exact MQ.tf_of (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c hπu hL1 hL5
    (MQ.sat_of π' c bL (MQ.hlet_of ((HW l).W K 1 LL hG) (sK l K) hs π' w₁ hw₁ hR.1 hπu c))
    (MQ.dvd_pow_of_dvr _ hp0 hpu)

end Formalism.MainNotions.N.Ln34
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

theorem modelF_local (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) (hM : 1 ≤ M)
    (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ) (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    {u u' : LetA O n} (hu' : u' ∈ W.AΔ) (huu : u' * u = 1) (hγE : W.γA W.gamK Eπ = u * Eπ)
    (h5a : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T)
    (hNP : ∀ y ∈ NcS W T c, y ∈ LamPS W T Eπ h' c) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1) (hexp : ExpansionFormLetter W T Pt) :
    ModelF W T Pt π' Eπ h' M c α β := by
  have F := hfr.1 T hcry hjmp

  have C1 : ∀ x hx, x ∈ NL W T Pt π' Eπ h' c →
      ∃ y hy, y ∈ NcS W T c ∧ α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy := by
    intro x hx hxNL
    induction hxNL using Submodule.span_induction with
    | mem x hxS =>
      obtain ⟨⟨y0, hy0⟩, hq⟩ := Submodule.Quotient.mk_surjective _ (α T ⟨x, hx⟩)
      have hα : α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y0 hy0 := hq.symm
      have hN := alpha_core W T Pt π' Eπ h' M σ c α β hfr hcry hjmp hs hww hQ h5a hp4 hpt hexp
        x hx hxS y0 hy0 hα
      obtain ⟨-, h2, h3⟩ := (mem_LamPS W T Eπ h' c y0).1 hy0
      exact ⟨y0, hy0, (mem_NcS W T c y0).2 ⟨hN, h2, h3⟩, hα⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
      have e : (⟨0, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = 0 := rfl
      rw [e, map_zero]
      exact (Submodule.Quotient.mk_zero _).symm
    | add x₁ x₂ h₁ h₂ ih₁ ih₂ =>
      have hx₁ := NL_le_LamLA W T π' Eπ h' c Pt h₁
      have hx₂ := NL_le_LamLA W T π' Eπ h' c Pt h₂
      obtain ⟨y₁, hy₁, hN₁, e₁⟩ := ih₁ hx₁
      obtain ⟨y₂, hy₂, hN₂, e₂⟩ := ih₂ hx₂
      refine ⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, Submodule.add_mem _ hN₁ hN₂, ?_⟩
      have e : (⟨x₁ + x₂, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩ := rfl
      rw [e, map_add (f := _), e₁, e₂]
      exact (Submodule.Quotient.mk_add _).symm
    | smul r x₁ h₁ ih₁ =>
      have hx₁ := NL_le_LamLA W T π' Eπ h' c Pt h₁
      obtain ⟨y₁, hy₁, hN₁, e₁⟩ := ih₁ hx₁
      refine ⟨r • y₁, Submodule.smul_mem _ _ hy₁, Submodule.smul_mem _ _ hN₁, ?_⟩
      have e : (⟨r • x₁, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = r • ⟨x₁, hx₁⟩ := rfl
      rw [e, map_smul, e₁]
      exact (Submodule.Quotient.mk_smul _ _ _).symm

  have C2 : ∀ y hy, y ∈ NcS W T c →
      ∃ x hx, x ∈ NL W T Pt π' Eπ h' c ∧ β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx := by
    intro y hy hyN
    obtain ⟨⟨x, hx⟩, hq⟩ := Submodule.Quotient.mk_surjective _ (β T ⟨y, hy⟩)
    exact ⟨x, hx, Submodule.subset_span (beta_core W T Pt π' Eπ h' M σ c α β hfr hcry hjmp hs hww
      hQ hp4 hpt y hy ((mem_NcS W T c y).1 hyN).1 x hx hq.symm), hq.symm⟩

  have HighestWeightSpaceFinite : ∀ j : ℕ, j ≤ M → ∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy →
      x ∈ piNL W T Pt π' Eπ h' c j → y ∈ PiNS W T π' j := by
    intro j hjM x hx y hy hα hpi
    obtain ⟨x', hx'NL, rfl⟩ := Submodule.mem_map.1 hpi
    have hx'L := NL_le_LamLA W T π' Eπ h' c Pt hx'NL
    obtain ⟨y', hy', hy'N, hα'⟩ := C1 x' hx'L hx'NL
    have hay := LamPS_smul W T Eπ h' c (W.AΔ.pow_mem hπΔ j) hy'
    have h2 := F.2.2.2.2.1 (π' ^ j) (W.AΔ.pow_mem hπΔ j) x' hx'L y' hy' hα' hx hay
    rw [hα] at h2
    have hd : y - π' ^ j • y' ∈ JP W T π' Eπ h' M c := by
      have h2' : (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(LamPS W T Eπ h' c)) : QLamP W T π' Eπ h' M c) =
          Submodule.Quotient.mk ⟨π' ^ j • y', hay⟩ := h2
      have := (Submodule.Quotient.eq
        ((JP W T π' Eπ h' M c).comap (LamPS W T Eπ h' c).subtype)).1 h2'
      exact this
    obtain ⟨z, hzN, hz⟩ := JP_mem W T π' Eπ h' c hww hQ h5a M j hjM hd
    rw [mem_PiNS]
    refine ⟨⟨y' + z, Submodule.add_mem _ ((mem_NcS W T c y').1 hy'N).1 hzN, ?_⟩,
      ((mem_LamPS W T Eπ h' c y).1 hy).2.1⟩
    rw [smul_add, ← hz]
    abel

  have HighestWeightIntegral : ∀ j : ℕ, j ≤ M → ∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx →
      y ∈ PiNS W T π' j → x ∈ piNL W T Pt π' Eπ h' c j := by
    intro j hjM y hy x hx hβ hpi
    obtain ⟨⟨y1, hy1N, rfl⟩, -⟩ := (mem_PiNS W T π' j _).1 hpi
    have hunit : IsUnit (algebraMap (LetA O n) W.EE (π' ^ j)) := by
      rw [map_pow]
      exact hπu.pow j
    obtain ⟨-, hyΔ, hyc⟩ := (mem_LamPS W T Eπ h' c _).1 hy
    have hy1Δ : ∀ δ ∈ W.DelF, W.γD T δ y1 = y1 := by
      intro δ hδ
      have e : W.γD T δ (π' ^ j • y1) = π' ^ j • W.γD T δ y1 := by
        rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, W.AΔ.pow_mem hπΔ j δ hδ]
      refine sub_eq_zero.1 (tf_smul W T hunit ?_)
      rw [smul_sub, ← e, hyΔ δ hδ, sub_self]
    have hy1c : (letE c : LetA O n) • y1 = y1 := by
      refine sub_eq_zero.1 (tf_smul W T hunit ?_)
      rw [smul_sub, smul_comm, hyc, sub_self]
    have hy1Nc : y1 ∈ NcS W T c := (mem_NcS W T c y1).2 ⟨hy1N, hy1Δ, hy1c⟩
    have hy1L := hNP y1 hy1Nc
    obtain ⟨x1, hx1, hx1NL, hβ1⟩ := C2 y1 hy1L hy1Nc
    have hax := LamLA_smul W T π' Eπ h' c (W.AΔ.pow_mem hπΔ j) hx1
    have h6 := F.2.2.2.2.2.1 (π' ^ j) (W.AΔ.pow_mem hπΔ j) y1 hy1L x1 hx1 hβ1 hy hax
    rw [hβ] at h6
    have hd : x - smulLA W T π' c (π' ^ j) x1 ∈ JLA W T π' Eπ h' M c := by
      have h6' : (Submodule.Quotient.mk (⟨x, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) :
          QLamLA W T π' Eπ h' M c) = Submodule.Quotient.mk ⟨smulLA W T π' c (π' ^ j) x1, hax⟩ := h6
      have := (Submodule.Quotient.eq
        ((JLA W T π' Eπ h' M c).comap (LamLA W T π' Eπ h' c ⊤).subtype)).1 h6'
      exact this
    have h1 := JLA_le W T Pt π' Eπ h' M c hs hww hQ hp4 hpt hjmp hπΔ hEΔ j hjM hd
    have h2 : smulLA W T π' c (π' ^ j) x1 ∈ piNL W T Pt π' Eπ h' c j :=
      Submodule.mem_map_of_mem hx1NL
    have := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at this
  refine ⟨C1, C2, fun j _ hjM => ⟨HighestWeightSpaceFinite j hjM, HighestWeightIntegral j hjM⟩, ?_, ?_⟩
  · intro x hx y hy hα hinv
    have hγx : ((γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) x) ∈ piNL W T Pt π' Eπ h' c 1 :=
      (Submodule.mem_inf.1 hinv).2
    rw [LinearMap.sub_apply, LinearMap.id_apply] at hγx
    refine (mem_InvS W T π' Eπ h' 1 c y).2 ⟨hy, ?_⟩
    have hgx := LamLA_γ W T π' Eπ h' c hu' huu hγE hx
    have hgy := LamPS_γ W T Eπ h' c huu hγE hy
    have h7 := F.2.2.2.2.2.2.1 x hx y hy hα hgx hgy
    have hsx := Submodule.sub_mem _ hgx hx
    have hsy := Submodule.sub_mem _ hgy hy
    have hα' : α T ⟨_, hsx⟩ = mkP W T π' Eπ h' M c _ hsy := by
      have e : (⟨_, hsx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨_, hgx⟩ - ⟨x, hx⟩ := rfl
      rw [e, map_sub, h7, hα]
      exact (Submodule.Quotient.mk_sub _).symm
    exact HighestWeightSpaceFinite 1 hM _ hsx _ hsy hα' hγx
  · intro y hy x hx hβ hinv
    have hγy := ((mem_InvS W T π' Eπ h' 1 c y).1 hinv).2
    have hgx := LamLA_γ W T π' Eπ h' c hu' huu hγE hx
    have hgy := LamPS_γ W T Eπ h' c huu hγE hy
    have h8 := F.2.2.2.2.2.2.2.1 y hy x hx hβ hgy hgx
    have hsx := Submodule.sub_mem _ hgx hx
    have hsy := Submodule.sub_mem _ hgy hy
    have hβ' : β T ⟨_, hsy⟩ = mkLA W T π' Eπ h' M c _ hsx := by
      have e : (⟨_, hsy⟩ : ↥(LamPS W T Eπ h' c)) = ⟨_, hgy⟩ - ⟨y, hy⟩ := rfl
      rw [e, map_sub, h8, hβ]
      exact (Submodule.Quotient.mk_sub _).symm
    have h := HighestWeightIntegral 1 hM _ hsy _ hsx hβ' hγy
    refine Submodule.mem_inf.2 ⟨hx, ?_⟩
    show ((γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) x) ∈ piNL W T Pt π' Eπ h' c 1
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact h

end Local

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3upPf_FilC_anti (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) {a a' : ℤ} (h : a' ≤ a) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a' := by
  have hs : ∀ k : ℤ, FildR PD T.ρ τ (k + 1) ≤ FildR PD T.ρ τ k := by
    intro k
    refine inf_le_inf_left _ ?_
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul u w => exact ⟨u ⊗ₜ ⟨(w : BdR), PD.Fil_anti k w.2⟩, rfl⟩
    | add z z' hz hz' => rw [map_add (f := _)]; exact Submodule.add_mem _ hz hz'
  have hA : Antitone fun k => FildR PD T.ρ τ k := antitone_int_of_succ_le hs
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
  exact sup_le_sup_right (hA h) _

theorem u3upPf_memNL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n)
    (hPt : ∀ ζ τ, Pt c ζ τ → Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c)
    (hup : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true) (f : W.EE)
    (hf : IsCoord W Pt π' Eπ h' S up b c f) (x : W.DD T) (hx : x ∈ NcS W T (c - 1))
    (hFil : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true → x ∈ FilL W T Pt c τ (b τ)) :
    f ⊗ₜ mkL W T π' c x hx ∈ NL W T Pt π' Eπ h' c := by
  obtain ⟨a, ha, hea, hΛ, hup0, -, -⟩ := hf
  apply Submodule.subset_span
  refine ⟨1, fun _ => ⟨a, ha⟩, fun _ => x, ⟨fun _ => hx, ?_⟩, ?_⟩
  · rw [Fin.sum_univ_one]
    show TensorProduct.map (LinearMap.mulLeft O (algebraMap (LetA O n) W.EE (Eπ ^ h'))) LinearMap.id
        (f ⊗ₜ mkL W T π' c x hx) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ mkL W T π' c x hx
    rw [TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply, hΛ, hea]
  · intro τ ζ hpt i
    have hO := hPt ζ τ hpt
    have hu := hup τ hO
    have hv : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b τ) := hFil τ hO hu ζ hpt
    show (∑ j : Fin 1, serC (W.lev c ζ a) (valAt W T c ζ x) i) ∈ _
    rw [Fin.sum_univ_one]
    unfold serC
    split_ifs with hi
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      simp only [Int.toNat_natCast]
      by_cases hlt : k + b τ < h'
      · rw [hup0 τ ζ hpt hu k hlt, zero_smul]
        exact Submodule.zero_mem _
      · apply Submodule.smul_mem
        refine u3upPf_FilC_anti T τ ?_ hv
        push_neg at hlt
        omega
    · exact Submodule.zero_mem _

theorem u3upPf_PiNS_one (T : LocLat G Qp LL O) (π' : LetA O n) {M : ℕ} (hM : 1 ≤ M) {z : W.DD T}
    (hz : z ∈ PiNS W T π' M) : z ∈ PiNS W T π' 1 := by
  obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
  refine Submodule.mem_inf.2 ⟨?_, hz2⟩
  rw [Submodule.restrictScalars_mem] at hz1 ⊢
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN at hz1 ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz1
  refine Submodule.mem_map.2 ⟨π' ^ (M - 1) • w, (W.N T).smul_mem _ hw, ?_⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hM]

theorem u3upPf_lift {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' M ρ : ℕ) (c : ZMod n)
    (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)
    (hMF : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M) (hW : WKill W F ρ)
    (hNL : NinLam W T₁ Eπ h') (hG1 : GamPi W T₁ π') (hG2 : GamPi W T₂ π')
    (x : LA W T₂ π' c) (hx : x ∈ LamLA W T₂ π' Eπ h' c ⊤) (hxN : x ∈ NL W T₂ Pt π' Eπ h' c)
    (y : W.DD T₂) (hy : y ∈ LamPS W T₂ Eπ h' c)
    (hα : α T₂ ⟨x, hx⟩ = mkP W T₂ π' Eπ h' M c y hy) : LiftsBy W F π' Eπ h' ρ c y := by
  obtain ⟨n₂, hn₂, hn₂N, hα₂⟩ := hMF.1 x hx hxN
  have hd : y - n₂ ∈ PiNS W T₂ π' M := by
    refine (hMF.2.2.1 M hM le_rfl).1 0 (Submodule.zero_mem _) (y - n₂)
      (Submodule.sub_mem _ hy hn₂) ?_ (Submodule.zero_mem _)
    have h0 : (⟨0, Submodule.zero_mem _⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = 0 := rfl
    rw [h0, map_zero]
    symm
    show Submodule.Quotient.mk ((⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨n₂, hn₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c)
    rw [Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hα.symm.trans hα₂
  have hyN : y ∈ NcS W T₂ c := by
    obtain ⟨-, hΔ, hl⟩ := (mem_LamPS W T₂ Eπ h' c y).1 hy
    refine (mem_NcS W T₂ c y).2 ⟨?_, hΔ, hl⟩
    have h1 := PiNS_le_N W T₂ π' M hd
    have h2 := ((mem_NcS W T₂ c n₂).1 hn₂N).1
    have h3 := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at h3
  obtain ⟨n₁, hn₁, hF⟩ := hW c n₂ hn₂N
  refine ⟨(mem_InvS W T₂ π' Eπ h' 1 c y).2 ⟨hy, (Submodule.mem_inf.1 (hG2 c y hyN)).1⟩, n₁,
    (mem_InvS W T₁ π' Eπ h' 1 c n₁).2 ⟨hNL c hn₁, (Submodule.mem_inf.1 (hG1 c n₁ hn₁)).1⟩, ?_⟩
  rw [hF, ← smul_sub]
  exact Submodule.smul_mem _ _ (u3upPf_PiNS_one W T₂ π' hM hd)

end Local

theorem u3upPf_pt_over (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c := by
  obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hpt
  apply AlgHom.ext
  intro z
  have hzK : (z : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) z.2
  rw [AlgHom.comp_apply, hres (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 z) ⟨z, hzK⟩ rfl]
  exact hemb z ⟨z, hzK⟩ rfl

theorem u3upPf_MK_pos {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) (h' : ℕ)
    (hh' : 1 ≤ h') : 1 ≤ MK l K h' := by
  have hs := frobpin_sK_pos hl K LL hG
  have h4 : (0 : ℝ) < 4 * (h' : ℝ) := by
    have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
    linarith
  have hs' : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs
  exact Nat.ceil_pos.2 (div_pos h4 hs')

theorem u3upPf_ofR (D : D7) (HW : HWOf D.loc) (hMF : modelFR D HW) (hW : wKillR D HW)
    (hNL : ninLamR D HW) (hGP : gamPiR D HW) : UpSlotProposition D HW := by
  intro l _ hl K LL hG π' E hπ T₁ T₂ F S η m h' up b c α β hfr hN hall
  intro f hf x hx hFil h1 y hy hα
  obtain ⟨hc1, hc2, hon, hj1, hj2, hηb, hbS, hh', -, -⟩ := hN
  have hjI : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
      ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro T hj τ a ha
    have hd := hj τ a ha
    have hb := hbS τ
    have hη := hηb τ
    rw [Set.mem_Icc]
    rcases hd with hd | hd
    · unfold deep at hd
      split_ifs at hd <;> (rw [Set.mem_Icc] at hd; constructor <;> omega)
    · rw [Set.mem_Icc] at hd
      constructor <;> omega
  have hM := u3upPf_MK_pos hl K LL hG h' hh'
  have hMF2 := hMF l hl K LL hG π' E hπ h' hh' c α β hfr T₂ hc2 (hjI T₂ hj2)
  have hW' := hW l hl K LL hG π' E hπ T₁ T₂ F h' hc1 hc2 hon (hjI T₁ hj1)
  have hNL1 := hNL l hl K LL hG π' E hπ T₁ h' hc1 (hjI T₁ hj1)
  have hG1 := hGP l hl K LL hG π' E hπ T₁ hc1
  have hG2 := hGP l hl K LL hG π' E hπ T₂ hc2
  have hxN := u3upPf_memNL _ T₂ _ π' _ h' S up b c (fun ζ τ hpt => u3upPf_pt_over D HW hG c ζ τ hpt)
    hall f hf x hx hFil
  exact u3upPf_lift _ F _ π' _ h' _ _ c α β hMF2 hM hW' hNL1 hG1 hG2 _ h1 hxN y hy hα

end Formalism.MainNotions.N.Ln34

end
end
