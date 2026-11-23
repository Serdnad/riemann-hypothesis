module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle254
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle251
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle244
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.ptSq_add_hsDist_comparable_hsDist_mul : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptSq e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptSq e y + hsDist g ≤ t * hsDist (a * j g) ∧ hsDist (a * j g) ≤ t * (ptSq e y + hsDist g) := by
  first | exact @GlobalTheory.SectionHsCompare.hsDist_section_mul_block | exact GlobalTheory.SectionHsCompare.hsDist_section_mul_block | (intros; apply GlobalTheory.SectionHsCompare.hsDist_section_mul_block <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.polar_tanSq_ptSq_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanSq u < (t⁻¹ * r) ^ 2 → ptSq e (polarPt e u) < r ^ 2) ∧ (ptSq e (polarPt e u) < r ^ 2 → tanSq u < (t * r) ^ 2) := by
  first | exact @GlobalTheory.PolarCompare.polar_sq_compare | exact GlobalTheory.PolarCompare.polar_sq_compare | (intros; apply GlobalTheory.PolarCompare.polar_sq_compare <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.NearMod

theorem fDeg_eq (I : AutInst) : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by

  have hE : IsTotallyComplex I.E := I.cm.cmUnram.1
  have hdeg : Module.finrank ℚ I.E = Module.finrank ℚ I.F * 2 := by
    rw [← I.cm.deg2, Module.finrank_mul_finrank]
  have hc := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.E
  have hr : NumberField.InfinitePlace.nrRealPlaces I.E = 0 :=
    NumberField.nrRealPlaces_eq_zero_iff.mpr hE
  unfold Formalism.HermitianLatticesTheory.fDeg AutInst.f
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

theorem two_vInv_eq (I : AutInst) : 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd := by
  unfold Formalism.HermitianLatticesTheory.vInv AutInst.rd
  rw [fDeg_eq]
  ring

theorem one_type_arith (L κ Y : ℝ) (a J : ℕ) (hL : 0 ≤ L) (hJ : 1 ≤ J) (haJ : a ≤ J)
    (hκ : κ ≤ Real.exp (-(1 / 2 * J * L))) (hY0 : 0 ≤ Y) (hY : Y ≤ Real.exp (1 / 8 * L)) :
    2 * κ * Y ^ a ≤ 2 * Real.exp (-(3 / 8) * L) := by

  have hYa : Y ^ a ≤ Real.exp (a * (1 / 8 * L)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hY0 hY a
  have hYa0 : 0 ≤ Y ^ a := pow_nonneg hY0 a
  rcases lt_or_ge κ 0 with hκ0 | hκ0
  · have : κ * Y ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hκ0.le hYa0
    nlinarith [Real.exp_pos (-(3 / 8) * L)]
  · have h1 : κ * Y ^ a ≤ Real.exp (-(1 / 2 * J * L)) * Real.exp (a * (1 / 8 * L)) :=
      mul_le_mul hκ hYa hYa0 (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have ha' : (a : ℝ) ≤ J := by exact_mod_cast haJ
    have h2 : -(1 / 2 * J * L) + a * (1 / 8 * L) ≤ -(3 / 8) * L := by
      nlinarith [mul_nonneg (sub_nonneg.2 ha') hL, mul_nonneg (sub_nonneg.2 hJ') hL]
    have h3 := Real.exp_le_exp.2 h2
    nlinarith

theorem nearModerate : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.FlagMeas.ConstantBound → GlobalTheory.Dec.NearUnip →
    GlobalTheory.Deep.PtBound → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate := by
  intro hFM hCB hNU hPB
  unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate
  intro Cg hCg
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.moderate_log_factor_absorbed Cg
  refine ⟨max n₁ (3 ^ 15), ?_⟩
  intro B d p q b hq hC
  have h8 : 8 ≤ max n₁ (3 ^ 15) := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨-, hrd, hf, -, hpq, -, -, hmin, hd, hX, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b h8 hC
  obtain ⟨hDS, hSig, hn₀, hq2, hlrd, hlf, hb, hlb, -, hg1, hgb, -⟩ := id hC

  have hPt := hPB B d p q h hDS hSig hgap (by rw [hmin]; exact h120)
  have hm : 0 ≤ mainTerm B d := by
    show 0 ≤ (∏ v, d v) * B.I.vol B.μf B.fund * (B.e 1).re
    exact mul_nonneg (mul_nonneg hd.le ENNReal.toReal_nonneg) hPt.2.2.2.2.1

  have hn3 : 3 ^ 15 ≤ B.I.n := (le_max_right _ _).trans hn₀
  have hn1 : 1 ≤ B.I.n := le_trans (by norm_num) hn3
  have hlogn : 15 ≤ Real.log B.I.n := by
    have h3 : Real.exp 15 ≤ (B.I.n : ℝ) := by
      have e1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 15 := pow_le_pow_left₀ (Real.exp_pos 1).le e1 15
        _ ≤ (B.I.n : ℝ) := by exact_mod_cast hn3
    have := Real.log_le_log (Real.exp_pos 15) h3
    rwa [Real.log_exp] at this
  have hL : 0 ≤ (B.I.n : ℝ) * B.I.f * Real.log B.I.n := by
    have : (0 : ℝ) ≤ Real.log B.I.n := by linarith
    positivity

  have hY := hn₁ B.I.n B.I.f q B.I.rd (B.g : ℝ) b ((le_max_left _ _).trans hn₀) hf hq hq2 hrd hlrd hlf
    hb hlb (by exact_mod_cast hg1) hgb
  have hlX : 0 ≤ Real.log (bigX B b) := Real.log_nonneg (by linarith)
  have hY0 : 0 ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hlX)
  have hY1 : 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) ≤
      Real.exp (1 / 8 * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
    hY.1.trans_eq (by congr 1; ring)

  have hA := GlobalTheory.T.nearTerms_moderate_points_one_type_bound hFM hNU hPB B Cg _ d p q b h8 hq hC
  have hper : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
          {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (mainTerm B d *
          (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)))) := by
    intro J hJmem c
    have hJ := Finset.mem_Icc.1 hJmem
    have hsum : ∑ i, c.blocksFun i = J := c.sum_blocksFun
    have ha : 1 ≤ c.length := c.length_pos_of_pos (by omega)
    have hj1 : ∀ i, 1 ≤ c.blocksFun i := fun i => c.one_le_blocksFun i
    refine (hA.2 c.length c.blocksFun ha hj1 (by rw [hsum]; exact hJ.2)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hm
    have hκ := hCB B.I.E B.I.cm.cmUnram p q c.length c.blocksFun hj1 (by rw [hsum]; exact hJ.2)
      (by rw [hpq]; exact hlogn) (by rw [hpq]; exact hq2) (by rw [two_vInv_eq, hpq]; exact hlrd)
      (by rw [fDeg_eq, hpq]; exact hlf)
    rw [hsum, hpq, fDeg_eq] at hκ
    exact one_type_arith _ _ _ c.length J hL hJ.1 c.length_le (hκ.trans_eq (by congr 1; ring)) hY0 hY1

  have hSm : MeasurableSet {x : B.I.GA | tauStar B q b ≤ least B.I x} :=
    measurableSet_le measurable_const (GlobalTheory.LeastVar.continuous_least B.I hn1).measurable
  have hΦ0 : ∀ x, 1 / 2 ≤ least B.I x →
      {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x = 0 :=
    fun x hx => Set.indicator_apply_eq_zero.2 (fun _ => hA.1 x hx)
  set M : ℝ := mainTerm B d * (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n))) with hM
  have h2q : (2 : ENNReal) ^ q = ENNReal.ofReal (2 ^ q) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x ∂(B.I.muA B.μf)
      = ∫⁻ x in B.fund, {x | tauStar B q b ≤ least B.I x}.indicator
          (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]; rfl
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
          ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
            {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_le_sum_types B p q hSig hn1 _ hΦ0
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal M :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hper J hJ c
    _ = ((∑ J ∈ Finset.Icc 1 q, Fintype.card (Composition J) : ℕ) : ENNReal) * ENNReal.ofReal M := by
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (2 : ENNReal) ^ q * ENNReal.ofReal M := by
        gcongr
        exact_mod_cast (GlobalTheory.sum_card_composition_lt q).le
    _ = ENNReal.ofReal (2 ^ q * M) := by
        rw [h2q]; exact (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d) := by
        apply ENNReal.ofReal_le_ofReal
        have e2 : Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) =
            Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        have e1 : Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) =
            Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
        rw [e2, hM, e1]
        calc (2 : ℝ) ^ q * (mainTerm B d * (2 * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)))
            = mainTerm B d * (2 * 2 ^ q * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)) := by ring
          _ ≤ mainTerm B d * Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) :=
            mul_le_mul_of_nonneg_left hY.2 hm
          _ = _ := mul_comm _ _

end GlobalTheory.NearMod
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

open ValuativeRel Formalism.MainNotions.S.Loc IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DiffModProd

theorem different_ne_zero (F : Type) [Field F] [NumberField F] : differentIdeal ℤ (𝓞 F) ≠ 0 := by
  intro h
  have := absNorm_differentIdeal F (𝓞 F)
  rw [h, map_zero] at this
  exact discr_ne_zero F (Int.natAbs_eq_zero.1 this.symm)

theorem card_infinitePlace (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm

theorem rdE_pow (D : D7) :
    D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  rw [card_infinitePlace, ← GlobalTheory.RealPlaces.finrank_E D]
  unfold Host.rdE
  rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3, sq_abs]

theorem finprod_modK_localGen : ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (Z.δ p)) =
      (D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹ := by
  intro D Z
  let A : GlobalTheory.HL.Places D.host.F D.host.E D.conjF :=
    { quad := D.sp.cm.deg2, loc := D.s.atP, L := fun p => (Z.M p).L, L_cj := fun p => Z.hcj p }
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    haveI := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hδ : ∀ p, Z.δ p ≠ 0 := fun p => (Z.agree p).2.1
  have hI := different_ne_zero D.host.F
  set g : PlF D → ℝ := fun p =>
    (GlobalTheory.HL.resQ (ϖ p) : ℝ) ^ GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) with hg
  have hmod : ∀ p, (Z.M p).modK (algebraMap _ _ (Z.δ p)) = (g p ^ 2)⁻¹ := by
    intro p
    rw [(GlobalTheory.BaseModule.modK_algebraMap (Z.M p) (Z.agree p).1 (ϖ p) (hϖ p)).2 _ (hδ p), hg]
    dsimp only
    rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
    congr 1
    push_cast
    ring
  have hcount : ∀ p, GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) =
      ((Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors : ℕ) :=
    fun p => GlobalTheory.IdealResProd.vE_eq_count (D.s.atP p) (Z.M p).L (hϖ p) _ hI (hδ p) (GlobalTheory.T.span_different_eq_localGenerator D Z p)
  have hfin : (Function.mulSupport g).Finite := by
    refine (Ideal.finite_factors hI).subset fun p hp => ?_
    simp only [Set.mem_setOf_eq]
    by_contra h
    apply hp
    have h0 : (Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors = 0 := by
      by_contra hne
      exact h ((Associates.count_ne_zero_iff_dvd hI p.irreducible).1 hne)
    simp [g, hcount p, h0]
  have hprod : ∏ᶠ p, g p = |(NumberField.discr D.host.F : ℝ)| :=
    (GlobalTheory.IdealResProd.discr_and_level A ϖ hϖ).1 (fun p => Units.mk0 (Z.δ p) (hδ p))
      (fun p => GlobalTheory.T.span_different_eq_localGenerator D Z p)
  have hsupp : (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))) ⊆
      Function.mulSupport g := fun p hp h => hp (by show (Z.M p).modK _ = 1; rw [hmod, h]; simp)
  refine ⟨hfin.subset hsupp, ?_⟩
  rw [finprod_congr hmod, finprod_inv_distrib, ← finprod_pow hfin, hprod, rdE_pow]

end GlobalTheory.DiffModProd
end

section

noncomputable section

namespace GlobalTheory.UnipFlagCore

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Matrix
open scoped TensorProduct ENNReal

theorem mem_spanR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n r : ℕ}
    (e : Fin r → Fin n → E) (s : Set (Fin r)) (w : Fin n → R ⊗[F] E) :
    w ∈ spanR (F := F) R e s ↔
      ∃ c : Fin r → R ⊗[F] E, (∀ b, b ∉ s → c b = 0) ∧ w = ∑ b, c b • ratTup (F := F) R e b := by
  classical
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨Pi.single a 1, fun b hb => ?_, ?_⟩
      · exact Pi.single_eq_of_ne (by rintro rfl; exact hb ha) _
      · rw [Finset.sum_eq_single a]
        · simp only [Pi.single_eq_same, one_smul]; rfl
        · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
        · simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      refine ⟨c + d, fun b hb => by simp [hc b hb, hd b hb], ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨t • c, fun b hb => by simp [hc b hb], ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hc b hb, zero_smul]; exact Submodule.zero_mem _

theorem hE_swap {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) : hE σ J y x = σ (hE σ J x y) := by

  simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ.1 j i]; ring

theorem nsub_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F),
    P.IsStd σ J T → ∃ K : Set (Nsub (AF F) σ J P), IsCompact K ∧
      ∀ m : Nsub (AF F) σ J P, ∃ γ ∈ ratOf (K := Nsub (AF F) σ J P), ∃ k ∈ K, m = γ * k := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hσ := conj_invol hCM
  obtain ⟨h0, -, hef, -, -, -, -⟩ := hP
  have he : LinearIndependent E P.e := linearIndependent_of_dual P.e P.f fun a b => by
    rw [hE_swap hσ hJ (P.e b) (P.f a), hef]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hlin : ∀ (g : HA (AF F) σ J) (x : Fin n → AF F ⊗[F] E),
      lin (AF F) σ J g x - x = ((HA.mat _ σ J g).1 - 1) *ᵥ x := fun g x => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  obtain ⟨K, hK, hm⟩ := cocompact_of_mem_iff_adelic hσ hJ P.e he h0 (Nsub (AF F) σ J P) fun g => by
    refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun x => imp_congr Iff.rfl ?_)
    · have := mem_spanR_iff (F := F) (AF F) P.e {b | b < a} (lin (AF F) σ J g (ratV (F := F) (AF F) (P.e a)) - ratV (F := F) (AF F) (P.e a))
      rw [this, hlin]
      simp only [Set.mem_setOf_eq, not_lt]
      rfl
    · have := mem_spanR_iff (F := F) (AF F) P.e Set.univ (lin (AF F) σ J g x - x)
      rw [this, hlin]
      simp only [Set.mem_univ, not_true_eq_false, false_imp_iff, implies_true, true_and]
  refine ⟨K, hK, fun m => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hm m
  exact ⟨γ, hγ, k, hk, rfl⟩

end GlobalTheory.UnipFlagCore
end
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PerpFlags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := fun v hv =>
  (mem_orth _ _).2 fun x hx => (mem_orth _ _).1 hv x (h hx)

theorem xplus_le {T : E} {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsFullLattice E Λ) (F : LFlag S r T)
    (M : Submodule (𝓞 E) S.V) (h1 : XLam Λ F ≤ M) (h2 : F.fl.z ∈ M) : Xplus F ≤ spanE S M := by
  refine sup_le (fun v hv => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span h2))
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hΛ v
  have h3 : d • v ∈ M := h1 ⟨hd, (toO S (Xsp F)).smul_mem d hv⟩
  have h4 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h3)
  rwa [← algebraMap_smul E d v,
    inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h4

theorem gflag_eq_zero {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c : Fin r → E) (hc : c ≠ 0)
    (h : ∀ b, S.hT (∑ a, c a • F.e a) (F'.fvec b) = 0) : Gflag F F' = 0 := by
  have hz : ∀ b, ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b = 0 := fun b => by
    have := h b

    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply] at this
    simpa [Zhat, brS, FlagG.fvec] using this
  obtain ⟨a0, ha0⟩ := Function.ne_iff.1 hc
  have d1 : Dl F F' r = 0 := by
    rw [Dl, leadMinorE, dite_eq_left (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨fun a => star (c a), fun e => ha0 (star_eq_zero.1 (congrFun e a0)), funext fun b => ?_⟩
    exact hz (Fin.castLE (Nat.le_succ r) b)
  have d2 : Dl F F' (r + 1) = 0 := by
    rw [Dl, leadMinorE, dite_eq_left le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0, fun e => ha0 ?_, funext fun b => ?_⟩
    · simpa using congrFun e a0.castSucc
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc] using hz b
  simp [Gflag, d1, d2]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → Hp Λ F F' ≤ orth S (Xplus F) ∧ Hp Λ F F' ≤ orth S (Xplus F') ∧ Hp Λ F F' ⊓ Xsp F = ⊥ := by
  intro E _ _ _ S r T T' Λ F F' hΛ hF hF' hG
  have a1 : Hp Λ F F' ≤ orth S (Xplus F) := orth_anti (xplus_le hΛ F _
    (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (hF.2 ▸ Submodule.mem_span_singleton_self _)))))
  have a2 : Hp Λ F F' ≤ orth S (Xplus F') := orth_anti (xplus_le hΛ F' _
    (le_sup_of_le_left le_sup_right)
    (Submodule.mem_sup_right (hF'.2 ▸ Submodule.mem_span_singleton_self _)))
  refine ⟨a1, a2, eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx.2
  by_cases hc : c = 0
  · simp [hc]
  refine absurd (gflag_eq_zero F.fl F'.fl c hc fun b => ?_) hG
  refine GlobalTheory.Mass.RowPerp.swap_zero S.herm ((mem_orth _ _).1 (a2 hx.1) _ ?_)
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · rw [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.LoopC.PerpFlags
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.ProdHaarS

theorem isHaarOn_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN →
    IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨-, -, h, -⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  exact h

end GlobalTheory.SgInf.ProdHaarS
end
