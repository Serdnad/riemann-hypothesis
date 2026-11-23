module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle357
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle192
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle394
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle265
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle155
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle396
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle398
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017

@[expose] public section

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.innerDatumStabiliser_from_adapted_pair : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' Λ : LV D) (γ g h : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → (∀ σ, Adapt σ F0 F0 → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam) F0 = Lsub lam F0 → ∃ n ∈ NRat F0, Formalism.HermitianLatticesTheory.gmap (n * σ) lam = lam) → (∀ σ, Adapt σ F0' F0' → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam') F0' = Lsub lam' F0' → ∃ n ∈ NRat F0', Formalism.HermitianLatticesTheory.gmap (n * σ) lam' = lam') → h ∈ stabL F F' Λ → ∃ b, GlobalTheory.StabCnt.InB F0 F0' lam lam' γ b ∧ GlobalTheory.StabCnt.Corr F0 F F0' F' γ g b h := by
  first | exact @GlobalTheory.StabCnt.stab_onto | exact GlobalTheory.StabCnt.stab_onto | (intros; apply GlobalTheory.StabCnt.stab_onto <;> assumption)
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamNG

theorem ampQ_id {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ id L = L.ampNG := by
  funext d
  unfold ampQ PN.LocalNG.ampNG
  simp only [id]

theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {νL νB : X.B.I.Ginf → Measure X.B.I.Ginf} {ng : PN.Pts D.host.E D.R.rS → ℝ} {γ : PN.Pts D.host.E D.R.rS}
    (h : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ) : HasPt Y u u' (Y.tO u u').ngSet γ := by
  obtain ⟨-, -, t, ht, hv, -, hp, -⟩ := h
  exact ⟨t, ht, hv, hp⟩

theorem leaves_of_fam : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧
    (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  intro hF
  refine ⟨fun hG => ?_, fun hW => ?_, fun hG4 => ?_, fun hE => ?_⟩
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hG Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S Fm hT => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ
      (hasPt_of_isPt hγ) Fm hT
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hW Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire
      hbk νL νB ng γ hγ S Fm hT hRel hTerm hG5 => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q
      i0 i0' νq Irat Ire hbk _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT hRel hTerm hG5
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨CSt, hCSt, a2, b2, h2⟩ := hG4 Cg cb Cw cT CT C0
    refine ⟨CSt, hCSt, max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0'
      νq Irat Ire hbk ν hν => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0
      ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hν
    refine ⟨s, hs1, hs2, hs3, fun γ hγ S Fm hT x _ => ?_⟩
    have h := hs4 _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT x.1 x.2
    rw [ampQ_id] at h
    exact h
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hE Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ (hasPt_of_isPt hγ)

end GlobalTheory.SnFamNG
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.NonzeroFlag

theorem telescope : ∀ (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ),
    (∀ i : Fin a, r i.succ = r i.castSucc + j i) → r (Fin.last a) = r 0 + ∑ i, j i := by
  intro a
  induction a with
  | zero => intro r j _; simp
  | succ a ih =>
    intro r j h
    have h1 := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => h i.castSucc)
    have h2 := h (Fin.last a)
    rw [Fin.sum_univ_castSucc]
    have h3 : r (Fin.last (a + 1)) = r (Fin.last a).castSucc + j (Fin.last a) := h2
    have h4 : r (Fin.last a).castSucc = r 0 + ∑ i : Fin a, j i.castSucc := h1
    omega

theorem exists_composition (a : ℕ) (j : Fin a → ℕ) (hj : ∀ i, 1 ≤ j i) (J : ℕ) (hJ : ∑ i, j i = J)
    (P : ∀ a : ℕ, (Fin a → ℕ) → Prop) (h : P a j) :
    ∃ c : Composition J, P c.length c.blocksFun := by
  have key : ∀ (b : ℕ) (e : b = a) (j' : Fin b → ℕ), (∀ i, j' i = j (Fin.cast e i)) → P b j' := by
    intro b e j' hh
    subst e
    have : j' = j := funext hh
    rw [this]; exact h
  refine ⟨⟨List.ofFn j, ?_, ?_⟩, key _ (by simp [Composition.length]) _ ?_⟩
  · intro i hi
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
    exact hj k
  · rw [List.sum_ofFn, hJ]
  · intro i
    simp [Composition.blocksFun]
    rfl

theorem measurableSet_simplexH (a : ℕ) : MeasurableSet (simplexH a) := by
  have : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : i < k, {τ : Fin a → ℝ | τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ : Fin a → ℝ | τ i < 1 / 2}) := by
    ext τ
    simp [simplexH, StrictMono]
  rw [this]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · exact MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem mem_typeSet (I : AutInst) (p q : ℕ) (hs : HasSig I p q) (x : I.GA) (hx : stepLt I x (1 / 2) ≠ ⊥) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, x ∈ typeSet I c.blocksFun (simplexH c.length) := by
  obtain ⟨⟨a, S, τ, hF⟩, -, h3⟩ := GlobalTheory.PointFlag.flag_spec I x
  have h3 := (h3 a S τ hF).1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hjdef
  have hj1 : ∀ i, 1 ≤ j i := fun i => by have := (h3 i).2.1; simp only [hjdef]; omega
  have hj2 : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := (h3 i).2.1; simp only [hjdef]; omega
  have htel := telescope a (fun i => Formalism.HN.rkK (S i)) j hj2
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hr := (GlobalTheory.T.canonicalLatticeFlag_isotropic_selfDual I x).2.1 v
  have hq : rkR (I.ε v) ≤ q := by
    rw [← (hs v).2]; exact min_le_right _ _
  have hle : ∑ i, j i ≤ q := by
    simp only [hF.2.2.1] at htel
    omega
  have ha : a ≠ 0 := by
    rintro rfl
    apply hx
    rw [← hF.2.2.1, ← hF.1]; rfl
  have hge : 1 ≤ ∑ i, j i :=
    (hj1 ⟨0, Nat.pos_of_ne_zero ha⟩).trans (Finset.single_le_sum (fun i _ => Nat.zero_le (j i)) (mem_univ _))
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨hge, hle⟩, ?_⟩
  refine exists_composition a j hj1 _ rfl (fun a j => x ∈ typeSet I j (simplexH a)) ?_
  exact ⟨τ, ⟨hF.2.2.2.1, fun i => ⟨(hF.2.2.2.2.1 i).1, (hF.2.2.2.2.1 i).2.1⟩⟩, S, hF, hj2⟩

theorem nonzeroFlagBound : VolumeStep → NonzeroFlagBound := by
  intro hV I μf _ _ fund hfund p q hs hn hq hrd hf
  obtain ⟨hfd, hv, -, hf1, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hpq := hpq p q hs
  have hn16 : 16 ≤ I.n := by
    have hpos : (0 : ℝ) < I.n := by
      rcases Nat.eq_zero_or_pos I.n with h | h
      · rw [h] at hn; simp at hn; linarith
      · exact_mod_cast h
    have := Real.log_le_sub_one_of_pos hpos
    have : (16 : ℝ) ≤ I.n := by linarith
    exact_mod_cast this
  have h2q : 2 * q + 2 ≤ I.n := by nlinarith
  set X : ℝ := I.n * I.f * Real.log I.n with hX
  have hX15 : 15 ≤ X := by
    have h1 : (1 : ℝ) ≤ I.n := by exact_mod_cast (by omega : 1 ≤ I.n)
    have h2 : (1 : ℝ) ≤ I.f := by exact_mod_cast hf1
    have h3 : (1 : ℝ) ≤ I.n * I.f := one_le_mul_of_one_le_of_one_le h1 h2
    rw [hX]; nlinarith
  have hone : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) / I.muA μf fund ≤
        ENNReal.ofReal (Real.exp (-(1 / 2 * J * X))) := by
    intro J hJ c
    obtain ⟨hJ1, hJq⟩ := Finset.mem_Icc.mp hJ
    have hsum := c.sum_blocksFun
    have hT := (GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio hV I μf fund hfund p q hs h2q c.length c.blocksFun
      (c.length_pos_of_pos hJ1) c.one_le_blocksFun (by omega) _ (measurableSet_simplexH _) subset_rfl).2.2.2
    have hD := GlobalTheory.T.lintegral_flagSizeDensity_le_one I.n I.f c.length c.blocksFun hf1 c.one_le_blocksFun (by omega)
    have hK := GlobalTheory.T.flag_explicit_constant_le_exp_neg_half I.E I.cm.cmUnram p q c.length c.blocksFun c.one_le_blocksFun (by omega)
      (by rw [hpq]; exact hn) (by rw [hpq]; exact hq) (by rw [hpq, hv]; exact hrd) (by rw [hpq, hfd]; exact hf)
    rw [hpq, hfd, hsum] at hK
    refine hT.trans ((mul_le_mul_right hD _).trans ?_)
    rw [mul_one]
    refine ENNReal.ofReal_le_ofReal (hK.trans (le_of_eq ?_))
    rw [hX]; congr 1; ring
  have hsub : {x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund ⊆
      ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
        typeSet I c.blocksFun (simplexH c.length) ∩ fund := by
    rintro x ⟨hx, hxf⟩
    obtain ⟨J, hJ, c, hc⟩ := mem_typeSet I p q hs x hx
    simp only [Set.mem_iUnion]
    exact ⟨J, hJ, c, mem_univ _, hc, hxf⟩
  have hμ : I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) ≤
      ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) :=
    (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun J _ => measure_biUnion_finset_le _ _))
  calc I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) / I.muA μf fund
      ≤ (∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund)) / I.muA μf fund :=
        ENNReal.div_le_div_right hμ _
    _ = ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) / I.muA μf fund := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal (Real.exp (-(1 / 2 * J * X))) :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hone J hJ c
    _ = ENNReal.ofReal (∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * X))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun J _ => by positivity)]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((GlobalTheory.T.sum_two_pow_pred_mul_exp_neg_le_exp_neg_third q X hX15).trans (le_of_eq ?_))
        rw [hX]; congr 1; ring

end GlobalTheory.NonzeroFlag
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.derivative_along_lie_algebra_preserves_smooth_space : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → ∀ W : Set (GA D V → ℂ), (∀ f ∈ W, Continuous f ∧ ∀ τ, ∃ L : Matrix (Fin V.rank) (Fin V.rank) ℂ → GA D V → ℂ, (∀ X ∈ lieAt V τ, L X ∈ W ∧ ∀ x, HasDerivAt (fun t : ℝ => f (x * oneP θ V τ X t)) (L X x) 0) ∧ ∀ (a : ℝ), ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ, L (a • X + Y) = (a : ℂ) • L X + L Y) → ∀ f ∈ W, ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  first | exact @GlobalTheory.DerClosedSmooth.smooth_of_closed | exact GlobalTheory.DerClosedSmooth.smooth_of_closed | (intros; apply GlobalTheory.DerClosedSmooth.smooth_of_closed <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localTerm_noDefect_primeTo_invariants : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), (FP p).RelG (LocNG.theta (Z.M p)) → (FP p).PrimeTo → ∀ (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → ¬ LocNG.BBne (H := locH Z p) t := by
  first | exact @GlobalTheory.LocNoDef.noDefect | exact GlobalTheory.LocNoDef.noDefect | (intros; apply GlobalTheory.LocNoDef.noDefect <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.lat_gmap {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T}
    {F0' : LFlag (D.sp.Y 0) D.R.rS T'} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G)
    (σ τ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    c.lat σ (Formalism.HermitianLatticesTheory.gmap τ Λ) = c.lat (σ * τ) Λ := by
  unfold GCoord.lat Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

theorem GFrames.datOf_N_fst (G : GFrames A r k) {g : G.GLV} (hg : g ∈ G.N) (Γ : G.Lt) (p) :
    (G.datOf (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) p).1 = (G.datOf Γ p).1 := by
  have hloc : ∀ q, ∃ g' ∈ (G.S q).N, A.Ext q g g' := hg
  obtain ⟨g', hgN, hext⟩ := hloc p
  unfold Places.Ext at hext
  have := (A.loc p).lf
  have := (A.loc p).char0
  have hmove : g' • A.lat p Γ = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    unfold Places.lat
    rw [Submodule.smul_span, Submodule.map_coe, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    apply congrArg (fun f => f '' (Γ : Set G.V))
    funext x
    simp [hext]
  unfold GFrames.datOf
  rw [← hmove]
  exact (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries (A.L p) r k (G.S p)).2.2.1 g' hgN (A.lat p Γ)

theorem GFrames.datOf_N'_snd (G : GFrames A r k) {g : G.GLV} (hg : g ∈ G.N') (Γ : G.Lt) (p) :
    (G.datOf (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) p).2.1 = (G.datOf Γ p).2.1 := by
  have hloc : ∀ q, ∃ g' ∈ (G.S q).N', A.Ext q g g' := hg
  obtain ⟨g', hgN, hext⟩ := hloc p
  unfold Places.Ext at hext
  have := (A.loc p).lf
  have := (A.loc p).char0
  have hmove : g' • A.lat p Γ = A.lat p (Γ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E))) := by
    unfold Places.lat
    rw [Submodule.smul_span, Submodule.map_coe, ← Set.image_smul, Set.image_image, Set.image_image]
    congr 1
    apply congrArg (fun f => f '' (Γ : Set G.V))
    funext x
    simp [hext]
  unfold GFrames.datOf
  rw [← hmove]
  exact (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries (A.L p) r k (G.S p)).2.2.2.1 g' hgN (A.lat p Γ)
end Loc

theorem datOf_dcoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).1 = (G.datOf (c.lat ρ t₀.lam) p).1 ∧ (G.datOf (c.lat (ρ * n) t.lam) p).2.1 = (G.datOf (c.lat ρ t₀.lam) p).2.1 := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hB G c t₀ ρ U U' hmv t n m hlam hlam' hnm p
  obtain ⟨hn, hm, hlin⟩ := hnm
  obtain ⟨P1, P2, P3, -⟩ := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hB G c t₀ ρ U U' hmv

  have hrel : ∀ s : TauC Y u u', Formalism.HermitianLatticesTheory.gmap (GTerm.lin s) s.lam' = s.lam :=
    fun s => (Quot.out s.cls).property.2.2.1
  constructor
  · rw [P3, hlam]
    exact GFrames.datOf_N_fst G ((P1 n).1 hn) _ p
  · have e1 : c.lat (ρ * n) t.lam = (c.lat (ρ * GTerm.lin t₀) t₀.lam').map
        (((c.grp (ρ * GTerm.lin t₀) m : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) := by
      rw [← P3, ← hrel t, GCoord.lat_gmap, hlin, hlam']
      congr 1
      group
    have e2 : c.lat (ρ * GTerm.lin t₀) t₀.lam' = c.lat ρ t₀.lam := by
      rw [← GCoord.lat_gmap, hrel t₀]
    rw [e1, ← e2]
    exact GFrames.datOf_N'_snd G ((P2 m).1 hm) _ p

end GlobalTheory.HL
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_admissible_integralFrame_of_localTerms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) := by
  first | exact @GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt | exact GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt | (intros; apply GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt <;> assumption)
end

section

namespace GlobalTheory.HTThetaLeaf

theorem main : Formalism.L2.SG.NGHTie.HTTheta := by
  unfold Formalism.L2.SG.NGHTie.HTTheta
  exact GlobalTheory.TypeUnifProd.main

end GlobalTheory.HTThetaLeaf
end

section

namespace GlobalTheory.DiffModProd

theorem htDelta : Formalism.L2.SG.NGHTie.HTDelta := by
  unfold Formalism.L2.SG.NGHTie.HTDelta
  exact finprod_modK_localGen

end GlobalTheory.DiffModProd
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localPairingClass_stable_unitriangularChange : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) → Chg f A g → Chg f' A' g' → H.Zhat f f' ∈ clsLoc M Y0 → H.Zhat g g' ∈ clsLoc M Y0 := by
  first | exact @GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg | exact GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg | (intros; apply GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localMass_le_genericMass_const_nine : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets k r 9 := by
  first | exact @GlobalTheory.localMass_le_genericMass_nine | exact GlobalTheory.localMass_le_genericMass_nine | (intros; apply GlobalTheory.localMass_le_genericMass_nine <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.mean_primitive_corank_one_sublattices_bound : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), UnitaryVolumeMass.stMassRatio D → Formalism.MainNotions.BridgeLemma₂.PrimitiveMeanCorankOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  first | exact @GlobalTheory.Mass.PrimMeanCorankOne.main | exact GlobalTheory.Mass.PrimMeanCorankOne.main | (intros; apply GlobalTheory.Mass.PrimMeanCorankOne.main <;> assumption)
end
