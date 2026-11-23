module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle032
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBoundOfNorms
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CjTFromBlocks
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrame
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1b

variable {D : D7} {X : HidaSetting D}

theorem fixedFlag_level_ne_zero (D : D7) (u : D.what₂.Word) : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

theorem relevantSet_zeroG_not_identity {Y : Full X} {u : D.what₂.Word} {t : GTu Y u} (ht : t ∈ relSet Y u) :
    t.relevant ∧ t.G = 0 ∧ ¬ t.isId := by
  obtain ⟨⟨hG, hid⟩, hr⟩ := ht
  refine ⟨hr, ?_, hid⟩
  have h : Gt t = 0 := hG
  unfold Gt at h
  by_contra hne
  rw [if_neg hne] at h
  exact one_ne_zero h

theorem exists_nfFull_of_relevant_of_G_eq_zero (Y : Full X) {u : D.what₂.Word} (t : GTu Y u) (hr : t.relevant) (hG : t.G = 0) :
    ∃ (j : ℕ) (hj : j ≤ D.R.rS) (c : D.host.E),
      Formalism.HermitianLatticeCounting.S6.NFFull (nfF (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)) (nfF (frq X t.rep).fl (nf_T_ne D u)) j hj c := by
  obtain ⟨hrel, hG0⟩ := relRepC D X Y u u t hr hG
  obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hpos : 0 < (σ ((Tu D u : ℕ) : D.host.E)).re := by
    rw [map_natCast, Complex.natCast_re]
    exact_mod_cast tie_Tu_pos D u
  refine Formalism.HermitianLatticeCounting.Final.S6.normalForm D.host.E (hS D).V σ (nfH (hS D)) D.R.rS _ _ (fun x => p_starConj D σ x)
    hpos hpos (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ) (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ)
    (nf_rel D.host.F (tie_trace D.sp.cm) _ _ _ _ hrel) ?_
  rw [nf_G (lf D (X.Fu u)).fl (frq X t.rep).fl (fixedFlag_level_ne_zero D u) (nf_T_ne D u)]
  exact hG0

theorem index_eq_normalForm {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) {j : ℕ} {hj : j ≤ D.R.rS} {c : D.host.E}
    (hN : Formalism.HermitianLatticeCounting.S6.NFFull (nfF (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)) (nfF (frq X t.rep).fl (nf_T_ne D u)) j hj c) :
    jT t = j := by
  have hfin := hN.1.2.1
  rw [nf_II (lf D (X.Fu u)).fl (frq X t.rep).fl (fixedFlag_level_ne_zero D u) (nf_T_ne D u)] at hfin
  unfold jT
  rw [hfin]
  omega

theorem realAbs_zero_eq_one (rd : ℝ) (τ : D.host.E →+* ℂ) (x : D.host.E) (hx : x = 1) :
    absReal rd τ D.R.rS 0 x = 1 := by
  subst hx
  simp [absReal, frameExp]

theorem delta_pos_le_height_sq (hPF : PFHost D) (large₂ : SizeData₂ D) {CH C : ℝ} (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) (ht : t ∈ relSet Y u) :
    0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hD : Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j ≠ 0 := (nf_gen _ _ _ _ j hj c hN).2.2.2.1
  have hlab : labT t (jT t) = Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j := by
    unfold labT
    rw [if_pos le_rfl, hjT]
  have hdel : k2Del D (jT t) (labT t) =
      ∏ τ : D.what₂.Tau, absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) ^ 2 := by
    unfold k2Del
    exact hPF _ _
  have hrd := pf_rd_pos D
  have hpos : ∀ τ, 0 < absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) := by
    intro τ
    unfold absReal
    rw [hlab]
    exact mul_pos (norm_pos_iff.2 ((map_ne_zero _).2 hD)) (Real.rpow_pos_of_pos hrd _)
  refine ⟨by rw [hdel]; exact Finset.prod_pos fun τ _ => pow_pos (hpos τ) 2, ?_⟩
  rw [hdel]
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  unfold k2S
  rw [← Finset.prod_pow]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (H1C large₂ CH) _ (szf_card_Tau D)
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb (two_rank_add_two_eq_m D) hCH hC) (fun τ => (hpos τ).le) (fun τ => ?_) (fun τ => ?_)
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · rcases Nat.eq_zero_or_pos (jT t) with h0 | h0
    · have hl0 : labT t (jT t) = 1 := by
        rw [hlab, ← hjT, h0]
        unfold Dl leadMinorE
        simp
      have h1 : absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) = 1 := by
        rw [h0] at hl0 ⊢
        exact realAbs_zero_eq_one _ _ _ hl0
      rw [h1]
      have h2 : (1 : ℝ) ≤ (2 * H1C large₂ CH) ^ (2 * D.R.rS) := one_le_pow₀ (by linarith)
      have h3 : (1 : ℝ) / (2 * H1C large₂ CH) ^ (2 * D.R.rS) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h2
      exact h3.trans ((Finset.le_fold_max _).2 (Or.inl le_rfl))
    · have hmem : jT t ∈ k2ends D (jT t) (labT t) := by
        unfold k2ends
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h0, le_rfl⟩, by rw [hlab]; exact hD⟩
      exact (Finset.le_fold_max _).2 (Or.inr ⟨jT t, hmem, le_rfl⟩)

theorem localNorm_le_height_sq (hPF : PFHost D) (large₂ : SizeData₂ D) {CH C : ℝ} (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) (l : ℕ) (hl : l ∈ k2ends D (jT t) (labT t)) :
    ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) ≤
      Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hrd := pf_rd_pos D
  rw [hPF]
  unfold k2S
  rw [← Finset.prod_pow]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (H1C large₂ CH) _ (szf_card_Tau D)
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb (two_rank_add_two_eq_m D) hCH hC) (fun τ => ?_) (fun τ => ?_) (fun τ => ?_)
  · unfold absReal
    positivity
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · exact (Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)

end ZsC1b

theorem DelC_holds : DelC := by
  intro Cg cb Cw cT CT C0 CH hCH
  refine ⟨2 * (CH + 1), fun C hC => ⟨0, 0, fun C' Cl _ _ D large₂ X Y u hH _ t ht => ?_⟩⟩
  exact delta_pos_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t ht

end Formalism.L2.SG.KappaOffDiagonal
end
end

section

noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped Classical TensorProduct

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem finiteLevelVolume_of_measure (hM : X.MeasTie hb) : FiniteLevelVolumeEquality X hb := by
  unfold FiniteLevelVolumeEquality
  rw [hM.2.2.1]
  haveI : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  let e := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).toHomeomorph.toMeasurableEquiv
  have he : (X.toFin hb : X.B.I.Gf → _) = e := rfl
  have hK : levelUnitary X hb = e '' X.K2 := rfl
  rw [hK, he, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]

theorem mem_rr_iff (x : X.B.I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ↔
      toHA X.B.I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I (toHA X.B.I hb) (toHA_isBridge X.B.I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J,
      h ∈ ratHA X.B.I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA X.B.I hb).injective hyx]

theorem covolTie_of (hM : X.MeasTie hb) : CovolTie X := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' X.B.I X.B.μf
  haveI : (X.B.I.muA X.B.μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) X.B.fund (X.B.I.muA X.B.μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨X.B.fund_spec.1, X.B.fund_spec.2.1, X.B.fund_spec.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
  let e := (toHA X.B.I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I :=
    { toFun := fun g => ⟨(toHA X.B.I hb).symm (g : HA _ _ _), (mem_rr_iff X hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA X.B.I hb x, (mem_rr_iff X hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  haveI : Countable Γ := Function.Injective.countable eΓ.injective
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((X.B.I.muA X.B.μf).map e) (X.B.I.muA X.B.μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' X.B.fund) X.measG.μG := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : X.B.I.GA) * x) = (g : HA _ _ _) * e x
    show toHA X.B.I hb ((toHA X.B.I hb).symm g * x) = (g : HA _ _ _) * toHA X.B.I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmap : X.measG.μG (e '' X.B.fund) = X.B.I.muA X.B.μf X.B.fund := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]
  haveI : (X.measG.μG).IsHaarMeasure := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    exact (toHA X.B.I hb).isHaarMeasure_map (X.B.I.muA X.B.μf)
  haveI : (X.measG.μG).IsMulLeftInvariant := inferInstance
  haveI : MeasurableConstSMul Γ (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    ⟨fun c => (continuous_const_mul (c : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurable⟩
  unfold CovolTie covolBy
  split_ifs with h
  · have h1 : IsFundamentalDomain Γ h.choose X.measG.μG := h.choose_spec
    rw [h1.measure_eq hfd, hmap]
    rfl
  · exact absurd ⟨_, hfd⟩ h

section MassData

open Formalism.L2.SG.MassDataConc Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem MassDataDstarX_holds (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = Formalism.L2.SG.RowsConc.DstC X :=
  MassDataDstarX X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq L A hH hKpp (finiteLevelVolume_of_measure X hb hH.1)
    (covolTie_of X hb hH.1)

end MassData

end Formalism.L2.SG.IntegralApproximation
end
end

section

noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Corner

variable {K : Type*} [CommRing K] (cj : K →+* K) {r : ℕ}

def cornerM (g : K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then g else 0

theorem corner_left (L : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hcj : cj 1 = 1) (g : K) : L * cornerM (r := r) g * cjT cj L = cornerM g := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply, cjT, Matrix.transpose_apply, Matrix.map_apply]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, if_pos rfl]
    rw [hL i, hL j]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj, hcj]
  · intro b _ hb; simp [hb]
  · simp

theorem corner_right (P : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0)
    (hcj : cj 1 = 1) (g : K) : cjT cj P * cornerM (r := r) g * P = cornerM g := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply, cjT, Matrix.transpose_apply, Matrix.map_apply]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hP i]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hP j]
  by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj, hcj]

end Corner

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem gDiag_corner (p : PlF D) (T : D.host.E) :
    gDiag δ M p T = cornerM (frFac δ p (Fin.last D.R.rS) * (M p).L.cj (frFac δ p (Fin.last D.R.rS)) *
      (D.s.atP p).ιE (-T)) := by
  ext a b
  simp only [gDiag, cornerM, Matrix.of_apply]
  by_cases h : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
  · rw [if_pos h, if_pos h, h.1, h.2]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]

theorem gaCong_L (hA : ∀ q, Agree δ M q) (p : PlF D) (hs : (M p).split = none) (T T' : D.host.E) (Z Z' : MatZ D)
    (L P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep)
    (hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0)
    (hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0)
    (hLO : ∀ i j, L i j ∈ (M p).L.O) (hPO : ∀ i j, P i j ∈ (M p).L.O)
    (hLu : ∃ y ∈ (M p).L.O, L.det * y = 1) (hPu : ∃ y ∈ (M p).L.O, P.det * y = 1)
    (hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P) :
    ∃ A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
      GaPlus M δ p T T' Z' = (A.map (M p).L.cj).transpose * GaPlus M δ p T T' Z * A := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) with hcj
  have hinv : ∀ x, cj (cj x) = x := fun x => (M p).L.cj_cj x
  refine ⟨Matrix.fromBlocks (cjT cj L) 0 0 P, ?_, ?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O (M p).L _ (hLO j i)
    · exact (M p).L.O.zero_mem
    · exact (M p).L.O.zero_mem
    · exact hPO i j
  · obtain ⟨y, hy, hLy⟩ := hLu
    obtain ⟨z, hz, hPz⟩ := hPu
    refine ⟨cj y * z, (M p).L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O (M p).L _ hy) hz, ?_⟩
    rw [Matrix.det_fromBlocks_zero₂₁]
    have hd : (cjT cj L).det = cj L.det := by
      unfold cjT; rw [Matrix.det_transpose]; exact (RingHom.map_det cj L).symm
    rw [hd]
    calc cj L.det * P.det * (cj y * z) = cj (L.det * y) * (P.det * z) := by rw [map_mul]; ring
      _ = 1 := by rw [hLy, hPz, map_one, one_mul]
  · have e1 : GaPlus M δ p T T' Z' = GaLoc M δ p T T' Z' := by unfold GaPlus; rw [hs]
    have e2 : GaPlus M δ p T T' Z = GaLoc M δ p T T' Z := by unfold GaPlus; rw [hs]
    rw [e1, e2, gaLoc_blocks δ M hA, gaLoc_blocks δ M hA]
    show _ = cjT cj _ * _ * _
    refine (block_cong cj hinv _ _ _ _ _ _ _ _ ?_ ?_ ?_).symm
    · rw [cjT_cjT cj hinv, gDiag_corner]
      exact corner_left cj L hL (map_one cj) _
    · rw [cjT_cjT cj hinv, hX]
    · rw [gDiag_corner]
      exact corner_right cj P hP (map_one cj) _

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def chiOO (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) : X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf)
            ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt) • Formalism.L2.SG.TermOp.OOt s

def frameVal (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u')
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) : X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.PairVal.cTerm vR s.toTerm •
    ((A : X.Vpi u →L[ℂ] X.Vpi u).comp
      ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.toTerm)).comp (B.symm : X.Vpi u' →L[ℂ] X.Vpi u')))

def NormalFormC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'),
      chiOO X Y u u' s.1 = frameVal X Y u u' vR i0 i0' νq A B s.1

def CommonFrameC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ (U : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (U' : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u') (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ (s : LiftT X Y u u' κ R ρ) (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'),
        chiOO X Y u u' s.1 = frameVal X Y u u' vR i0 i0' νq A B s.1 →
          frameVal X Y u u' vR i0 i0' νq A B s.1 = ζ • frameVal X Y u u' vR i0 i0' νq U U' s.1

def LemmaVLiftC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), ¬ s.1.relevant →
    Formalism.L2.SG.TermOp.OOt s.1 = 0

def AtPtRelevantC : Prop :=
  ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w → t.relevant

theorem cTerm_irrel (hAt : AtPtRelevantC X Y u u') (t : Term D u u' (X.Fu u) (Y.what₂ u)) (ht : ¬ t.relevant) :
    Formalism.L2.SG.PairVal.cTerm vR t = 0 := by
  unfold Formalism.L2.SG.PairVal.cTerm
  rw [dite_eq_right]
  rintro ⟨w, hw⟩
  exact ht (hAt t w hw)

end Formalism.L2.SG.Pf.RowForm

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Pf.RowForm
  MeasureTheory

theorem classFrameOO_of {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hB : NormalFormC X Y u u' vR i0 i0' νq κ)
    (hC : CommonFrameC X Y u u' vR i0 i0' νq κ) (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    ClassFrameOO X Y u u' vR i0 i0' νq κ := by
  intro R ρ
  obtain ⟨U, U', ζ, hζ, hU⟩ := hC R ρ
  refine ⟨U, U', ζ, hζ, fun s => ?_⟩
  by_cases hs : s.1.relevant
  · obtain ⟨A, B, hAB⟩ := hB R ρ s hs
    have h1 := hAB.trans (hU s A B hAB)
    unfold chiOO frameVal at h1
    rw [h1, smul_smul]
  · rw [hV R ρ s hs, smul_zero, cTerm_irrel X Y u u' vR hAt _ hs, mul_zero, zero_smul]

end Formalism.L2.SG.Pf
end
end
