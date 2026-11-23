module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle022
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle013
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsNearOfSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniformizerValuationHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle017
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle011
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

@[expose] public section

section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem alpha_split' {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) {a b : ℕ} (hab : a ≤ b) :
    alphaStd K 𝔭 b = alphaStd K 𝔭 a *
      ∏ i ∈ Finset.Icc (a + 1) b, (1 - etaF K F 𝔭 ^ i * (Ideal.absNorm 𝔭 : ℝ) ^ (-(i : ℤ))) := by
  unfold alphaStd
  rw [← Finset.prod_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_Icc] at hi hi'
    omega

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem jordanIsom_of (hE : ExactVec) (hR : Rebase) (hL : LocSpan) (hU : UnifVal)
    (hJ : JordSpan) : Formalism.L2.SG.Pf.Cnt.JordanIsom := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L L' hLl hLl' 𝔭 h𝔭 b a b' a' hb hb' hv
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  obtain ⟨π, hπ, hval⟩ := hU K F hK hF P hP
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨-, hbL, hbo, hbn, hba⟩ := hb
  obtain ⟨-, hbL', hbo', hbn', hba'⟩ := hb'
  have span_of_jordan (c : Fin (finrank K (⊤ : Submodule K V)) → V)
      (d : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F)
      (ho : ∀ i j, i ≠ j → h (c i) (c j) = 0)
      (hn : ∀ i, h (c i) (c i) = algebraMap F K ((d i : 𝓞 F) : F))
      (hd : ∀ i, d i ≠ 0) : Submodule.span K (Set.range c) = ⊤ := by
    have hi : LinearIndependent K c := LinearMap.linearIndependent_of_isOrthoᵢ ho (fun i => by
      rw [hn i]
      apply (map_ne_zero (algebraMap F K)).2
      intro hz
      apply hd i
      exact FaithfulSMul.algebraMap_injective (𝓞 F) F (by simpa using hz))
    apply hi.span_eq_top_of_card_eq_finrank'
    simp
  have hsp := span_of_jordan b a hbo hbn hba
  have hsp' := span_of_jordan b' a' hbo' hbn' hba'
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨g, hg, -, hgm⟩ := core_of_split hs hda
    (splitAt_of (hE K F V hK hF h hs hd P hP π hπ) (hR K V (locRing P) π h hS hπ hs hda))
    _ (Fin _) le_rfl b b' (fun i => vF _ (a i)) 1 hbo hbo'
    (fun i => by rw [hbn i]; exact hval _ (hba i))
    (fun i => by rw [hbn' i, hv i]; exact hval _ (hba' i)) (one_mem _)
    (fun v => by
      rw [hsp, hsp']
      exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  refine ⟨g, hg, gmap_eq_of_iff fun v => ?_⟩
  rw [← hbL, ← hbL', locF_eq_loc hK hF hP, locF_eq_loc hK hF hP, hL K F V hK hF P hP,
    hL K F V hK hF P hP]
  exact hgm v

end Formalism.L2.SG.Pf.G3

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_isometry_holds : JordanIsom :=
  Formalism.L2.SG.Pf.G3.jordanIsom_of Formalism.L2.SG.Pf.TemperedBoundGL3.exact_vector_holds Formalism.L2.SG.Pf.TemperedBoundGL3.rebasing_holds
    Formalism.L2.SG.Pf.G3.local_span_holds Formalism.L2.SG.Pf.TemperedBoundGL3.uniformizer_valuation_holds Formalism.L2.SG.Pf.G3.jordan_span_holds

end Formalism.L2.SG.Pf.Cnt
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped ENNReal
open Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem uMat_continuous (v : InfinitePlace X.B.I.F) :
    Continuous fun s : X.B.I.Ginf => uMat (s v) := by
  first
    | exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)
    | fun_prop
    | continuity

theorem hJ_continuous (v : InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → ℂ) :
    Continuous fun s : X.B.I.Ginf => hJ (X.B.I.ε v) x (uMat (s v) *ᵥ y) := by
  simp only [hJ]
  first
    | exact continuous_const.matrix_dotProduct
        (continuous_const.matrix_mulVec ((uMat_continuous X v).matrix_mulVec continuous_const))
    | (have hu := uMat_continuous X v; fun_prop)

theorem xMat_entry_continuous (v : InfinitePlace X.B.I.F) (b a : Fin D.R.rS) :
    Continuous fun s => xMat X v s b a :=
  hJ_continuous X v (fV X v b) (eV X v a)

theorem aMat_entry_continuous (v : InfinitePlace X.B.I.F) (b a : Fin D.R.rS) :
    Continuous fun s => aMat X v s b a :=
  hJ_continuous X v (fV X v b) (fV X v a)

theorem xMat_continuous (v : InfinitePlace X.B.I.F) : Continuous fun s => xMat X v s := by
  first
    | exact continuous_pi fun b => continuous_pi fun a => xMat_entry_continuous X v b a
    | exact continuous_matrix fun b a => xMat_entry_continuous X v b a

theorem mMat_entry_measurable (v : InfinitePlace X.B.I.F) (b a : Fin D.R.rS) :
    Measurable fun s => mMat X v s b a := by
  have hx : Continuous fun s => xMat X v s := xMat_continuous X v
  have ha : Continuous fun s => aMat X v s := by
    first
      | exact continuous_pi fun b => continuous_pi fun a => aMat_entry_continuous X v b a
      | exact continuous_matrix fun b a => aMat_entry_continuous X v b a
  have hd : Measurable fun s => ((xMat X v s).det)⁻¹ := hx.matrix_det.measurable.inv
  simp only [mMat, Matrix.mul_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  refine Finset.measurable_sum _ fun c _ => ?_
  exact (hd.mul (hx.matrix_adjugate.matrix_elem b c).measurable).mul (ha.matrix_elem c a).measurable

theorem reim_measurable {α : Type} [MeasurableSpace α] {f : α → ℂ} (hf : Measurable f) (t : Bool) :
    Measurable fun x => reim (f x) t := by
  cases t
  · first
      | exact Complex.measurable_re.comp hf
      | (simp only [reim, Bool.false_eq_true, if_false]; exact Complex.measurable_re.comp hf)
  · first
      | exact Complex.measurable_im.comp hf
      | (simp only [reim, if_true]; exact Complex.measurable_im.comp hf)

theorem kap_measurable : Measurable (kap X u) := by
  refine Measurable.of_eval fun i => ?_
  obtain ⟨v, c⟩ := i
  rcases c with ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))
  · exact reim_measurable (xMat_entry_continuous X v p.1.1 p.1.2).measurable t
  · exact reim_measurable (hJ_continuous X v (fV X v b) (zV X u v)).measurable t
  · exact reim_measurable (hJ_continuous X v (fV X v b) (X.wfr u v j)).measurable t
  · exact reim_measurable (((mMat_entry_measurable X v p.1.1 p.1.2).sub
      (continuous_star.measurable.comp (mMat_entry_measurable X v p.1.2 p.1.1))).div_const 2) t
  · exact Complex.measurable_im.comp (mMat_entry_measurable X v a a)

private lemma isClosed_setOf_sub_one_mulVec_mem {n : ℕ} (w : Fin n → ℂ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ w ∈ S} := by
  have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => (g - 1) *ᵥ w := by
    first
      | exact (continuous_id.sub continuous_const).matrix_mulVec continuous_const
      | fun_prop
  exact S.closed_of_finiteDimensional.preimage hc

private lemma isClosed_setOf_InN {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have h : {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} =
      ((⋂ a : Fin r, {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ e a ∈ spanLt e a.1}) ∩
        {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ z ∈ spanLt e r}) ∩
      ⋂ y : Fin n → ℂ, ⋂ (_ : ∀ a, hJ ε (e a) y = 0),
        {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ y ∈ spanLt e r} := by
    ext g
    simp only [InN, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  exact ((isClosed_iInter fun a => isClosed_setOf_sub_one_mulVec_mem _ _).inter (isClosed_setOf_sub_one_mulVec_mem _ _)).inter
    (isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_setOf_sub_one_mulVec_mem _ _)

theorem ninfU_closed : IsClosed (X.NinfU u) := by
  have h : ∀ v : InfinitePlace X.B.I.F, IsClosed {s : X.B.I.Ginf | InN (X.B.I.ε v)
      (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat (s v))} := fun v =>
    (isClosed_setOf_InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))).preimage
      (uMat_continuous X v)
  have h2 := isClosed_iInter h
  simp only [← Set.setOf_forall] at h2
  exact h2

theorem boxN_eq : boxN X u = X.NinfU u ∩ kap X u ⁻¹' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) := by
  ext s
  simp only [boxN, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ico]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro h ⟨v, i⟩
    obtain ⟨hx, hy, hp, hm, hd⟩ := h v
    rcases i with ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))
    · cases t
      · exact (hx p.1.1 p.1.2 p.2).1
      · exact (hx p.1.1 p.1.2 p.2).2
    · cases t
      · exact (hy b).1
      · exact (hy b).2
    · cases t
      · exact (hp b j).1
      · exact (hp b j).2
    · cases t
      · exact (hm p.1.1 p.1.2 p.2).1
      · exact (hm p.1.1 p.1.2 p.2).2
    · exact hd a
  · intro h v
    exact ⟨fun b a hba => ⟨h (v, Sum.inl (Sum.inl (⟨(b, a), hba⟩, false))),
        h (v, Sum.inl (Sum.inl (⟨(b, a), hba⟩, true)))⟩,
      fun b => ⟨h (v, Sum.inl (Sum.inr (b, false))), h (v, Sum.inl (Sum.inr (b, true)))⟩,
      fun b j => ⟨h (v, Sum.inr (Sum.inl (b, j, false))), h (v, Sum.inr (Sum.inl (b, j, true)))⟩,
      fun b a hba => ⟨h (v, Sum.inr (Sum.inr (Sum.inl (⟨(b, a), hba⟩, false)))),
        h (v, Sum.inr (Sum.inr (Sum.inl (⟨(b, a), hba⟩, true))))⟩,
      fun a => h (v, Sum.inr (Sum.inr (Sum.inr a)))⟩

def KapInj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), Set.InjOn (kap X u) (X.NinfU u)

theorem coordMeas_of (h : KapInj) : CoordMeas := by
  intro D X u
  exact ⟨kap_measurable X u, (ninfU_closed X u).measurableSet, h D X u⟩

def HaarUnique : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (μ ν : Measure X.B.I.Ginf),
    IsHaarOnSet X.B.I (X.NinfU u) μ → IsHaarOnSet X.B.I (X.NinfU u) ν → ∃ c : ℝ≥0∞, μ = c • ν

def LebHaar : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    ∃ lam : Measure X.B.I.Ginf, IsHaarOnSet X.B.I (X.NinfU u) lam ∧ lam.map (kap X u) = volume

private lemma measure_inter_eq_of_compl_null {α : Type*} [MeasurableSpace α] (μ : Measure α) {N : Set α}
    (hN : μ Nᶜ = 0) (P : Set α) : μ (P ∩ N) = μ P := by
  refine le_antisymm (measure_mono Set.inter_subset_left) ?_
  calc μ P ≤ μ ((P ∩ N) ∪ Nᶜ) := by
        refine measure_mono fun s hs => ?_
        by_cases h : s ∈ N
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr h
    _ ≤ μ (P ∩ N) + μ Nᶜ := measure_union_le _ _
    _ = μ (P ∩ N) := by rw [hN, add_zero]

theorem coordHaar_of (hU : HaarUnique) (hL : LebHaar) : CoordHaar := by
  intro D X u μ hμ
  obtain ⟨lam, hlam, hmap⟩ := hL D X u
  obtain ⟨c, rfl⟩ := hU D X u μ lam hμ hlam
  have hkm : Measurable (kap X u) := kap_measurable X u
  have hbm : MeasurableSet (Set.pi Set.univ
      (fun _ : InfinitePlace X.B.I.F × CIdx D.R.rS D.R.k => Set.Ico (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hvol : volume (Set.pi Set.univ
      (fun _ : InfinitePlace X.B.I.F × CIdx D.R.rS D.R.k => Set.Ico (0 : ℝ) 1)) = 1 := by
    first
      | (rw [volume_pi, Measure.pi_pi]; simp [Real.volume_Ico])
      | simp [Real.volume_pi_Ico]
  have hbox : lam (boxN X u) = 1 := by
    rw [boxN_eq, Set.inter_comm, measure_inter_eq_of_compl_null lam hlam.2.2.1,
      ← Measure.map_apply hkm hbm, hmap, hvol]
  rw [Measure.map_smul c hkm.aemeasurable, hmap, Measure.smul_apply, hbox, smul_eq_mul, mul_one]

theorem covolN_of_four (hInj : KapInj) (hU : HaarUnique) (hL : LebHaar) (hC : CoordCovol) : CovolN := by
  intro D X u μ FdN hμ hF
  obtain ⟨hkm, -, hinj⟩ := coordMeas_of hInj D X u
  have hH := coordHaar_of hU hL D X u μ hμ
  obtain ⟨hAm, hAv⟩ := hC D X u FdN hF
  have hpre : kap X u ⁻¹' (kap X u '' (FdN ∩ X.NinfU u)) ∩ X.NinfU u = FdN ∩ X.NinfU u := by
    ext s
    constructor
    · rintro ⟨⟨t, ht, hts⟩, hs⟩
      rw [← hinj ht.2 hs hts]
      exact ht
    · intro hs
      exact Set.mem_inter (Set.mem_image_of_mem _ hs) hs.2
  have h2 := measure_inter_eq_of_compl_null μ hμ.2.2.1 (kap X u ⁻¹' (kap X u '' (FdN ∩ X.NinfU u)))
  rw [hpre] at h2
  have h3 : μ.map (kap X u) (kap X u '' (FdN ∩ X.NinfU u)) = μ (FdN ∩ X.NinfU u) := by
    rw [Measure.map_apply hkm hAm]
    exact h2.symm
  rw [hH, Measure.smul_apply, hAv, smul_eq_mul] at h3
  rw [← measure_inter_eq_of_compl_null μ hμ.2.2.1 FdN, ← h3]
  exact mul_comm _ _

end Formalism.L2.SG.Pf.LsNc5
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.LocalSpans

theorem summand_localization : SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 h𝔭 Λ ⟨L, hL, rfl⟩
  let W := Submodule.span K (L : Set V)
  let i := W.subtype.restrictScalars (𝓞 K)
  let L' := L.comap i
  have hmap : L'.map i = L := by
    apply Submodule.map_comap_eq_self
    change L ≤ LinearMap.range (W.restrictScalars (𝓞 K)).subtype
    rw [Submodule.range_subtype]
    exact fun _ hx => Submodule.subset_span hx
  have hfull : Submodule.IsFullLattice K L' := by
    have hfg : L'.FG := Submodule.fg_of_fg_map_injective i Subtype.val_injective
      (hmap.symm ▸ hL.fg)
    letI : Submodule.IsLattice K L' := Submodule.IsLattice.of_fg K hfg
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
    have himage : W.subtype '' (L' : Set W) = (L : Set V) := by
      rw [← hmap, Submodule.map_coe]
      rfl
    rw [Submodule.map_span, himage, Submodule.map_top, Submodule.range_subtype]
  let X' := X.comap W.subtype
  let Lloc := UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 L'
  obtain ⟨p, hpX, hpId, hpL⟩ :=
    UpperTheory.Reformulated.B.SummandLocalization.summand_localization
      K F W X' 𝔭 h𝔭 Lloc ⟨L', hfull, rfl⟩
  let N := (LinearMap.ker p).map W.subtype
  have hNX : Disjoint N X := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨w, hw, rfl⟩ hx
    have hzero : p w = 0 := hw
    rw [hpId w hx] at hzero
    exact congrArg Subtype.val hzero
  obtain ⟨Y, hNY, hYX⟩ := hNX.exists_isCompl
  let π := X.projection Y hYX.symm
  have hπ (w : W) : π w = (p w : V) := by
    have hdiff : (w : V) - (p w : V) ∈ Y := hNY ⟨w - p w, by
      change p (w - p w) = 0
      rw [map_sub, hpId _ (hpX w), sub_self], rfl⟩
    have he := Submodule.projection_apply_of_mem_right hYX.symm hdiff
    change π ((w : V) - (p w : V)) = 0 at he
    have hp : (p w : V) ∈ X := hpX w
    have hproj : π (p w : V) = (p w : V) :=
      Submodule.projection_apply_of_mem_left hYX.symm hp
    rwa [map_sub, hproj, sub_eq_zero] at he
  refine ⟨π, Submodule.projection_apply_mem hYX.symm,
    fun _ hx => Submodule.projection_apply_of_mem_left hYX.symm hx, ?_⟩
  letI := h𝔭.isPrime
  intro y hy
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  have ht0 : t ≠ 0 := fun ht0 => ht (ht0 ▸ 𝔭.zero_mem)
  let a := algebraMap (𝓞 F) (𝓞 K) t
  have ha : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h
    apply ht0
    apply RingOfIntegers.algebraMap.injective F K
    apply (RingOfIntegers.coe_injective)
    simpa [a] using h
  have hyW : y ∈ W := by
    have hs : algebraMap (𝓞 K) K a • y ∈ W := by
      rw [algebraMap_smul]
      exact Submodule.subset_span hty
    have h := W.smul_mem (algebraMap (𝓞 K) K a)⁻¹ hs
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h
  let w : W := ⟨y, hyW⟩
  have hwL : w ∈ Lloc := (LocalSpans.mem_locF 𝔭 L' w).2 ⟨t, ht, hty⟩
  rw [show y = (w : V) from rfl, hπ w]
  obtain ⟨u, hu, hpu⟩ := (LocalSpans.mem_locF 𝔭 L' (p w)).1 (hpL w hwL)
  exact (LocalSpans.mem_locF 𝔭 L (p w : V)).2 ⟨u, hu, hpu⟩

end Formalism.L2.SG.Pf.G6
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcS.LT

def SplitStr : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)), IsCMExt F E σ → ¬ IsField (Fv F v ⊗[F] E) →
    ∃ π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v,
      (∀ s, π₁ (sigR (Fv F v) σ s) = π₂ s) ∧ (∀ s, π₂ (sigR (Fv F v) σ s) = π₁ s) ∧
      (∀ c : Fv F v, π₁ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = c ∧
        π₂ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = c) ∧
      (∀ s t, π₁ s = π₁ t → π₂ s = π₂ t → s = t) ∧
      (∀ p q : Fv F v, ∃ s, π₁ s = p ∧ π₂ s = q)

end Formalism.L2.SG.Pf.NcS.LT
end
end
