module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Development
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.MemSpanOfSharpG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ModularBoundZeroHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Bundle002
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem mem_headCols_iff (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (l : Fin (r + 1) → M.R) :
    l ∈ headCols Z ↔ ∃ w : Fin (r + 1) → M.R, w (Fin.last r) = 0 ∧ Z.mulVec w = l := by
  constructor
  · intro hl
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨Pi.single a.castSucc 1, by simp [(Fin.castSucc_lt_last a).ne], ?_⟩
      rw [← col_eq_mulVec]
    | zero => exact ⟨0, rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w + w', by simp [hw, hw'], Matrix.mulVec_add _ _ _⟩
    | smul s x _ hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨s • w, by simp [hw], Matrix.mulVec_smul _ _ _⟩
  · rintro ⟨w, hw, rfl⟩
    exact mulVec_mem_headCols _ _ hw

theorem llMap_of_last (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (w : Fin (r + 1) → M.R)
    (hw : w (Fin.last r) = 0) : llMap hs Z TT w = Z.Z.mulVec w := by
  show Z.Z.mulVec w - (TT * dgR hs (trO hs (w (Fin.last r)))) • eV r = _
  rw [hw, map_zero, map_zero, mul_zero, zero_smul, sub_zero]

theorem headCols_le_LL (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) {l : Fin (r + 1) → M.R}
    (hl : l ∈ headCols Z.Z) : l ∈ LL hs Z TT := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff Z.Z l).1 hl
  exact ⟨w, llMap_of_last hs Z TT w hw⟩

theorem firstQuotient_eq_zero_iff (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (l : Fin (r + 1) → M.R) :
    mk1 hs Z TT l = 0 ↔ ∃ m, llMap hs Z TT m = l := by
  rw [mk1, QuotientAddGroup.eq_zero_iff]
  rfl

theorem ker_fact (hs : M.split = some g) (T T' : F) (TT : M.R) (hTT : g.e (TT : E) = (T, T'))
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit Zh.det)
    (hG : IsUnit (Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det)))
    (l : Fin (r + 1) → M.R) (h1 : mk1 hs Z TT l = 0) (h2 : laG (ZZm g Zh T T') l = 0) :
    l ∈ headCols Z.Z := by
  obtain ⟨m, rfl⟩ := (firstQuotient_eq_zero_iff hs Z TT l).1 h1
  rw [laG_llMap hs Zh T T' Z hZ hu] at h2
  have hq := q_ne g
  have hd1 := ((isUnit_iff_ph (g := g) _).1 hu).1
  have hd2 := ((isUnit_iff_ph (g := g) _).1 hu).2
  have hG1 := ((isUnit_iff_ph (g := g) _).1 hG).1
  have ecj : ∀ x : E, ph1 g (M.L.cj x) = ph2 g x := fun x => by
    rw [firstProj_apply, secondProj_apply, g.e_cj]; rfl
  have eal1 : ∀ c : F, ph1 g (algebraMap F E c) = c := fun c => by rw [firstProj_apply, AlgEquiv.commutes]; rfl
  have eal2 : ∀ c : F, ph2 g (algebraMap F E c) = c := fun c => by rw [secondProj_apply, AlgEquiv.commutes]; rfl
  have et1 : ph1 g (tau0 g T T') = -T / (g.q : F) := by simp [firstProj_apply]
  have et2 : ph2 g (tau0 g T T') = T' / (g.q : F) := by simp [secondProj_apply]
  have eT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hTT]
  have eT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hTT]
  set a := ph1 g ((m (Fin.last r) : M.R) : E) with ha
  set b := ph2 g ((m (Fin.last r) : M.R) : E) with hb
  have etr : ((trO hs (m (Fin.last r)) : 𝒪[F]) : F) = (a - b) / (g.q : F) := by rw [trO_coe]; rfl
  have H1 := congrArg (ph1 g) h2
  have H2 := congrArg (ph2 g) h2
  simp only [map_sub, map_mul, map_one, map_zero, eal1, eal2, et1, et2, eT1, eT2, etr,
    cornerRatio_firstProj hs Zh T T' hu, cornerRatio_secondProj hs Zh T T' hu] at H1 H2
  rw [← ha] at H1
  rw [← hb] at H2
  have E1 : a * ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * b = 0 := by
    field_simp [hd1, hq] at H1
    linear_combination H1
  have E2 : b * ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * a = 0 := by
    field_simp [hd2, hq] at H2
    linear_combination H2
  have hG1' : ph1 g Zh.det * ph2 g Zh.det - T * T' * (ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det *
      ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0 := by
    simpa [map_sub, map_mul, ecj, eal1] using hG1
  have ha0 : a = 0 := by
    have : a * (ph1 g Zh.det * ph2 g Zh.det - T * T' * (ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det *
        ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det)) = 0 := by
      linear_combination ph2 g Zh.det * E1 - T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * E2
    exact (mul_eq_zero.1 this).resolve_right hG1'
  have hb0 : b = 0 := by
    rw [ha0, mul_zero, add_zero] at E2
    exact (mul_eq_zero.1 E2).resolve_right hd2
  have hm : m (Fin.last r) = 0 := by
    apply Subtype.ext
    apply g.e.injective
    rw [ZeroMemClass.coe_zero, map_zero]
    exact Prod.ext ha0 hb0
  rw [llMap_of_last hs Z TT m hm]
  exact mulVec_mem_headCols _ _ hm

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

private theorem mem_R_of_split_coords_integral_congr (hs : M.split = some g) (x : E) (h1 : (g.e x).1 ∈ 𝒪[F])
    (h2 : (g.e x).2 ∈ 𝒪[F]) (hd : ∃ c : 𝒪[F], (g.e x).1 - (g.e x).2 = (g.q : F) * c) : x ∈ M.R := by
  obtain ⟨c, hc⟩ := hd
  unfold Model.R
  rw [hs]
  refine Subring.mem_comap.2 (Subring.mem_map.2 ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩)
  · rw [RingHom.mem_eqLocus]
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨c, Subtype.ext ?_⟩
    simp [hc, mul_comm]
  · rfl

theorem zsig_mem (hs : M.split = some g) (T T' : F) (c : 𝒪[F]) (hc : T - T' = (g.q : F) ^ 2 * c)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R)
    (hZ : Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (a b : Fin (r + 1)) :
    HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b ∈ M.R := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext (by simpa using h))
  have hmem : HermSp.ZZplusOf M Zh T T' b a ∈ M.R := by
    have := congrFun (congrFun hZ b) a
    simp only [Matrix.map_apply, Subring.coe_subtype] at this
    rw [← this]
    exact (Z b a).2
  obtain ⟨u1, u2, d, hd⟩ := comp_of_mem_R hs hmem
  rw [zz_comp hs] at u1 u2 hd
  dsimp only at u1 u2 hd
  have hT : T = T' + (g.q : F) ^ 2 * c := by linear_combination hc
  by_cases hab : a = Fin.last r ∧ b = Fin.last r
  · simp only [if_pos hab.symm] at u1 u2 hd
    refine mem_R_of_split_coords_integral_congr hs _ ?_ ?_ ⟨d, ?_⟩
    all_goals rw [zz_comp hs]
    all_goals simp only [Matrix.map_apply, g.e_cj, Prod.fst_swap, Prod.snd_swap, if_pos hab]
    · rw [show (g.e (Zh a b)).2 / (g.q : F) - -T / g.q =
          -(-((g.e (Zh a b)).2 / g.q) - T' / g.q) + g.q * c by rw [hT]; field_simp; ring]
      exact add_mem (neg_mem u2) (mul_mem g.q.2 c.2)
    · rw [show -((g.e (Zh b a)).1 / (g.q : F)) - T' / g.q =
          -((g.e (Zh b a)).1 / g.q - -T / g.q) + g.q * c by rw [hT]; field_simp; ring]
      exact add_mem (neg_mem u1) (mul_mem g.q.2 c.2)
    · rw [← hd]
      ring
  · have hba : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h => hab (And.symm h)
    simp only [if_neg hba] at u1 u2 hd
    refine mem_R_of_split_coords_integral_congr hs _ ?_ ?_ ⟨d, ?_⟩
    all_goals rw [zz_comp hs]
    all_goals simp only [Matrix.map_apply, g.e_cj, Prod.fst_swap, Prod.snd_swap, if_neg hab]
    · rw [show (g.e (Zh a b)).2 / (g.q : F) - 0 = -(-((g.e (Zh a b)).2 / g.q) - 0) by ring]
      exact neg_mem u2
    · rw [show -((g.e (Zh b a)).1 / (g.q : F)) - 0 = -((g.e (Zh b a)).1 / g.q - 0) by ring]
      exact neg_mem u1
    · rw [← hd]
      ring

theorem stepZsig0 : StepZsig0 := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT _ hcex Zh Z hZ hu h0
  obtain ⟨c, hc⟩ := hcex
  have hcj : IsUnit (Zh.map M.L.cj).det := by
    rw [det_map_cj]
    exact hu.map M.L.cj
  have hcj0 : ((Zh.map M.L.cj).submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [show (Zh.map M.L.cj).submatrix Fin.castSucc Fin.castSucc =
        (Zh.submatrix Fin.castSucc Fin.castSucc).map M.L.cj from rfl, det_map_cj, h0, map_zero]
  refine ⟨?_, ?_, ?_⟩
  · have hT' : T' ∈ 𝒪[F] := by
      rw [show T' = T - (g.q : F) ^ 2 * c by linear_combination -hc]
      exact sub_mem hT (mul_mem (pow_mem g.q.2 2) c.2)
    refine ⟨⟨g.e.symm (T, T'), mem_R_of_split_coords_integral_congr hs _ ?_ ?_ ⟨g.q * c, ?_⟩⟩, ?_⟩
    · simpa using hT
    · simpa using hT'
    · simp only [AlgEquiv.apply_symm_apply]
      push_cast
      rw [hc]
      ring
    · exact g.e.apply_symm_apply _
  · rw [hZ]
    exact zzplus_det_unit hs Zh T T' hu h0
  · refine ⟨⟨Matrix.of fun a b => ⟨HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b,
      zsig_mem hs T T' c hc Zh Z hZ a b⟩, ?_⟩, ?_⟩
    · have hmap : ((Matrix.of fun a b => (⟨HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b,
          zsig_mem hs T T' c hc Zh Z hZ a b⟩ : M.R)).map M.R.subtype) =
          HermSp.ZZplusOf M (Zh.map M.L.cj) T T' := by
        ext a b
        rfl
      rw [hmap]
      exact zzplus_det_unit hs _ T T' hcj hcj0
    · ext a b
      rfl

theorem thetaMbe0_of_detG_coordG_splitIsoCount (h0 : DetG) (h1 : CoordG) (h2 : SplitIsometryCountIntegral) (M : Model F E) (r n : ℕ) :
    ThetaMbe0 M r n true := by
  intro hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hmode
  have hD2 : H.Dl f₂ f₂' r = 0 := dl_zero_two hyp hD
  have hh1 : ((H.Zhat t₁.f t₁.f').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [← dl_eq_det]; exact hD
  have hh2 : ((H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [← dl_eq_det]; exact hD2
  have hU1 : IsUnit (H.Zhat t₁.f t₁.f').det := by
    have := dl_succ_unit hyp
    rwa [dl_full] at this
  have hU2 : IsUnit (H.Zhat f₂ f₂').det := by
    refine h0 F E M g hs r _ t₁.T t₁.T' hh2 ?_
    rw [← e₂]; exact Z₂.unit
  have hR : ∀ a b, HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b ∈ M.R := by
    intro a b
    rw [← e₂]
    exact (Z₂.Z a b).2
  have hsp := hyp.1.1.2.2.2.2.2 g hs
  have hT0 : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  rw [h1 F E M g hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD (by rw [dl_full]; exact hU2) hR]
  exact h2 F E M g hs r t₁.T t₁.T' hT0 hsp.1 hsp.2.1 _ _ Z₁.Z Z₂.Z e₁ e₂ hU1 hU2 hh1 hh2

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
