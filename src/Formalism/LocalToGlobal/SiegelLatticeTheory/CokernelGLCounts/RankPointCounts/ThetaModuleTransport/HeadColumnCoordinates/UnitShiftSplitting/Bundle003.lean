module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.CoordU
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.DlRSwapZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.EmbeddingSecondComponent
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Bundle002
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.GraphTransport
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DecompU
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.Bundle001
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem unit_gramCU {f f' : Fin (r + 1) → V} {T T' : F}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hGd : IsUnit (H.Gdet f f' T T')) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  rw [gramC_eq H f f' T T' hF hF', Matrix.det_transpose]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD1
  have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
  have : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s := by
    rw [← hdet, mul_assoc, hs, mul_one]
  rw [this]
  exact hGd.mul hsu

theorem unit_gramHU {g : SplitG M.L} (hs : M.split = some g) {t : Term V M r}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T')
    (hD1 : IsUnit (H.Dl t.f t.f' (r + 1))) (hGd : IsUnit (H.Gdet t.f t.f' t.T t.T')) :
    IsUnit (gramH H (H.MMfam t)).det := by
  set qi := algebraMap F E ((g.q : F)⁻¹) with hqi
  let B : Matrix (Ix r) (Ix r) E := Matrix.fromBlocks 1 0 (-qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
  have hfam : H.MMfam t = fun i => ∑ j, B i j • Sum.elim t.f t.f' j := by
    rw [mmfam_some H hs]
    funext i
    rcases i with a | a
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm, neg_smul]
      rfl
  have hqu : IsUnit qi := by
    refine ⟨⟨qi, algebraMap F E (g.q : F), qi_mul_q g, ?_⟩, rfl⟩
    rw [mul_comm]; exact qi_mul_q g
  have hB : IsUnit B.det := by
    simp only [B]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
    exact hqu.pow _
  have hV : gramH H (Sum.elim t.f t.f') = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
    rw [gramC_eq H _ _ _ _ hF hF']
    ext i j; rfl
  have hG := unit_gramCU H hF hF' hD1 hGd
  rw [hfam, gramH_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hV]
  have hBc : IsUnit (B.map M.L.cj).det := by
    have : (B.map M.L.cj).det = M.L.cj B.det := by
      rw [show (B.map M.L.cj) = (M.L.cj : E →+* E).mapMatrix B from rfl, ← RingHom.map_det]; rfl
    rw [this]; exact hB.map _
  exact (hB.mul hG).mul hBc

theorem gdet_eq (f f' : Fin (r + 1) → V) (T T' : F) :
    H.Gdet f f' T T' = H.Dl f f' (r + 1) * M.L.cj (H.Dl f f' (r + 1)) -
      algebraMap F E (T * T') * (H.Dl f f' r * M.L.cj (H.Dl f f' r)) := rfl

theorem gdet_swap (f f' : Fin (r + 1) → V) (T T' : F) : H.Gdet f' f T' T = H.Gdet f f' T T' := by
  rw [gdet_eq, gdet_eq, dl_swap_full, dl_swap_r, M.L.cj_cj, M.L.cj_cj, mul_comm T' T]
  ring

theorem gamR_sepU {g : SplitG M.L} {t₁ : Term V M r} {f₂ f₂' : Fin (r + 1) → V}
    (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r))
    (hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T')) (hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T'))
    (hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1))
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂')
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW f₂ ⟨_, z_mem H f₂ t₁.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW f₂ ⟨_, omP_mem H f₂ f₂' hg₂.2.2.2.1⟩)
    (hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW f₂' ⟨_, z_mem H f₂' t₁.T' hg₂.2.2.1⟩)
    (ho' : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW f₂' ⟨_, omP_mem H f₂' f₂ (unit_swap H f₂ f₂' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ GamR H t₁ (algebraMap F E (g.q : F)),
      ∀ p₂ ∈ GamR H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) (algebraMap F E (g.q : F)),
      PcG H hg₂ p₂.2.2.1 = PcG H hg₁ p.2.2.1 → PcG' H hg₂ p₂.2.2.2 = PcG' H hg₁ p.2.2.2 →
      p₂.2.2.1 = φ p.2.2.1 ∧ p₂.2.2.2 = φ' p.2.2.2 := by
  rintro _ ⟨u₁, u₁', u₁'', hu₁, hu₁', -, rfl⟩ _ ⟨u₂, u₂', u₂'', hu₂, hu₂', -, rfl⟩ hc hc'
  simp only [PcG, PcG', coordW_mk, Prod.mk.injEq] at hc hc'
  have hν := nu_eq H t₁.f t₁.f' f₂ f₂' t₁.T' hg₁.2.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1 hrel
  have hrel' : H.Dl t₁.f' t₁.f r * H.Dl f₂' f₂ (r + 1) = H.Dl f₂' f₂ r * H.Dl t₁.f' t₁.f (r + 1) := by
    rw [dl_swap_r H t₁.f t₁.f', dl_swap_full H f₂ f₂', dl_swap_r H f₂ f₂', dl_swap_full H t₁.f t₁.f',
      ← map_mul, ← map_mul, hrel]
  have hν' := nu_eq H t₁.f' t₁.f f₂' f₂ t₁.T hg₁.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1)
    (unit_swap H _ _ hg₂.2.2.2.1) hrel'
  constructor
  · exact mkW_transport H hg₁.2.1 hg₁.2.2.1 hg₂.2.1 hg₂.2.2.1 hg₁.2.2.2.1 hg₂.2.2.2.1
      (by rw [← gdet_eq]; exact hG₁) (by rw [← gdet_eq]; exact hG₂) hν φ hz ho ⟨u₁, hu₁⟩
      (mem_span_of_sharpG H hg₁ u₁) ⟨u₂, hu₂⟩ (mem_span_of_sharpG H hg₂ u₂) hc.1 hc.2
  · exact mkW_transport H hg₁.2.2.1 hg₁.2.1 hg₂.2.2.1 hg₂.2.1 (unit_swap H _ _ hg₁.2.2.2.1)
      (unit_swap H _ _ hg₂.2.2.2.1)
      (by rw [← gdet_eq, gdet_swap]; exact hG₁) (by rw [← gdet_eq, gdet_swap]; exact hG₂) hν' φ' hz' ho'
      ⟨u₁', hu₁'⟩ (by rw [span_swap]; exact mem_span_of_sharpG H hg₁ u₁') ⟨u₂', hu₂'⟩
      (by rw [span_swap]; exact mem_span_of_sharpG H hg₂ u₂') hc'.2 hc'.1

end Parts

theorem coordGU_holds : CoordGU := by
  intro F _ _ _ E _ _ _ _ M g hs r n V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hR
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := by
    have hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0 := hyp.1.1.2.2.2.2.1
    apply isUnit_of_cj_fixed g _ hG
    rw [gdet_eq]
    simp only [map_sub, map_mul, M.L.cj_cj, M.L.cj.commutes]
    ring
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have key := gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1))
      (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel
    have hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) := hU2.mul (hU2.map M.L.cj)
    have : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' *
        (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))) := by
      rw [gdet_eq, key]; exact hB.mul (by rw [← gdet_eq]; exact hG₁)
    exact isUnit_of_mul_isUnit_left this
  have hg₁ : GoodG H g t₁ := ⟨hs, hF₁, hF₁', dl_succ_unit hyp,
    unit_gramHU H hs hF₁ hF₁' (dl_succ_unit hyp) hG₁⟩
  have hg₂ : GoodG H g (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) :=
    ⟨hs, hyp.2.1, hyp.2.2.1, hU2, unit_gramHU H hs hyp.2.1 hyp.2.2.1 hU2 hG₂⟩
  have hTT := (hyp.1.1.2.2.2.2.2 g hs).2.1
  have hI := hyp.2.2.2.1
  have hmm : MMInt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) := mmInt_G H hg₂ hT hTT hR
  have eZ := sends_one H φ _ _ (z_mem H t₁.f t₁.T hF₁) (z_mem H f₂ t₁.T hyp.2.1) hyp.2.2.2.2.1
  have eZ' := sends_one H φ' _ _ (z_mem H t₁.f' t₁.T' hF₁') (z_mem H f₂' t₁.T' hyp.2.2.1)
    hyp.2.2.2.2.2
  have eO := sends_omP H φ hg₁.2.2.2.1 hU2 hI.2.2.2.1
  have eO' := sends_omP' H φ' hg₁.2.2.2.1 hU2 hI.2.2.2.2.1
  have hGam := fun θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =>
    graph_transport4 (PsiG H hg₁).toEquiv (PsiG H hg₂).toEquiv θ.toEquiv φ φ' (PcG H hg₁) (PcG H hg₂)
      (PcG' H hg₁) (PcG' H hg₂) (GamR H t₁ (algebraMap F E (g.q : F))) (GamR H _ (algebraMap F E (g.q : F)))
      _ _ (gamR_image H hg₁) (gamR_image H hg₂)
      (coordW_comp H φ hI.1 _ _ _ _ _ _ _ _ eZ eO)
      (coordW_comp H φ' hI.2.1 _ _ _ _ _ _ _ _ eO' eZ')
      (gamR_sepU H hg₁ hg₂ hG₁ hG₂ hrel φ φ' eZ eO eZ' eO')
  have key : ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r),
      θ ∈ Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ↔
        (PsiG H hg₁).symm.trans (θ.trans (PsiG H hg₂)) ∈
          ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹))
            (H.Zhat t₁.f t₁.f') (H.Zhat f₂ f₂') (algebraMap F E t₁.T) (algebraMap F E t₁.T') := by
    intro θ
    constructor
    · rintro ⟨_, _, hD', _, hG⟩
      exact ⟨(isomD_iffG H hg₁ hg₂ θ).1 hD', (hGam θ).1 (hG g hs)⟩
    · rintro ⟨hD', hG⟩
      refine ⟨hU2, hmm, (isomD_iffG H hg₁ hg₂ θ).2 hD', fun h => ?_, fun g' hg' => ?_⟩
      · rw [hs] at h; cases h
      · rw [hs] at hg'
        cases hg'
        exact (hGam θ).2 hG
  refine Nat.card_congr
    { toFun := fun θ => ⟨(PsiG H hg₁).symm.trans (θ.1.trans (PsiG H hg₂)), (key θ.1).1 θ.2⟩
      invFun := fun θc => ⟨(PsiG H hg₁).trans (θc.1.trans (PsiG H hg₂).symm), (key _).2 (by
        convert θc.2 using 1
        ext x
        simp)⟩
      left_inv := fun θ => by
        apply Subtype.ext; apply LinearEquiv.ext; intro x; simp
      right_inv := fun θc => by
        apply Subtype.ext; apply LinearEquiv.ext; intro x; simp }

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def ind (r : ℕ) (a b : Fin (r + 1)) : F := if a = Fin.last r ∧ b = Fin.last r then 1 else 0

theorem e_cor (x : E) (a b : Fin (r + 1)) :
    g.e (cor r a b x) = (ind r a b * (g.e x).1, ind r a b * (g.e x).2) := by
  unfold cor ind; split_ifs <;> simp <;> rfl

theorem e_cjR (x : E) : g.e ((M.L.cj : E →+* E) x) = ((g.e x).2, (g.e x).1) := g.e_cj x

theorem e_cjA (x : E) : g.e (M.L.cj x) = ((g.e x).2, (g.e x).1) := g.e_cj x

theorem e_gram (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (i j : Ix r) :
    g.e (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T') i j) =
      match i, j with
      | Sum.inl a, Sum.inl b => (ind r a b * (-T), ind r a b * (-T))
      | Sum.inl a, Sum.inr b => ((g.q : F)⁻¹ * ((g.e (Zh a b)).2 + ind r a b * T),
          (g.q : F)⁻¹ * ((g.e (Zh a b)).1 + ind r a b * T))
      | Sum.inr a, Sum.inl b => ((g.q : F)⁻¹ * ((g.e (Zh b a)).1 + ind r a b * T),
          (g.q : F)⁻¹ * ((g.e (Zh b a)).2 + ind r a b * T))
      | Sum.inr a, Sum.inr b => ((g.q : F)⁻¹ * (g.q : F)⁻¹ *
            (-(g.e (Zh b a)).1 - (g.e (Zh a b)).2 - ind r a b * (T + T')),
          (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(g.e (Zh b a)).2 - (g.e (Zh a b)).1 - ind r a b * (T + T'))) := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [gramG, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, map_mul, map_add, map_sub, map_neg, e_cor,
      Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg, e_cjR, e_cjA] <;>
    refine Prod.ext ?_ ?_ <;> simp [e_cjR, e_cjA] <;> ring

theorem sum_ind_l (x : Fin (r + 1) → F) (b : Fin (r + 1)) :
    ∑ a, x a * ind r a b = if b = Fin.last r then x (Fin.last r) else 0 := by
  unfold ind
  by_cases hb : b = Fin.last r
  · subst hb; simp
  · simp [hb]

variable (hs : M.split = some g)

def mOf1 (c : Ix r → M.L.O) : Fin (r + 1) → M.R :=
  fun a => rOf hs (c1 g (c (Sum.inr a))) (-(c1 g (c (Sum.inl a))))

def mOf2 (c : Ix r → M.L.O) : Fin (r + 1) → M.R :=
  fun a => rOf hs (c2 g (c (Sum.inr a))) (-(c2 g (c (Sum.inl a))))

theorem e_llMap (Z : M.Mat (r + 1)) (TT : M.R) (m : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    g.e ((llMap hs Z TT m b : M.R) : E) =
      (∑ a, (g.e (Z.Z b a : E)).1 * (g.e (m a : E)).1 -
          (if b = Fin.last r then (g.e (TT : E)).1 *
            (((g.e (m (Fin.last r) : E)).1 - (g.e (m (Fin.last r) : E)).2) / (g.q : F)) else 0),
        ∑ a, (g.e (Z.Z b a : E)).2 * (g.e (m a : E)).2 -
          (if b = Fin.last r then (g.e (TT : E)).2 *
            (((g.e (m (Fin.last r) : E)).1 - (g.e (m (Fin.last r) : E)).2) / (g.q : F)) else 0)) := by
  by_cases hb : b = Fin.last r
  · subst hb
    refine Prod.ext ?_ ?_ <;>

      simp [llMap, Matrix.mulVec, dotProduct, map_sum, Prod.fst_sum, Prod.snd_sum, e_dgR, trO_coe]
  · refine Prod.ext ?_ ?_ <;>

      simp [hb, llMap, Matrix.mulVec, dotProduct, map_sum, Prod.fst_sum, Prod.snd_sum, e_dgR, trO_coe]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

def ScaleChoiceP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F),
    (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) → (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
    T ∈ 𝒪[F] →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    ∃ α : E, α * M.L.cj α = 1 ∧ α ∈ M.L.O ∧ (α - 1) * algebraMap F E ((g.q : F)⁻¹) ∈ M.L.O ∧
      ∃ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R,
        Z₁'.map M.R.subtype = HermSp.ZZplusOf M (Zh₁ * dlast r α) T T' ∧
        Z₂'.map M.R.subtype = HermSp.ZZplusOf M (Zh₂ * dlast r α) T T' ∧
        IsUnit (Z₁'.map M.R.subtype).det ∧ IsUnit (Z₂'.map M.R.subtype).det ∧
        IsUnit (HermSp.ZZplusOf M ((Zh₁ * dlast r α).map M.L.cj) T T').det ∧
        IsUnit (HermSp.ZZplusOf M ((Zh₂ * dlast r α).map M.L.cj) T T').det ∧
        Nat.card (IsoMbe Z₁' Z₂') = Nat.card (IsoMbe Z₁ Z₂)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

theorem zz_split (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    HermSp.ZZplusOf M Zh T T' = ZZm g Zh T T' +
      Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F))) := by
  unfold ZZm
  ext a b
  simp only [Matrix.add_apply, Matrix.of_apply, cor]
  split_ifs
  · have h0 : g.e.symm (-T / (g.q : F), T' / (g.q : F)) + g.e.symm (T / (g.q : F), -T' / (g.q : F)) = 0 := by
      rw [← map_add (f := _), Prod.mk_add_mk]
      have e : (-T / (g.q : F) + T / (g.q : F), T' / (g.q : F) + -T' / (g.q : F)) = (0 : F × F) :=
        Prod.ext (by simp [neg_div]) (by simp [neg_div])
      rw [e, map_zero]
    rw [add_assoc, h0, add_zero]
  · simp


include hs in
theorem zz_unit_iff (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    IsUnit (HermSp.ZZplusOf M Zh T T').det ↔
      ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 ∧
        ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
  have hq : ((g.q : F)) ≠ 0 := fun h => g.q_irr.ne_zero (by ext; simpa using h)
  have hcor1 : (Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F)))).map (ph1 g) = Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM r (T / (g.q : F)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, cor, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM]
    split_ifs <;> simp [firstProj_apply]
  have hcor2 : (Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F)))).map (ph2 g) = Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM r (-T' / (g.q : F)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, cor, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM]
    split_ifs <;> simp [secondProj_apply]
  have hd1 : (Zh.map (ph1 g)).det = ph1 g Zh.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hd2 : (Zh.map (ph2 g)).det = ph2 g Zh.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hs1 : ((Zh.map (ph1 g)).submatrix Fin.castSucc Fin.castSucc).det =
      ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]
  have hs2 : ((Zh.map (ph2 g)).submatrix Fin.castSucc Fin.castSucc).det =
      ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]
  have e1 : ph1 g (HermSp.ZZplusOf M Zh T T').det = ((g.q : F)⁻¹) ^ (r + 1) *
      (ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, zz_split, Matrix.map_add _ (map_add _), zzMinus_firstProj_smul hs, hcor1,
      Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.det_add_cornerM]
    have es : ∀ (c : F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F),
        ((c • A).submatrix Fin.castSucc Fin.castSucc).det = c ^ r * (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro c A
      have : (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc := by
        ext i j
        rfl
      rw [this, Matrix.det_smul, Fintype.card_fin]
    rw [Matrix.det_smul, Fintype.card_fin, es, hd1, hs1]
    ring
  have e2 : ph2 g (HermSp.ZZplusOf M Zh T T').det = (-((g.q : F)⁻¹)) ^ (r + 1) *
      (ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, zz_split, Matrix.map_add _ (map_add _), zzMinus_secondProj_transpose hs, hcor2,
      Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.det_add_cornerM]
    have es : ∀ (c : F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F),
        ((c • A).submatrix Fin.castSucc Fin.castSucc).det = c ^ r * (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro c A
      have : (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc := by
        ext i j
        rfl
      rw [this, Matrix.det_smul, Fintype.card_fin]
    have et : ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) F,
        (A.transpose.submatrix Fin.castSucc Fin.castSucc).det = (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro A
      rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    rw [Matrix.det_smul, Fintype.card_fin, es, Matrix.det_transpose, et, hd2, hs2]
    ring
  rw [isUnit_iff_ph (g := g), e1, e2, mul_ne_zero_iff, mul_ne_zero_iff]
  simp only [ne_eq, pow_eq_zero_iff', inv_eq_zero, neg_eq_zero, hq, false_and, not_false_eq_true, true_and]

theorem dlast_det {K : Type} [CommRing K] (δ : K) : (dlast r δ).det = δ := by
  unfold dlast
  rw [Matrix.det_diagonal, Finset.prod_ite_eq']
  simp

theorem head_mul_dlast {K : Type} [CommRing K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (δ : K) :
    (A * dlast r δ).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp [dlast, Matrix.mul_diagonal, Fin.castSucc_ne_last]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end
