module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionRankZeroExtRestriction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle575
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle653
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle606
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle673
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle737
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LastSeeSaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem wittExtensionByZero_symplectic_form_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a b : WO S₀ T) :
    symplO S T (d.ext0 T a) (d.ext0 T b) = symplO S₀ T a b := by
  have h := d.hO_ext T 0 0 0 0 a b
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  rw [symplO, symplO, h]

theorem isHalf_mul_right {k l m : ℕ} {e : AE D} {u : Mx D k l} (p : Mx D l m) (hu : IsHalf e u) : IsHalf e (u ⬝ p) := by
  intro i j
  show e * ∑ r, u i r * p r j = ∑ r, u i r * p r j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [← mul_assoc, hu i r]

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


open GlobalTheory.FinPl.VLast.KernPf (wittCoreRestrictionHom wittCoreRestrictionHom_apply wittDecomposition_rankZero_ext_restriction) in
theorem lastLat_rankZero (hψ : IsStdChar D ψ (-1)) (J : JacL D 0) {X T L'' : HSp D} (o : OrthDec X T L'')
    (Γ : AddSubgroup (WO J.W T)) (ΓL : AddSubgroup (WO J.W₀ (negSp L''))) (ΓX : AddSubgroup (WO J.W₀ X))
    (hX : ∀ u, u ∈ ΓX ↔ J.d.ext0 T (o.resT J.W₀ u).1 ∈ Γ ∧ (show WO J.W₀ (negSp L'') from (o.resT J.W₀ u).2) ∈ ΓL)
    (h₁ : ∃ f, VacG ψ J.W T Γ f ∧ f ≠ 0) (h₂ : ∃ f, VacG ψ J.W₀ (negSp L'') ΓL f ∧ f ≠ 0) :
    LastLat ψ J o Γ ΓL ΓX := by
  have s0 := @GlobalTheory.SplitScalar.symplO_zero_right D
  have mA : ∀ a : WO J.W₀ T, J.d.ext0 T a ∈ Γ → (o.resT J.W₀).symm (a, 0) ∈ ΓX := fun a ha => by
    rw [hX, AddEquiv.apply_symm_apply]; exact ⟨ha, zero_mem _⟩
  have mB : ∀ b : WO J.W₀ L'', (show WO J.W₀ (negSp L'') from b) ∈ ΓL → (o.resT J.W₀).symm (0, b) ∈ ΓX := fun b hb => by
    rw [hX, AddEquiv.apply_symm_apply]; exact ⟨by rw [map_zero]; exact zero_mem _, hb⟩
  have n : ∀ a b : WO J.W₀ L'', ψ (symplO J.W₀ L'' a b) = 1 → ψ (symplO J.W₀ (negSp L'') a b) = 1 := fun a b h => by
    have e : symplO J.W₀ (negSp L'') a b = -symplO J.W₀ L'' a b := by
      simp only [symplO, hO, negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
    rw [e, ← GlobalTheory.CjNeg.conj_psi hψ, h, map_one]
  have hA : ∀ e (u : WO J.W₀ T), IsHalf e u → IsHalf e ((o.resT J.W₀).symm (u, 0)) := fun e u h => by
    rw [o.resT_symm_apply, Matrix.mul_zero, add_zero]; exact GlobalTheory.AscInh.isHalf_mul _ h
  have hB : ∀ e (u : WO J.W₀ L''), IsHalf e u → IsHalf e ((o.resT J.W₀).symm (0, u)) := fun e u h => by
    rw [o.resT_symm_apply, Matrix.mul_zero, zero_add]; exact GlobalTheory.AscInh.isHalf_mul _ h
  have back : ∀ u : WO J.W T, J.d.ext0 T (wittCoreRestrictionHom J.d T u) = u := wittDecomposition_rankZero_ext_restriction J.d T
  refine ⟨fun (w : WO J.W₀ X) hw => ⟨⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun (u : WO J.W₀ L'') hu => n _ _ ?_,
    fun e he (u : WO J.W₀ L'') hu hh => n _ _ ?_⟩, ?_⟩
  · have hu' : J.d.ext0 T (wittCoreRestrictionHom J.d T u) ∈ Γ := by rw [back]; exact hu
    have := hw.1 _ (mA _ hu')
    rw [o.symplO_resT, map_nsmul (o.resT J.W₀), AddEquiv.apply_symm_apply, Prod.smul_snd, nsmul_zero, s0, add_zero] at this
    rw [← back u, ← map_nsmul, wittExtensionByZero_symplectic_form_eq]
    exact this
  · have hu' : J.d.ext0 T (wittCoreRestrictionHom J.d T u) ∈ Γ := by rw [back]; exact hu
    have := hw.2 e he _ (mA _ hu') (hA e _ (isHalf_mul_right _ hh))
    rw [o.symplO_resT, AddEquiv.apply_symm_apply, s0, add_zero] at this
    rw [← back u, wittExtensionByZero_symplectic_form_eq]
    exact this
  · have := hw.1 _ (mB u hu)
    rwa [o.symplO_resT, map_nsmul (o.resT J.W₀), AddEquiv.apply_symm_apply, Prod.smul_fst, nsmul_zero, s0, zero_add] at this
  · have := hw.2 e he _ (mB u hu) (hB e u hh)
    rwa [o.symplO_resT, AddEquiv.apply_symm_apply, s0, zero_add] at this
  · obtain ⟨f₁, a₁, b₁⟩ := h₁
    obtain ⟨f₂, a₂, b₂⟩ := h₂
    refine ⟨f₁, f₂, a₁, a₂, b₁, b₂, ?_⟩
    show VacG ψ J.W₀ X _ (o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f₂))
    refine ⟨o.isThetaFunO_boxT (GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero J.d T a₁.1) (GlobalTheory.CjNeg.theta_negT' hψ a₂.1),
      fun u hu => ?_, fun e he u hu hh => ?_⟩
    · obtain ⟨h1, h2⟩ := (hX u).1 hu
      rw [o.heisO_boxT, map_nsmul (o.resT J.W₀), Prod.smul_fst, Prod.smul_snd, GlobalTheory.RankZeroVac.heisenbergOperator_wittExtendByZero,
        map_nsmul (J.d.ext0 T), a₁.2.1 _ h1, GlobalTheory.CjNeg.heis_negT' hψ]
      exact congrArg (fun f => o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (a₂.2.1 _ h2)
    · obtain ⟨h1, h2⟩ := (hX u).1 hu
      rw [o.heisO_boxT, GlobalTheory.RankZeroVac.heisenbergOperator_wittExtendByZero,
        a₁.2.2 e he _ h1 (GlobalTheory.RankZeroVac.isHalf_wittHyperbolicExtendByZero_apply J.d T (GlobalTheory.AscInh.isHalf_mul o.pA hh)), GlobalTheory.CjNeg.heis_negT' hψ]
      exact congrArg (fun f => o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))
        (a₂.2.2 e he _ h2 (GlobalTheory.AscInh.isHalf_mul o.pB hh))

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

theorem latCore_zero_split : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (u : WO (G.V (.core 1)) (G.V (.core 0))), u ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) (F.oz.resT _ u).1 ∈ latRow G 0 ∧ (F.oz.resT _ u).2 ∈ lineLat F 0 := by
  intro D q T L μ0 hL sc G W M hM F hF h u
  have e1 := GlobalTheory.T.orthogonal_projection_preserves_depth_lattice D q T L μ0 hL sc G W M hM F hF
  have e2 := GlobalTheory.T.depthLatticeGridCore_iff_firstRow_extByZero D q T L μ0 hL sc G W M hM F hF h
  have hu : F.oz.jA ⬝ (F.oz.pA ⬝ u) + F.oz.jB ⬝ (F.oz.pB ⬝ u) = u := (F.oz.resT _).symm_apply_apply u
  have hl : F.oz.pB ⬝ u ∈ lineLat F 0 ↔ (F.oz.resT _).symm (0, F.oz.pB ⬝ u) ∈ latCore G 0 := Iff.rfl
  show u ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) (F.oz.pA ⬝ u) ∈ latRow G 0 ∧ F.oz.pB ⬝ u ∈ lineLat F 0
  rw [hl, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB ⬝ (F.oz.pB ⬝ u)), ← e2]
  constructor
  · intro hm
    have ha := e1 u hm
    refine ⟨ha, ?_⟩
    have hb : F.oz.jB ⬝ (F.oz.pB ⬝ u) = u - F.oz.jA ⬝ (F.oz.pA ⬝ u) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hu
    rw [hb]; exact sub_mem hm ha
  · rintro ⟨ha, hb⟩
    rw [← hu]
    exact add_mem ha hb

end GlobalTheory.LastSeeSaw

namespace GlobalTheory.LastSeeSaw

theorem lastLat_std : OnStd fun {D} _ _ _ {G} W F => (∀ ρ, 2 * ρ + 2 ≤ D.R.m → ∃ Φ₀, VacG W.ψ _ _ (lineLat F ρ) Φ₀ ∧ Φ₀ ≠ 0) ∧ ∀ (v : CoreVol G) h, LastLat W.ψ (F.jac v 0 h) F.oz (latRow G 0) (lineLat F 0) (latCore G 0) := by
  intro D q T L μ0 hL sc G W M hM F hF
  have hψ := W.ψ_std
  have hline0 : ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := GlobalTheory.T.exists_ne_zero_vacuum_besselLineLattice_rankZero D q T L μ0 hL sc G W M hM F hF
  refine ⟨fun ρ hρ => ?_, fun v h => ?_⟩
  · rcases ρ with _ | σ
    · exact hline0
    · obtain ⟨-, -, h3⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D q T L μ0 hL sc G W M hM F hF
      exact GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ hψ _ _ _ _ (G.sp.P_is (2 * (σ + 1) + 1) (by omega)).sd (h3 (σ + 1)) _ le_rfl
  · have hm : 0 < D.R.m := by omega
    have hdep := dep_vac W 0 hm
    refine lastLat_rankZero hψ (F.jac v 0 h) F.oz _ _ _ (latCore_zero_split D q T L μ0 hL sc G W M hM F hF h) ?_ hline0
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (W.vac 0), ⟨GlobalTheory.CjNeg.theta_negS' hψ hdep.1, fun u hu => ?_, fun e he u hu hh => ?_⟩, ?_⟩
    · exact (GlobalTheory.CjNeg.heis_negS' hψ _ _ _ _).trans (congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id) (hdep.2.1 u hu))
    · exact (GlobalTheory.CjNeg.heis_negS' hψ _ _ _ _).trans (congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id) (hdep.2.2 e he u hu hh))
    · intro h0
      apply GlobalTheory.SeeSaw.Inh.vac_ne_zero (W.vac_is 0 hm)
      funext w
      have h1 := congrFun h0 w
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Pi.zero_apply, map_eq_zero] at h1
      exact (map_eq_zero (starRingEnd ℂ)).1 h1

end GlobalTheory.LastSeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.BidualLattice

variable {D : D7}



theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  unfold latO
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _)]
    refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
    funext i j
    simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]
  · rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _)]
    refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
    funext i j
    simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem extY_jY_mem {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {LS : Lat S} {L₀ : Lat S₀} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (hm : ∀ v, MonoAt d LS L₀ v) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    d.extY T (u * d.jY) ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hS hT] at hu ⊢
  refine ⟨GlobalTheory.AscFinWit.mxAt_mul' (GlobalTheory.AscFinWit.mxAt_mul' hu.1 _) _, fun y hy => ?_⟩
  have e : (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from d.extY T (u * d.jY)) *ᵥ y =
      (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) *ᵥ (d.jY *ᵥ (d.pY *ᵥ y)) := by
    simp only [HypDec.extY_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  refine hu.2 _ ?_
  rw [GlobalTheory.FinPlLoc.part_lat _ _ _ _ hS.1] at hy ⊢
  refine ⟨fun i => ?_, fun v _ c hc => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _
      (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hy.1 l))
  · have hs := ((hm v) (c • y)).1 (hy.2 v trivial c hc)
    have e1 : c • (d.jY *ᵥ (d.pY *ᵥ y)) = ∑ i, GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ (c • y)) i) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e1]
    exact sum_mem fun i _ => hs.2.1 i

theorem dual_extX {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {LS : Lat S} {L₀ : Lat S₀} {LT : Lat T}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hm : ∀ v, MonoAt d LS L₀ v) {a : Mx D T.rank ρ} (ha : MxAt (fun _ => True) a) :
    d.extX T a ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
      ∀ a', d.extY T a' ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) →
        ψ (symplO S T (d.extX T a) (d.extY T a')) = 1 := by
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT _ _ (GlobalTheory.AscFinWit.mxAt_mul' ha d.pX)).trans ?_
  exact ⟨fun h _ ha' => h _ ha', fun h u hu =>
    (congrArg ψ (GlobalTheory.AscFinWit.symplO_extX d T a u)).trans (h _ (extY_jY_mem d hS hT hm hu))⟩

theorem mxAt_of_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {a' : Mx D T.rank ρ}
    (h : MxAt (fun _ => True) (d.extY T a')) : MxAt (fun _ => True) a' := by
  simpa only [HypDec.extY_apply, Matrix.mul_assoc, d.pY_jY, Matrix.mul_one] using GlobalTheory.AscFinWit.mxAt_mul' h d.jY

end GlobalTheory.AscFin.BidualLattice

namespace GlobalTheory.AscFin.BidualLattice

theorem bidual_main (hin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i) (hout : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latBig G i, e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)))) : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ := by
  have hI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting
  unfold OnStd at hI ⊢
  delta All at hI ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h a ha H
  have hJ := hI D hD T L μ0 hL sc G W M hM F hF
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hSV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by cases hj)).sd
  have hSW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (GlobalTheory.CosetRow.selfDual_chi hL G (2 * ρ + 1) hi).2
  have hbig : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0))) :=
    (hJ.1 (2 * ρ + 1) hi).2.2.2
  have hmono : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((hJ.2.1 ρ h).2.1 v).1
  have hrowO : ∀ u ∈ latRow G (2 * ρ + 1), u ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := fun u hu => by
    have h0 := hu.1
    rwa [BidualLattice.latO_negSp] at h0
  have hA2 : ∀ a', MxAt (fun _ => True) a' → (∀ b, (F.dB ρ h).extX _ b ∈ latRow G (2 * ρ + 1) →
      W.ψ (symplO _ _ ((F.dB ρ h).extX _ b) ((F.dB ρ h).extY _ a')) = 1) →
      W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1 :=
    fun a' h1 h2 => H a' (AddSubgroup.subset_closure ⟨h1, h2⟩)
  have hO : (F.dB ρ h).extX _ a ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := by
    refine (BidualLattice.dual_extX (F.dB ρ h) hψ hSV hSW hmono ha).2 fun a' ha' => ?_
    refine hA2 a' (BidualLattice.mxAt_of_extY _ (GlobalTheory.FinPl.LatMem.latO_mxAt ha')) fun b hb => ?_
    have hb' := hrowO _ hb
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hSV hSW _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hb')).1 hb' _ ha'
  refine ⟨?_, fun e he => ?_⟩
  · exact (BidualLattice.latO_negSp (G.V (.grid (2 * ρ + 2) 0)) _ _ _ _).ge hO
  · have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    have hsx : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ, (F.dB ρ h).extX _ (e • x) = e • (F.dB ρ h).extX _ x :=
      fun x => by simp only [HypDec.extX_apply, Matrix.smul_mul]
    have hsy : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ, (F.dB ρ h).extY _ (cA D e • x) =
        cA D e • (F.dB ρ h).extY _ x := fun x => by simp only [HypDec.extY_apply, Matrix.smul_mul]
    have hea : MxAt (fun _ => True) (e • a) := fun i j => Ideal.mul_mem_left _ _ (ha i j)
    have hB : (F.dB ρ h).extX _ (e • a) ∈ latBig G (2 * ρ + 1) := by
      refine (BidualLattice.dual_extX (F.dB ρ h) hψ hSV hbig hmono hea).2 fun a' ha' => ?_
      rw [hsx, GlobalTheory.SplitScalar.symplO_smul, ← hsy]
      have ha'f := BidualLattice.mxAt_of_extY _ (GlobalTheory.FinPl.LatMem.latO_mxAt ha')
      refine hA2 _ (fun i j => Ideal.mul_mem_left _ _ (ha'f i j)) fun b hb => ?_
      rw [hsy, ← GlobalTheory.SplitScalar.symplO_smul]
      have hb' := hin hL hD G (2 * ρ + 1) hi e he _ hb
      exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hSV hbig _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hb')).1 hb' _ ha'
    have h2 := hout hL hD G (2 * ρ + 1) hi e he _ hB
    rwa [hsx, smul_smul, hee] at h2

theorem bidual_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ :=
  bidual_main GlobalTheory.T.depthLatticeGridRow_smul_mem_selfDualModulusShift GlobalTheory.T.selfDualModulusShift_half_mem_completedModulusHom

end GlobalTheory.AscFin.BidualLattice

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin



namespace GlobalTheory.TgtCoreSplit

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem finPart_pure (α : Af D.host.F) (e : D.host.E) :
    finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem toEAf_pure (e : D.host.E) :
    toEAf D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  unfold toEAf
  rw [RingHom.comp_apply, finPart_pure]
  rfl

theorem rat_mulVec_pure {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (α : Af D.host.F) (t : Fin n → D.host.E) :
    rat M *ᵥ (fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] t i) =
      fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (M *ᵥ t) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem proj_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, MonoAt d L L₀ v)
    {t : Fin S.rank → D.host.E} (ht : t ∈ L) : (d.i₀ * d.q0) *ᵥ t ∈ L := by
  have hy : (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i) ∈ latV S L (fun _ => True) :=
    AddSubgroup.subset_closure ⟨1, one_mem_intAf, fun v hv => (hv trivial).elim, 1, rfl, t, ht, by
      funext i; rw [one_mul]⟩
  have h2 := GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hL (fun v _ => hm v)
    (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ (fun v _ => hm v) hy)
  have e : d.j0 *ᵥ (d.p0 *ᵥ (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i)) =
      fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((d.i₀ * d.q0) *ᵥ t) i := by
    rw [Matrix.mulVec_mulVec, show d.j0 * d.p0 = rat (d.i₀ * d.q0) by rw [rat_mul]; rfl]
    exact rat_mulVec_pure _ _ _
  rw [e] at h2
  have h3 := (GlobalTheory.Core.Mi.LatMatch.TraceX.latV_iff_hatL S L _ _ (GlobalTheory.FinPlLoc.latV_idAt h2)).1 h2
  simp only [toEAf_pure] at h3
  exact (GlobalTheory.Mem.Col2.PtUniq.mem_iff_hatL (F := D.host.F) hL _).2 h3

theorem mul_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hM : ∀ t ∈ LT, M *ᵥ t ∈ LT) {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : rat M * u ∈ latO S T LS (LT : Set _) P := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply]
    generalize (∑ k, star (s k) * S.gram k j) = c
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem mul_mem_smul_homLat {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ t ∈ Λ', M *ᵥ t ∈ Λ') {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') :
    M * x ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hM _ (hy z hz)
  · rw [Matrix.mul_add]; exact add_mem ha hb

theorem mul_mem_hatMx {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin m) (Fin m) D.host.E) (hM : ∀ x ∈ N, M * x ∈ N) {u : Mx D m n} (hu : u ∈ hatMx N) :
    rat M * u ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, M * x, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

end GlobalTheory.TgtCoreSplit


open GlobalTheory.TgtCoreSplit in
theorem GlobalTheory.AscFin.latRow_bessel_core_split : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ w)) ∈ latRow G (2 * ρ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h w hw
  have hI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hm : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((hI.2.1 ρ h).2.1 v).2
  have hL1 : Submodule.IsLattice D.host.E (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * ρ + 1) 0) ⟨by omega, Nat.zero_le _⟩).sd.1
  have hL0 : Submodule.IsLattice D.host.E (G.Λ (.core (2 * ρ + 1))) :=
    (node_isV G hL (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega)).sd.1
  have hP : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) *ᵥ t ∈ G.Λ (.grid (2 * ρ + 1) 0) :=
    fun t ht => proj_mem _ hL1 hL0 hm ht
  have e : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 * w)) =
      rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, rat_mul]
    show (F.dJ ρ h).j0 * ((F.dJ ρ h).p0 * w) * (F.dB ρ h).p0 = (F.dJ ρ h).j0 * (F.dJ ρ h).p0 * (w * (F.dB ρ h).p0)
    simp only [Matrix.mul_assoc]
  have hw' : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T))) := hw
  rw [e]
  show (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T)))
  refine ⟨mul_mem_latO _ hP hw'.1, fun a ha => ?_⟩
  rw [← Matrix.mul_smul]
  exact mul_mem_hatMx _ _ (fun x hx => mul_mem_smul_homLat _ _ hP hx) (hw'.2 a ha)

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.standard_lattice_off_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  first | exact @GlobalTheory.AscFin.stdAt_pcBF | exact GlobalTheory.AscFin.stdAt_pcBF | (intros; apply GlobalTheory.AscFin.stdAt_pcBF <;> assumption)
end
