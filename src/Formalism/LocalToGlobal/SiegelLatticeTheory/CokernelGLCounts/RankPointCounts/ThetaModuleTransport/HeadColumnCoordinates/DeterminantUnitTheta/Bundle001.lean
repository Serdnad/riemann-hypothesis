module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.MemSpanOfSharpG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Bundle002
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.DlRSwapZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.GraphTransport
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.TraceUniformizerEqNegOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaGC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.Bundle001
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

section Transport

theorem graph_transport4 {D₁ D₂ Dc₁ Dc₂ W₁ W₂ W₁' W₂' P P' : Type} (Ψ₁ : D₁ ≃ Dc₁) (Ψ₂ : D₂ ≃ Dc₂)
    (θ : D₁ ≃ D₂) (φ : W₁ → W₂) (φ' : W₁' → W₂') (Pc₁ : W₁ → P) (Pc₂ : W₂ → P) (Pc₁' : W₁' → P')
    (Pc₂' : W₂' → P') (Γ₁ : Set (D₁ × D₁ × W₁ × W₁')) (Γ₂ : Set (D₂ × D₂ × W₂ × W₂'))
    (Γc₁ : Set (Dc₁ × Dc₁ × P × P')) (Γc₂ : Set (Dc₂ × Dc₂ × P × P'))
    (h1 : (fun p => (Ψ₁ p.1, Ψ₁ p.2.1, Pc₁ p.2.2.1, Pc₁' p.2.2.2)) '' Γ₁ = Γc₁)
    (h2 : (fun p => (Ψ₂ p.1, Ψ₂ p.2.1, Pc₂ p.2.2.1, Pc₂' p.2.2.2)) '' Γ₂ = Γc₂)
    (hP : ∀ w, Pc₂ (φ w) = Pc₁ w) (hP' : ∀ w, Pc₂' (φ' w) = Pc₁' w)
    (hinj : ∀ p ∈ Γ₁, ∀ q ∈ Γ₂, Pc₂ q.2.2.1 = Pc₁ p.2.2.1 → Pc₂' q.2.2.2 = Pc₁' p.2.2.2 →
      q.2.2.1 = φ p.2.2.1 ∧ q.2.2.2 = φ' p.2.2.2) :
    ((fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' Γ₁ = Γ₂) ↔
      ((fun p => (Ψ₂ (θ (Ψ₁.symm p.1)), Ψ₂ (θ (Ψ₁.symm p.2.1)), p.2.2.1, p.2.2.2)) '' Γc₁ = Γc₂) := by
  subst h1 h2
  constructor
  · intro h
    rw [← h, Set.image_image, Set.image_image]
    congr 1
    funext p
    simp [hP, hP']
  · intro h
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hc : (Ψ₂ (θ p.1), Ψ₂ (θ p.2.1), Pc₁ p.2.2.1, Pc₁' p.2.2.2) ∈
          (fun p => (Ψ₂ p.1, Ψ₂ p.2.1, Pc₂ p.2.2.1, Pc₂' p.2.2.2)) '' Γ₂ := by
        rw [← h]
        exact ⟨_, ⟨p, hp, rfl⟩, by simp⟩
      obtain ⟨q, hq, hqe⟩ := hc
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨e1, e2, e3, e4⟩ := hqe
      obtain ⟨f1, f2⟩ := hinj p hp q hq e3 e4
      have hpq : ((θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2) : D₂ × D₂ × W₂ × W₂') = q :=
        Prod.ext (Ψ₂.injective e1).symm (Prod.ext (Ψ₂.injective e2).symm (Prod.ext f1.symm f2.symm))
      show ((θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2) : D₂ × D₂ × W₂ × W₂') ∈ Γ₂
      rw [hpq]
      exact hq
    · intro hq
      have hc : (Ψ₂ q.1, Ψ₂ q.2.1, Pc₂ q.2.2.1, Pc₂' q.2.2.2) ∈
          (fun p => (Ψ₂ (θ (Ψ₁.symm p.1)), Ψ₂ (θ (Ψ₁.symm p.2.1)), p.2.2.1, p.2.2.2)) ''
            ((fun p => (Ψ₁ p.1, Ψ₁ p.2.1, Pc₁ p.2.2.1, Pc₁' p.2.2.2)) '' Γ₁) := by
        rw [h]
        exact ⟨q, hq, rfl⟩
      obtain ⟨_, ⟨p, hp, rfl⟩, hpe⟩ := hc
      simp only [Equiv.symm_apply_apply, Prod.mk.injEq] at hpe
      obtain ⟨e1, e2, e3, e4⟩ := hpe
      obtain ⟨f1, f2⟩ := hinj p hp q hq e3.symm e4.symm
      exact ⟨p, hp, Prod.ext (Ψ₂.injective e1) (Prod.ext (Ψ₂.injective e2) (Prod.ext f1.symm f2.symm))⟩

end Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def PcG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) : H.Wb t.f →ₗ[E] E × E :=
  coordW H t.f (t.f (Fin.last r)) (omP H t.f t.f') (z_mem H t.f t.T hg.2.1)
    (omP_mem H t.f t.f' hg.2.2.2.1)

def PcG' {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) : H.Wb t.f' →ₗ[E] E × E :=
  coordW H t.f' (omP H t.f' t.f) (t.f' (Fin.last r))
    (omP_mem H t.f' t.f (unit_swap H t.f t.f' hg.2.2.2.1)) (z_mem H t.f' t.T' hg.2.2.1)

theorem pcG_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (hu : (u : V) ∈ H.perp (H.X t.f)) :
    PcG H hg (H.mkW t.f ⟨u, hu⟩) = ((sharpEquiv H t (unit_gramHG H hg) u (Sum.inl (Fin.last r)) : E),
      lamStarC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (fun b =>
        (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl b) : E) +
          algebraMap F E (g.q : F) * (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr b) : E))) := by
  simp only [PcG, coordW_mk]
  refine Prod.ext ?_ ?_
  · show H.h u (t.f (Fin.last r)) = _
    rw [sharpG_inl H hg]
  · show H.h u (omP H t.f t.f') = _
    rw [h_omP, lamStarC]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sharpG_f' H hg]
    rfl

theorem pcG'_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (hu : (u : V) ∈ H.perp (H.X t.f')) :
    PcG' H hg (H.mkW t.f' ⟨u, hu⟩) = (lamC (H.Zhat t.f t.f') (fun a =>
        (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl a) : E)),
      (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl (Fin.last r)) : E) +
        algebraMap F E (g.q : F) * (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr (Fin.last r)) : E)) := by
  simp only [PcG', coordW_mk]
  refine Prod.ext ?_ ?_
  · show H.h u (omP H t.f' t.f) = _
    rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sharpG_inl H hg]
  · show H.h u (t.f' (Fin.last r)) = _
    rw [sharpG_f' H hg]

theorem gamR_image {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    (fun p => (PsiG H hg p.1, PsiG H hg p.2.1, PcG H hg p.2.2.1, PcG' H hg p.2.2.2)) ''
        GamR H t (algebraMap F E (g.q : F)) =
      GamRC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹))
        (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  set s := sharpEquiv H t (unit_gramHG H hg) with hsdef
  ext ⟨d, e, c, c'⟩
  constructor
  · rintro ⟨_, ⟨u, u', u'', hu, hu', huu, rfl⟩, he⟩
    refine ⟨s u, s u', s u'', fun a => ?_, fun a => ?_, fun i => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharpG_inl H hg]
      exact (mem_perpX_iff H t.f u).1 hu a
    · rw [← sharpG_f' H hg]
      exact (mem_perpX_iff H t.f' u').1 hu' a
    · rw [sharpEquiv_apply, sharpEquiv_apply, sharpEquiv_apply, ← h_sub_left, huu, H.h_smul_left]
    · rw [← he]
      simp only [PsiG_mk, pcG_mk, pcG'_mk, ← hsdef]
  · rintro ⟨Y, Y', Y'', hY, hY', hYY, he⟩
    set u := s.symm Y with hu
    set u' := s.symm Y' with hu'
    set u'' := s.symm Y'' with hu''
    have sY : s u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have sY' : s u' = Y' := by rw [hu', LinearEquiv.apply_symm_apply]
    have sY'' : s u'' = Y'' := by rw [hu'', LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f) := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharpG_inl H hg, ← hsdef, sY, hY a]
      rfl
    have hX' : (u' : V) ∈ H.perp (H.X t.f') := by
      rw [mem_perpX_iff]
      intro a
      rw [sharpG_f' H hg, ← hsdef, sY']
      exact hY' a
    have hqO : algebraMap F E (g.q : F) ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L g.q
    have huu : (u : V) - u' = algebraMap F E (g.q : F) • (u'' : V) := by
      have h0 : u - u' - (⟨_, hqO⟩ : M.L.O) • u'' = 0 := by
        apply s.injective
        rw [map_zero, map_sub, map_sub, map_smul, sY, sY', sY'']
        funext i
        apply Subtype.ext
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        push_cast
        rw [hYY i]
        ring
      have h1 := congrArg Subtype.val h0
      simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_zero, Subring.smul_def] at h1
      exact sub_eq_zero.1 h1
    refine ⟨(ddMk H t u, ddMk H t u'', H.mkW t.f ⟨u, hX⟩, H.mkW t.f' ⟨u', hX'⟩),
      ⟨u, u', u'', hX, hX', huu, rfl⟩, ?_⟩
    rw [he]
    simp only [PsiG_mk, pcG_mk, pcG'_mk, ← hsdef, sY, sY', sY'']

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Cut

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def ZZm (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  HermSp.ZZplusOf M Zh T T' + Matrix.of fun a b => cor r a b (g.e.symm (-T / (g.q : F), T' / (g.q : F)))

def laG (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (l : Fin (r + 1) → M.R) : E :=
  (Zm⁻¹.mulVec fun i => (l i : E)) (Fin.last r)

abbrev mk1 (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (l : Fin (r + 1) → M.R) : DD1 hs Z TT :=
  QuotientAddGroup.mk l

def Gam1 (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Set (DD1 hs Z TT × DD1 hs Z TT × M.R × E) :=
  {p | ∃ (l : Fin (r + 1) → M.R) (η : M.R),
    p = (mk1 hs Z TT (η • eV r + q2 hs • l), mk1 hs Z TT l, η, laG Zm l)}

variable {Z₁ Z₂ : M.Mat (r + 1)} {TT : M.R}

def OLin (hs : M.split = some g) (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) : Prop :=
  ∀ (c : 𝒪[F]) (l l₂ : Fin (r + 1) → M.R), θ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
    θ (mk1 hs Z₁ TT (dgR hs c • l)) = mk1 hs Z₂ TT (dgR hs c • l₂)

def Match1 (hs : M.split = some g) (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (Zm₁ Zm₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) '' Gam1 hs Z₁ TT Zm₁ = Gam1 hs Z₂ TT Zm₂

def Ind (hs : M.split = some g) (γ : IsoMbe Z₁.Z Z₂.Z) (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) : Prop :=
  ∀ l l₂ : Fin (r + 1) → M.R, γ.1 (Submodule.Quotient.mk l) = Submodule.Quotient.mk l₂ →
    θ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂

private theorem split_symm_pair_zero_mem_O (c : F) (hc : c ∈ 𝒪[F]) : g.e.symm (c, 0) ∈ M.L.O := by
  rw [M.L.O_def]
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C ⟨c, hc⟩),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C _), ?_⟩
  have hmap : algebraMap (𝒪[F]) E ⟨c, hc⟩ = algebraMap F E c := rfl
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_sub, Polynomial.eval₂_C, hmap]
  apply g.e.injective
  simp [map_mul, map_sub, AlgEquiv.commutes, Prod.algebraMap_apply]

private theorem split_coords_mem_integers_of_mem_R (hs : M.split = some g) (y : E) (hy : y ∈ M.R) :
    (g.e y).1 ∈ 𝒪[F] ∧ ((g.e y).2 - (g.e y).1) / (g.q : F) ∈ 𝒪[F] := by
  unfold Model.R at hy
  rw [hs] at hy
  simp only [Subring.mem_comap, Subring.mem_map, RingHom.mem_eqLocus] at hy
  obtain ⟨⟨a, b⟩, hab, he⟩ := hy
  have he' : g.e y = ((a : F), (b : F)) := he.symm
  rw [he']
  refine ⟨a.2, ?_⟩
  simp only [RingHom.comp_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hab
  obtain ⟨d, hd⟩ := hab
  change d * g.q = a - b at hd
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have hd' : (d : F) * (g.q : F) = (a : F) - (b : F) := by
    have := congrArg Subtype.val hd
    push_cast at this
    exact this
  have key : ((b : F) - (a : F)) / (g.q : F) = ((-d : 𝒪[F]) : F) := by
    rw [div_eq_iff hq]
    push_cast
    linear_combination hd'
  rw [key]
  exact (-d).2

theorem iotaOne_mem_first (hs : M.split = some g) (x : M.R) : g.e.symm ((g.e (x : E)).1, 0) ∈ M.L.O := split_symm_pair_zero_mem_O _ (split_coords_mem_integers_of_mem_R hs _ x.2).1

theorem iotaOne_mem_second (hs : M.split = some g) (x : M.R) :
    g.e.symm (((g.e (x : E)).2 - (g.e (x : E)).1) / (g.q : F), 0) ∈ M.L.O := split_symm_pair_zero_mem_O _ (split_coords_mem_integers_of_mem_R hs _ x.2).2

def iota1 (hs : M.split = some g) (l : Fin (r + 1) → M.R) : Ix r → M.L.O
  | Sum.inl a => ⟨_, iotaOne_mem_first hs (l a)⟩
  | Sum.inr a => ⟨_, iotaOne_mem_second hs (l a)⟩

def iota2 (hs : M.split = some g) (l : Fin (r + 1) → M.R) : Ix r → M.L.O :=
  fun i => ⟨M.L.cj (iota1 hs l i), cj_mem_O M.L (iota1 hs l i).2⟩

variable {Zσ₁ Zσ₂ : M.Mat (r + 1)}

def IsoB (hs : M.split = some g) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT)
    (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) : Prop :=
  ∀ l l₂ w w₂ : Fin (r + 1) → M.R, θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
    θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT w₂ →
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂ (algebraMap F E T) (algebraMap F E T')
        (iota1 hs l₂) (iota2 hs w₂) -
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T) (algebraMap F E T')
        (iota1 hs l) (iota2 hs w) ∈ M.L.O

end Cut

section Steps

def GHyp {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) {r : ℕ} (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)) : Prop :=
  (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) ∧ (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) ∧
    g.e (TT : E) = (T, T') ∧ Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' ∧
    Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' ∧ IsUnit Zh.det ∧
    IsUnit (Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det))

def KapEq {E : Type} [CommRing E] {r : ℕ} (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det = Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det

def StepSplit : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card {p : (DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) × (DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) //
        OLin hs p.1 ∧ OLin hs p.2 ∧ Match1 hs p.1 (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') ∧
        Match1 hs p.2 (ZZm g (Zh₁.map M.L.cj) T T') (ZZm g (Zh₂.map M.L.cj) T T') ∧
        IsoB hs Zh₁ Zh₂ T T' p.1 p.2}

def FirstIsometryForward : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT, OLin hs θ → Match1 hs θ (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') →
      ∃ γ : IsoMbe Z₁.Z Z₂.Z, Ind hs γ θ

def FirstIsometryBackward : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT,
      OLin hs θ ∧ Match1 hs θ (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') ∧ Ind hs γ θ

def FirstIsometryUniqueness : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (γ γ' : IsoMbe Z₁.Z Z₂.Z), Ind hs γ θ → Ind hs γ' θ → γ = γ'

def StepDu : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ γ' : IsoMbe Zσ₁.Z Zσ₂.Z,
      ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT),
        Ind hs γ θ₁ → Ind hs γ' θ₂ → IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂

def StepDuU : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ θ₂' : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT),
      IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂ → IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂' → θ₂ = θ₂'

end Steps

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end
