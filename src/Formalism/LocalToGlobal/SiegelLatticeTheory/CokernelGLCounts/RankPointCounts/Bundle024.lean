module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GramMMUnitOfTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle022
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueEtaPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
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
import Formalism.PeriodIntegrals.Bundle030
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

section

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

private theorem adjugate_last_col_sum_and_det_of_coset (Z Z' P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (v v' : Fin (r + 1) → S.V) (φ : S.V →ₗ[E] S.V) (hZ : Z' = P * Z * Q)
    (hv : ∀ b, v' b = φ (∑ c, Q c b • v c)) (hQ : Q.det = 1) (hP : P.det = 1)
    (hPl : ∀ a, P a (Fin.last r) = if a = Fin.last r then 1 else 0) :
    ∑ b, Z'.adjugate b (Fin.last r) • v' b = φ (∑ b, Z.adjugate b (Fin.last r) • v b) ∧
      Z'.det = Z.det := by
  have hQQ : Q * Q.adjugate = 1 := by rw [Matrix.mul_adjugate, hQ, one_smul]
  have hPP : P.adjugate * P = 1 := by rw [Matrix.adjugate_mul, hP, one_smul]
  have hPl' : ∀ d, P.adjugate d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    have := congrFun (congrFun hPP d) (Fin.last r)
    simpa [Matrix.mul_apply, hPl, Matrix.one_apply] using this
  have hW : ∀ c, (Q * (Q.adjugate * (Z.adjugate * P.adjugate))) c (Fin.last r) =
      Z.adjugate c (Fin.last r) := by
    intro c
    rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_apply]
    simp [hPl']
  refine ⟨?_, ?_⟩
  · rw [hZ, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]

    simp only [hv, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, ← hW c, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [hZ, Matrix.det_mul, Matrix.det_mul, hP, hQ, one_mul, mul_one]

theorem omp_coset (F : FlagG S r T) (F0 : FlagG S r T') (σ γ1 s' : S.V ≃ₗ[E] S.V)
    (hσ : σ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hσ' : σ.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ1 : γ1 ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hγ2 : σ * γ1 * s' ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hσf : ∀ j, ∀ x ∈ F.Xa (j + 1), σ.symm x - x ∈ F.Xa j) (hσz : σ.symm F.z - F.z ∈ F.X)
    (hsf : ∀ j, ∀ x ∈ F0.Xa (j + 1), s' x - x ∈ F0.Xa j) (hsz : s' F0.z - F0.z ∈ F0.X) :
    omp F (mapFlag (σ * γ1 * s') hγ2 F0) = σ (omp F (mapFlag γ1 hγ1 F0)) ∧
    (Zhat F (mapFlag (σ * γ1 * s') hγ2 F0)).det = (Zhat F (mapFlag γ1 hγ1 F0)).det ∧
    omp (mapFlag (σ * γ1 * s') hγ2 F0) F = σ (omp (mapFlag γ1 hγ1 F0) F) ∧
    (Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F).det = (Zhat (mapFlag γ1 hγ1 F0) F).det := by
  obtain ⟨M, hM, hMd, hMl⟩ := coef_mat F0 (s' : S.V →ₗ[E] S.V) (fun j x hx => hsf j x hx) hsz
  obtain ⟨N, hN, hNd, hNl⟩ := coef_mat F (σ.symm : S.V →ₗ[E] S.V) (fun j x hx => hσf j x hx) hσz
  have hM' : ∀ b, s' (F0.fvec b) = ∑ c, M c b • F0.fvec c := hM
  have hN' : ∀ b, σ.symm (F.fvec b) = ∑ c, N c b • F.fvec c := hN
  have hs : ∀ x y, S.hT (σ x) (σ y) = S.hT x y := hσ
  have hv1 : ∀ b, (mapFlag (σ * γ1 * s') hγ2 F0).fvec b =
      σ (∑ c, M c b • (mapFlag γ1 hγ1 F0).fvec c) := by
    intro b

    rw [fvec_mapFlag, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hM' b, map_sum]
    simp only [fvec_mapFlag, map_smul]
  have hv2 : ∀ b, F.fvec b = σ (∑ c, N c b • F.fvec c) := by
    intro b
    rw [← hN', LinearEquiv.apply_symm_apply]
  have hZ1 : Zhat F (mapFlag (σ * γ1 * s') hγ2 F0) = Nᴴ * Zhat F (mapFlag γ1 hγ1 F0) * M := by
    ext a b
    have e1 : Zhat F (mapFlag (σ * γ1 * s') hγ2 F0) a b =
        S.hT (F.fvec a) ((mapFlag (σ * γ1 * s') hγ2 F0).fvec b) := rfl
    rw [e1, hv1 b, hv2 a, hs]

    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Zhat, brS, starRingEnd_apply,
    Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hZ2 : Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F = Mᴴ * Zhat (mapFlag γ1 hγ1 F0) F * N := by
    ext a b
    have e1 : Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F a b =
        S.hT ((mapFlag (σ * γ1 * s') hγ2 F0).fvec a) (F.fvec b) := rfl
    rw [e1, hv1 a, hv2 b, hs]

    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Zhat, brS, starRingEnd_apply,
    Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨h1, h2⟩ := adjugate_last_col_sum_and_det_of_coset _ _ _ _ _ _ (σ : S.V →ₗ[E] S.V) hZ1 hv1 hMd
    (by simp [Matrix.det_conjTranspose, hNd])
    (by intro a; rw [Matrix.conjTranspose_apply, hNl]; split_ifs <;> simp)
  obtain ⟨h3, h4⟩ := adjugate_last_col_sum_and_det_of_coset _ _ _ _ _ _ (σ : S.V →ₗ[E] S.V) hZ2 hv2 hNd
    (by simp [Matrix.det_conjTranspose, hMd])
    (by intro a; rw [Matrix.conjTranspose_apply, hMl]; split_ifs <;> simp)
  exact ⟨h1, h2, h3, h4⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG8

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem rgHyp_of (M : Model F E) (hM : M.OK) {r n : ℕ} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    (hn : Module.finrank E V = n) (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') (hyp : LocalCountHypotheses H t₁ f₂ f₂' φ φ')
    (Λ₂ : Submodule M.L.O V) (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩)
    (hth : ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ')
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩)
    (hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂) :
    ∃ ψ, RGHyp H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ θ φ φ' := by
  have hT₁ := hyp.1.1
  have hT₂ := hg.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT₁.2.1.2.1, hT₁.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT₁.2.2.1.2.1, hT₁.2.2.1.2.2.1⟩
  have hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)) := hT₂.2.2.2.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT₁.2.2.2.1
  obtain ⟨ψ, -, hψc⟩ := corrIso_holds M r n V H hn t₁ f₂ f₂' φ φ' hyp hD₂
  have hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f') :=
    isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ (isUnit_Gdet H _ _ _ _ hT₁.2.2.2.2.1)
  have hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim f₂ f₂'))) (H.W0 f₂ f₂') :=
    isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hyp.2.1 hyp.2.2.1 hD₂ (isUnit_Gdet H _ _ _ _ hT₂.2.2.2.2.1)
  have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
  have hZ₁' : IsUnit (H.Zhat t₁.f' t₁.f).det := det_Zhat_swap_unit H _ _ hZ₁
  have hzφ : φ (H.mkW t₁.f ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩) =
      H.mkW f₂ ⟨f₂ (Fin.last r), z_mem_perpX H hyp.2.1⟩ := by
    have e := hyp.2.2.2.2.1 ⟨_, z_mem_perpX H hF₁⟩ ⟨_, z_mem_perpX H hyp.2.1⟩ rfl rfl
    simpa using e
  have hzφ' : φ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perpX H hF₁'⟩) =
      H.mkW f₂' ⟨f₂' (Fin.last r), z_mem_perpX H hyp.2.2.1⟩ := by
    have e := hyp.2.2.2.2.2 ⟨_, z_mem_perpX H hF₁'⟩ ⟨_, z_mem_perpX H hyp.2.2.1⟩ rfl rfl
    simpa using e
  obtain ⟨u, hu⟩ := hD₂
  have hoφ : φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
      ((↑u⁻¹ : E) * H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ := by
    have e : H.Dl f₂ f₂' (r + 1) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
        H.Dl t₁.f t₁.f' (r + 1) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.1 _ _ rfl rfl
    rw [← hu] at e
    calc φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)
        = (↑u⁻¹ : E) • ((u : E) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  obtain ⟨u', hu'⟩ : IsUnit (M.L.cj (H.Dl f₂ f₂' (r + 1))) := by rw [← hu]; exact (Units.isUnit u).map _
  have hoφ' : φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
      ((↑u'⁻¹ : E) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ := by
    have e : M.L.cj (H.Dl f₂ f₂' (r + 1)) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
        M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.2.1 _ _ (om'_swap H _ _) (om'_swap H _ _)
    rw [← hu'] at e
    calc φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)
        = (↑u'⁻¹ : E) • ((u' : E) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  refine ⟨ψ, {
    hU₂ := hU₂
    hU₁ := hU₁
    hsd₁ := hT₁.1
    hsd₂ := hT₂.1
    hMM₁ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
    hMM₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
    hth := fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
    hθ := ?_
    hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁
    hC1 := fun w => by
      obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
      exact c₁
    hC1' := fun w => by
      obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
      exact c₂
    hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
    hC2' := fun v hv hvp => by
      rw [← U_swap] at hv
      obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
      rw [U_swap] at hv'
      exact ⟨v', hv', hv'p, e⟩ }⟩
  intro m₁ m₂
  rw [hθ m₁ m₂]
  constructor
  · rintro ⟨n₁, n₂, hc, h1, h2⟩
    obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
    exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
  · rintro ⟨w, h1, h2⟩
    exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩

theorem claimRG_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRG M r n := by
  intro hsome V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨ψ, D⟩ := rgHyp_of M hM H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  have core1 := fun hI => Set.Subset.antisymm (rg_fwd_sub H g D hI) (rg_fwd_sup H g D hI)
  have core2 := fun hG => Set.Subset.antisymm (rg_bwd_sub H g D hG) (rg_bwd_sup H g D hG)
  have hL1 := Lset_eq_snd H hM g hs t₁ hyp.1 D.hU₁
  have hL1' := Lset_eq_fst H hM g hs t₁ hyp.1 D.hU₁
  have hL2 := Lset_eq_snd H hM g hs (⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) hg D.hU₂
  have hL2' := Lset_eq_fst H hM g hs (⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) hg D.hU₂
  constructor
  · intro hR
    refine ⟨fun h => absurd (hs.symm.trans h) (by simp), fun g' hg' => ?_⟩
    rw [Option.some.inj (hg'.symm.trans hs)]
    exact core1 (hR.2.2.2.2 g hs)
  · rintro ⟨-, hGR⟩
    have hI := core2 (hGR g hs)
    have e : φ '' (Prod.snd '' H.iotaGraph g t₁) = Prod.snd '' (Prod.map φ' φ '' H.iotaGraph g t₁) := by
      rw [Set.image_image, Set.image_image]
      rfl
    have e' : φ' '' (Prod.fst '' H.iotaGraph g t₁) = Prod.fst '' (Prod.map φ' φ '' H.iotaGraph g t₁) := by
      rw [Set.image_image, Set.image_image]
      rfl
    refine ⟨(congrArg (φ '' ·) hL1).trans (e.trans ((congrArg (Prod.snd '' ·) hI).trans hL2.symm)),
      hyp.2.2.2.2.1,
      (congrArg (φ' '' ·) hL1').trans (e'.trans ((congrArg (Prod.fst '' ·) hI).trans hL2'.symm)),
      hyp.2.2.2.2.2, fun g' hg' => ?_⟩
    rw [Option.some.inj (hg'.symm.trans hs)]
    exact hI

theorem claimR_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimR M r n :=
  claimR_of_modes M r n (claimRL_at M r n hM) (claimRG_at M r n hM)

theorem localCount_of_module (M : Model F E) (r n : ℕ) (hM : M.OK) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n :=
  localCount_of_glue M r n hM (PI.LocCntLat.GE.glueEta_holds M r) (PI.LocCntLat.GC.glueConv_holds M r)
    (genOfPrim_holds M r n) (claimR_at M r n hM) h0 hU

theorem globalCount_of_module (D : Formalism.BasicNotions.D7)
    (h0 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ModSide0 M D.R.rS D.R.r M.split.isSome))
    (hU : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ModSideU M D.R.rS D.R.r M.split.isSome)) : Formalism.MainNotions.ThinScalesBound.T2 D := by
  intro F _ _ _ E _ _ _ _ M hM
  exact localCount_of_module M D.R.rS D.R.r hM (h0 F E M hM) (hU F E M hM)

end RG8

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Bridge

variable {D : D7}

def condI (y : D.host.E) : Ideal (𝓞 D.host.E) where
  carrier := {t | ∃ o : 𝓞 D.host.E, (t : D.host.E) * y = o}
  add_mem' := by
    rintro a b ⟨o₁, h₁⟩ ⟨o₂, h₂⟩
    exact ⟨o₁ + o₂, by push_cast; rw [add_mul, h₁, h₂]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨o, h⟩
    exact ⟨c * o, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h]⟩

theorem iota_mem_O (p : PlF D) (y : D.host.E)
    (h : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → IntP P y) :
    (D.s.atP p).ιE y ∈ (D.s.atP p).O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.iE_mem_O_iff_D]
  have := p.isPrime
  by_contra hno
  push Not at hno
  have hle : (condI y).comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ p.asIdeal := by
    intro s hs
    by_contra hsp
    obtain ⟨o, ho⟩ := hs
    apply hno s hsp
    have e : algebraMap D.host.F D.host.E (s : D.host.F) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) := by
      rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E,
        IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E]
    rw [e, ho]
    exact o.2
  obtain ⟨Q, hIQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (condI y) hle
  have hQ0 : Q ≠ ⊥ := by
    intro hb
    apply p.ne_bot
    rw [← hQc, hb]
    change Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ⊥ = ⊥
    rw [Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E)
  obtain ⟨t, ht, o, hto⟩ := h ⟨Q, hQp, hQ0⟩ hQc
  exact ht (hIQ ⟨o, hto⟩)

end Bridge

end Formalism.L2.SG.Pf.FibQ
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs PI.NRCW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable (D : D7)

abbrev aaF (a : Fin (D.R.rS + 1)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

theorem entry_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G) (hXS : XLam Λ G = XS D G.fl) (hz : G.fl.z ∈ Λ)
    (c b : Fin (D.R.rS + 1)) (hcb : c < b) : ∀ x ∈ aaF D b, x * fmat D G n c b ∈ aaF D c := by
  have hc : c.val < D.R.rS := by have := b.isLt; omega
  have hf : fmat D G n c b = G.fl.coefX (n (frame G b) - frame G b) ⟨c.val, hc⟩ := by
    simp only [fmat, dif_pos hc]
    rw [if_neg (ne_of_lt hcb), zero_add]
  rw [hf]
  have hXSΛ : ∀ v, v ∈ XS D G.fl → v ∈ Λ := by
    intro v hv
    rw [← hXS, XLam, Submodule.mem_inf] at hv
    exact hv.1
  have haF : aaF D c = aaI D ⟨c.val, hc⟩ := rfl
  rw [haF]
  intro x hx
  by_cases hb : b.val < D.R.rS
  · have hfi : frame G b = G.fl.e ⟨b.val, hb⟩ := by
      have h0 := frame_castSucc G ⟨b.val, hb⟩
      rwa [show (⟨b.val, hb⟩ : Fin D.R.rS).castSucc = b from Fin.ext rfl] at h0
    rw [hfi]
    have hxe : x • G.fl.e ⟨b.val, hb⟩ ∈ XS D G.fl := Submodule.subset_span ⟨⟨b.val, hb⟩, x, hx, rfl⟩
    have hn1 : n (x • G.fl.e ⟨b.val, hb⟩) ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨nlam_mem hn (hXSΛ _ hxe), nlam_X hn (Submodule.smul_mem _ x (e_mem_X _ _))⟩
    have hcx := (coefX_of_mem_XS D G.fl hn1).2 ⟨c.val, hc⟩
    have hd : n (G.fl.e ⟨b.val, hb⟩) - G.fl.e ⟨b.val, hb⟩ ∈ G.fl.X :=
      Xa_le_X _ _ ((nlam_frame_mem G hn).1 _)
    have hsplit : n (x • G.fl.e ⟨b.val, hb⟩) =
        x • (G.fl.e ⟨b.val, hb⟩ + (n (G.fl.e ⟨b.val, hb⟩) - G.fl.e ⟨b.val, hb⟩)) := by
      rw [map_smul]; congr 1; abel
    have hne : (⟨b.val, hb⟩ : Fin D.R.rS) ≠ ⟨c.val, hc⟩ := by
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    rw [hsplit, coefX_smul _ (add_mem (e_mem_X _ _) hd), coefX_add _ (e_mem_X _ _) hd, coefX_e, if_neg hne,
      zero_add] at hcx
    exact hcx
  · have hfz : frame G b = G.fl.z := by
      have h0 := frame_last G
      rwa [show Fin.last D.R.rS = b from Fin.ext (by have := b.isLt; simp; omega)] at h0
    rw [hfz]
    have hb0 : aaF D b = 1 := by
      have : (D.R.rS : ℤ) - (b : ℕ) = 0 := by have := b.isLt; push_cast; omega
      simp only [aaF, this, neg_zero, zpow_zero]
    rw [hb0] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
    have hv : n G.fl.z - G.fl.z ∈ XS D G.fl := by
      rw [← hXS, XLam, Submodule.mem_inf]
      exact ⟨sub_mem (nlam_mem hn hz) hz, (nlam_frame_mem G hn).2⟩
    have hcx := (coefX_of_mem_XS D G.fl hv).2 ⟨c.val, hc⟩
    rw [← Algebra.smul_def]
    exact fi_smul _ o hcx

end Glob

end Formalism.L2.SG.Pf.FibQ
end
end
