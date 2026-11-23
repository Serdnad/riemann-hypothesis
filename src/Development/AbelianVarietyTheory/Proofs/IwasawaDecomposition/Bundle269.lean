module

public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  intro K _ _ _ S G _ _ r P ψ f
  constructor
  · rintro ⟨x, rfl⟩ p
    have h1 : (S.lvlE r P ψ).mulVec x ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := ⟨x, rfl⟩
    rw [(image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).2, level_part_spec K S G r P ψ] at h1
    have hz := h1 p
    have h4 := S.I_actMat r (p : G) ((S.lvlE r P ψ).mulVec x)
    rw [hz, map_smul, CSD.I_apply] at h4
    apply Subtype.ext
    rw [← h4]
    rfl
  · intro hf
    have hI : Function.Injective S.I := by
      intro a b h
      rw [CSD.I_apply, CSD.I_apply] at h
      exact S.basis.equivFun.symm.injective (Subtype.ext h)
    have hzf : S.basis.equivFun.symm (S.basis.equivFun f) = f := S.basis.equivFun.symm_apply_apply f
    have hz : ∀ p : P, (S.actMat r (p : G)).mulVec (S.basis.equivFun f) =
        ((ψ p : Kˣ) : K) • S.basis.equivFun f := by
      intro p
      apply hI
      rw [S.I_actMat r (p : G) _, map_smul, CSD.I_apply, hzf, hf p]
      rfl
    have h1 : S.basis.equivFun f ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := by
      rw [(image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).2, level_part_spec K S G r P ψ]
      exact hz
    obtain ⟨x, hx⟩ := h1
    refine ⟨x, ?_⟩
    have hx' : (S.lvlE r P ψ).mulVec x = S.basis.equivFun f := hx
    rw [hx', hzf]
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.LiftForms

theorem TjL_eq_map_matLat : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hL : OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P0 ψ0 i t)) (hZ : Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec (Pi.single k 1))))) (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t ((lZ0 D A P0 ψ0 Zs i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x))))), Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hL hZ hθ
  classical
  set J := (D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap with hJdef
  have hJ : ∀ x, J x = D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) := fun x => rfl
  have hspan : Idx.Z0 D (tup t) ((i : ℕ) + 1) =
      Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) := by
    rw [hZ, span_range_mulVec]
    rfl

  have hproj : ∀ x, (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J x) =
      J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hspan]
      exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
    · intro w hw
      rw [hspan] at hw
      have hle : Submodule.span ℂ (J '' Set.range fun z => lZ0 D A P0 ψ0 Zs i t *ᵥ z) ≤
          (Submodule.span ℂ {J x - J (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x))})ᗮ := by
        rw [Submodule.span_le]
        rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right, hF.inner, hF.inner,
          hform_orth hP, sub_self]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hw)

  have hθall : ∀ y, D.what₂.thetaP (tup t) ((i : ℕ) + 1) y =
      D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y) := by
    have h := LinearMap.ext_on_range hF.span (f := D.what₂.thetaP (tup t) ((i : ℕ) + 1))
      (g := (D.what₂.thetaP (tup t) ((i : ℕ) + 1)).comp
        ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection : D.what₂.Mt (tup t) ((i : ℕ) + 1) →L[ℂ] _).toLinearMap)
      (fun k => by
        show D.what₂.thetaP (tup t) ((i : ℕ) + 1) (J (Pi.single k 1)) =
          D.what₂.thetaP (tup t) ((i : ℕ) + 1) ((Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection (J (Pi.single k 1)))
        rw [hproj]
        exact hθ _)
    intro y
    exact LinearMap.congr_fun h y
  have hle1 : (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ ≤ LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)) := by
    intro w hw
    rw [LinearMap.mem_ker, hθall, (Submodule.starProjection_apply_eq_zero_iff _).2 hw, map_zero]
  have hZj : D.what₂.Zj (tup t) ((i : ℕ) + 1) = Idx.Z0 D (tup t) ((i : ℕ) + 1) := by
    have h1 : D.what₂.Zj (tup t) ((i : ℕ) + 1) = (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ := by
      rw [LinearMap.orthogonal_ker]
      rfl
    rw [h1]
    apply le_antisymm
    · have := Submodule.orthogonal_le hle1
      rwa [Submodule.orthogonal_orthogonal] at this
    · exact inf_le_left
  have hfix : ∀ y ∈ LinearMap.range (D.what₂.eMt (tup t) ((i : ℕ) + 1)), D.what₂.eMt (tup t) ((i : ℕ) + 1) y = y := by
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun f : D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] D.what₂.Mt (tup t) ((i : ℕ) + 1) => f y) (D.what₂.eMt_idem _ _)
  have h4' : ∀ y, D.what₂.eMt (tup t) ((i : ℕ) + 1) ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection y) =
      (Idx.Z0 D (tup t) ((i : ℕ) + 1)).starProjection y := by
    intro y
    simp only [hZj]
    exact hfix _ (inf_le_right (a := (LinearMap.ker (D.what₂.thetaP (tup t) ((i : ℕ) + 1)))ᗮ)
      (Submodule.starProjection_apply_mem (Idx.Z0 D (tup t) ((i : ℕ) + 1)) y))

  have h6 : Submodule.span (𝓞 D.what₂.LL)
      {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} =
      (lNab D A P0 ψ0 i t).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro u hu
      obtain ⟨c, hc⟩ := hu
      refine ⟨(eMt i t).symm u, (hL.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, ?_⟩, by simp⟩
      rw [hJ, LinearEquiv.apply_symm_apply, hc]
      rfl
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := (hL.2 x).1 hx
      have hc' : D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x) =
          ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      have key : ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
          D.what₂.jMt (tup t) ((i : ℕ) + 1) y =
            ∑ v ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v := by
        refine Finset.sum_induction _ (fun m => ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
          {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier},
            D.what₂.jMt (tup t) ((i : ℕ) + 1) y = m) ?_ ⟨0, zero_mem _, map_zero _⟩ fun v hv => ?_
        · rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, add_mem hy hz, map_add _ _ _⟩
        · obtain ⟨y, hy⟩ := D.what₂.MtLat_sub (tup t) ((i : ℕ) + 1) v hv
          refine ⟨c v • y, Submodule.smul_mem _ _ (Submodule.subset_span ?_), by rw [Idx.smul_def, map_smulₛₗ, hy]⟩
          refine ⟨fun u => if u = v then 1 else 0, ?_⟩
          rw [hy, Finset.sum_eq_single v]
          · simp
          · intro u _ hu
            simp [hu]
          · intro h; exact absurd hv h
      obtain ⟨y, hy, hyx⟩ := key
      have hxy : y = eMt i t x := jMt_injective _ _ (hyx.trans hc'.symm)
      change eMt i t x ∈ _
      rw [← hxy]
      exact hy

  let π : D.what₂.MtL (tup t) ((i : ℕ) + 1) →ₗ[𝓞 D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P0 ψ0 Zs i t).mulVecLin ∘ₗ
      (lPrj D A P0 ψ0 Zs i t).mulVecLin ∘ₗ (eMt i t).symm.toLinearMap).restrictScalars (𝓞 D.what₂.LL)
  have hπe : ∀ x, π (eMt i t x) = eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ x)) := by
    intro x
    show eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ (lPrj D A P0 ψ0 Zs i t *ᵥ (eMt i t).symm (eMt i t x))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hπ : ∀ x, D.what₂.jMt (tup t) ((i : ℕ) + 1) (π x) = D.what₂.eMt (tup t) ((i : ℕ) + 1)
      ((D.what₂.Zj (tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) := by
    intro x
    obtain ⟨x, rfl⟩ := (eMt i t).surjective x
    rw [h4', ← hJ, hproj, hπe]
    rfl
  have hset : {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ D.what₂.TjSet (tup t) ((i : ℕ) + 1)} =
      π '' {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} := by
    ext x
    constructor
    · rintro ⟨m, hm, hx⟩
      obtain ⟨u, rfl⟩ := carrier_subset _ _ m hm
      exact ⟨u, hm, jMt_injective _ _ ((hπ u).trans hx)⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hu, (hπ u).symm⟩
  unfold Idx.TjL
  rw [hset, ← Submodule.map_span, h6]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, (hπe y).symm⟩
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hπe y⟩

end GlobalTheory.Mem.LiftForms

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.JwLift

theorem mem_dual_iff {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h y x := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]

theorem jwIdx_eq_jw : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hHZ : (lZ0 D A P0 ψ0 Zs i t)ᴴ * lH D A P0 ψ0 i t * lZ0 D A P0 ψ0 Zs i t = (A.side P0 ψ0 Zs).HT i t) (hsp : Submodule.span D.what₂.LL (↑((A.side P0 ψ0 Zs).Tl i t) : Set (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL)) = ⊤) (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL))) (w : D.what₂.places.Pl), Idx.jwIdx D (tup t) ((i : ℕ) + 1) w = Formalism.DivisionValues.jw ((A.side P0 ψ0 Zs).HT i t) (D.plEq w) ((A.side P0 ψ0 Zs).Tl i t) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hHZ hsp hT w
  set HT := (A.side P0 ψ0 Zs).HT i t with hHTdef
  set Tl := (A.side P0 ψ0 Zs).Tl i t with hTldef
  let Z : Matrix (Fin (lDim D A P0 ψ0 i t)) (Fin ((A.side P0 ψ0 Zs).dZ i t)) D.what₂.LL := lZ0 D A P0 ψ0 Zs i t
  let Pr : Matrix (Fin ((A.side P0 ψ0 Zs).dZ i t)) (Fin (lDim D A P0 ψ0 i t)) D.what₂.LL := lPrj D A P0 ψ0 Zs i t
  have hP1 : Pr * Z = 1 := hP.1
  have hHZ' : Zᴴ * lH D A P0 ψ0 i t * Z = HT := hHZ
  have hT' : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Tl.map ((Matrix.mulVecLin Z).restrictScalars (𝓞 D.what₂.LL))).map
      ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := hT
  let f : (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL) →ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    (eMt i t).toLinearMap ∘ₗ Matrix.mulVecLin Z
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : Z *ᵥ x = Z *ᵥ y := (eMt i t).injective hxy
    have h2 : Pr *ᵥ (Z *ᵥ x) = Pr *ᵥ (Z *ᵥ y) := by rw [h1]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP1, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  have hTL : Idx.TjL D (tup t) ((i : ℕ) + 1) = Tl.map (f.restrictScalars (𝓞 D.what₂.LL)) := by
    rw [hT', ← Submodule.map_comp]
    rfl
  have hTV : Idx.TjV D (tup t) ((i : ℕ) + 1) = LinearMap.range f := by
    unfold Idx.TjV
    rw [hTL, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hsp, Submodule.map_top]
  have hin : ∀ y z, inner ℂ (D.what₂.jMt (tup t) ((i : ℕ) + 1) (f y)) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (f z)) =
      D.what₂.embLL (Formalism.DivisionValues.hform HT y z) := by
    intro y z
    have := hF.inner (Z *ᵥ y) (Z *ᵥ z)
    have e1 : Formalism.DivisionValues.hform (lH D A P0 ψ0 i t) (Z *ᵥ y) (Z *ᵥ z) = Formalism.DivisionValues.hform HT y z := by
      rw [GlobalTheory.Mem.LiftForms.hform_dot HT, ← hHZ']
      exact GlobalTheory.Mem.LiftForms.hform_mulVec _ Z Z y z
    rw [← e1]
    exact this
  have hDual : Idx.TjDual D (tup t) ((i : ℕ) + 1) =
      (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform HT) Tl).map (f.restrictScalars (𝓞 D.what₂.LL)) := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      rw [hTV] at hx
      obtain ⟨z, rfl⟩ := hx
      refine ⟨z, (mem_dual_iff _ _ _).2 fun y hy => ?_, rfl⟩
      obtain ⟨c, hc⟩ := hx2 (f y) (by rw [hTL]; exact ⟨y, hy, rfl⟩)
      rw [hin] at hc
      exact ⟨c, (D.what₂.embLL.injective hc).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨by rw [hTV]; exact ⟨z, rfl⟩, ?_⟩
      rintro a ha
      rw [hTL] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨c, hc⟩ := (mem_dual_iff _ _ _).1 hz y hy
      refine ⟨c, ?_⟩
      change _ = D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL c)
      rw [hc]
      exact hin y z
  unfold Idx.jwIdx Formalism.DivisionValues.jw Formalism.HermitianLatticesTheory.jIdx
  rw [hTL, hDual]
  exact Formalism.BasicNotions.SkeletonIndexLemmas.lidx_map (D.plEq w) f hf _ _

end GlobalTheory.Mem.JwLift

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtPar

lemma univ_map_eq_range {α : Type} (n : ℕ) (f : ℕ → α) :
    (Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => f (i : ℕ)) = (Multiset.range n).map f := by
  rw [Fin.univ_val_map, List.ofFn_eq_map, Multiset.range, Multiset.map_coe, ← List.map_coe_finRange_eq_range,
    List.map_map]
  rfl

lemma transport {D : D7} {j : ℕ} {τ : D.what₂.Tau} {n n' : ℕ} (h : n = n')
    (hx : ∃ lam : DomWeight n, Bridge.IsLamPrime (D := D) lam j τ) :
    ∃ lam : DomWeight n', Bridge.IsLamPrime (D := D) lam j τ := by
  subst h; exact hx

lemma lamPrime_add_rho (W : Formalism.IndefR.IndefiniteWeightData.WeightData) (hk : 1 ≤ W.k) (hj : 1 ≤ W.j) (hjm : W.j ≤ W.m)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ W.nV) :
    W.lamPrime i + W.rhoNV i = W.uSideTarget i - 1 / 2 := by
  have hN : W.nV = W.p + W.q + W.t := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q]; omega
  have hNq : (W.nV : ℚ) = W.p + W.q + W.t := by exact_mod_cast hN
  simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt,
    Formalism.IndefR.IndefiniteWeightData.WeightData.dTau, Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV,
    Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus,
    Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus]
  split_ifs with h1 h2
  · ring
  · rw [hNq]; ring
  · have hc : W.q + 1 - (W.q + 1 - (i - W.p - W.t)) = i - W.p - W.t := by omega
    rw [hc]
    have hc' : ((i - W.p - W.t : ℕ) : ℚ) = i - W.p - W.t := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [hc', hNq]; ring

end GlobalTheory.Mem.WtPar

namespace GlobalTheory.Mem.WtPar

theorem infOf_lamLdef_eq_paramV : ∀ (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau),
    NG.infOf (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ).w = NG.paramV D.R (D.hc τ) j (1 / 2) := by
  intro D j τ
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  have hex : ∃ lam : DomWeight D.R.nV, Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
    have h0 := GlobalTheory.ForcedWeights.lamLForced D ((j : ℕ) + 1) (by omega) (by omega) τ
    have hr : (D.sp.V ((j : ℕ) + 1)).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    exact transport hr ⟨_, h0⟩
  have hl : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
    unfold Bridge.lamLdef; rw [dite_eq_left hex]; exact hex.choose_spec
  set lam := Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hw⟩ := hl
  have hWn : W.nV = D.R.nV := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r, Ranks.nV, Ranks.r, hWk, hWm, hWt]
  have hWp : W.p = D.R.k + (j : ℕ) := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.p, hWk, hWj]; omega
  let g : ℕ → ℚ := fun i => W.uSideTarget (i + 1) - 1 / 2

  have hL : NG.infOf lam.w = (Multiset.range D.R.nV).map (fun i => ((g i : ℚ) : ℂ)) := by
    unfold NG.infOf
    rw [← univ_map_eq_range]
    refine Multiset.map_congr rfl fun i _ => ?_
    have h1 := lamPrime_add_rho W (by omega) (by omega) (by omega) ((i : ℕ) + 1) (by omega)
      (by have := i.2; omega)
    have h2 := hw i
    have key : ((lam.w i : ℤ) : ℚ) + ((D.R.nV : ℚ) - 1) / 2 - ((i : ℕ) : ℚ) = g i := by
      simp only [g]
      rw [h2, ← h1]
      simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV, hWn]
      push_cast; ring
    have := congrArg (fun x : ℚ => (x : ℂ)) key
    push_cast at this ⊢
    exact this

  let gv : ℕ → ℚ := fun n => (W.v (n + 2) : ℚ) - 1 / 2
  let gb : ℕ → ℚ := fun n => -(W.b (n + 1) : ℚ) - 1 / 2
  let ge : ℕ → ℚ := fun c => -(W.e : ℚ) - 1 / 2 + ((D.R.t : ℚ) - 1 - 2 * c) / 2
  have hR : NG.paramV D.R (D.hc τ) j (1 / 2) =
      ((Multiset.range (D.R.k - 1)).map gv + (Multiset.range D.R.m).map gb
        + (Multiset.range D.R.t).map ge).map (fun x : ℚ => (x : ℂ)) := by
    simp only [Multiset.map_add (f := _), Multiset.map_map]
    unfold NG.paramV
    congr 1
    · congr 1
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gv, hWv i]
        push_cast; ring
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gb, hWb i]
        push_cast; ring
    · refine Multiset.map_congr rfl fun c _ => ?_
      have he : (D.hc τ).e j = (W.e : ℚ) := by
        rw [hWe]; congr 1; try (ext; simp)
      simp only [Function.comp, ge, he]
      push_cast; ring
  rw [hL, hR, show (fun i => ((g i : ℚ) : ℂ)) = (fun x : ℚ => (x : ℂ)) ∘ g from rfl, ← Multiset.map_map]
  congr 1

  have hsplit : D.R.nV = ((D.R.k - 1) + ((j : ℕ) + 1)) + D.R.t + (D.R.m - ((j : ℕ) + 1)) := by
    simp only [Ranks.nV, Ranks.r]; omega
  have hmsplit : D.R.m = ((j : ℕ) + 1) + (D.R.m - ((j : ℕ) + 1)) := by omega
  rw [hsplit, Multiset.range_add, Multiset.range_add, Multiset.range_add]
  conv_rhs => rw [hmsplit, Multiset.range_add]
  simp only [Multiset.map_add (f := _), Multiset.map_map]
  have e1 : (Multiset.range (D.R.k - 1)).map g = (Multiset.range (D.R.k - 1)).map gv := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [g, gv, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam, hWp, hWk]
    rw [if_pos (by omega), if_pos (by omega)]
  have e2 : (Multiset.range ((j : ℕ) + 1)).map (g ∘ fun x => D.R.k - 1 + x) =
      (Multiset.range ((j : ℕ) + 1)).map gb := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      hWp, hWk]
    rw [if_pos (by omega), if_neg (by omega)]
    have hh : D.R.k - 1 + n + 1 - (D.R.k - 1) = n + 1 := by omega
    rw [hh]; push_cast; ring
  have e3 : (Multiset.range D.R.t).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + x) =
      (Multiset.range D.R.t).map ge := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, ge, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt]
    rw [if_neg (by omega), if_pos (by omega)]
    have : ((D.R.k - 1 + ((j : ℕ) + 1) + c + 1 : ℕ) : ℚ) - ((D.R.k + (j : ℕ) : ℕ) : ℚ) = c + 1 := by
      rw [show D.R.k - 1 + ((j : ℕ) + 1) + c + 1 = (D.R.k + (j : ℕ)) + (c + 1) by omega]
      push_cast; ring
    rw [this]; ring
  have e4 : (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + x) =
      (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (gb ∘ fun x => (j : ℕ) + 1 + x) := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt, hWj]
    rw [if_neg (by omega), if_neg (by omega)]
    have hh : (j : ℕ) + 1 + (D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + c + 1 - (D.R.k + (j : ℕ)) - D.R.t) = (j : ℕ) + 1 + c + 1 := by omega
    rw [hh]
  rw [e1, e2, e3, e4]
  abel

end GlobalTheory.Mem.WtPar
end

section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemTame

theorem exists_tameGenAt :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∃ γ : G E Ω, TameGenAt A γ :=
  @GlobalTheory.TameInertiaGen.exists_tameGenAt

end GlobalTheory.MemTame
end
