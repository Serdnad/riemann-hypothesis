module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle024
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle275
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle228
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle297
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle339
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle372
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanDecompositionExists
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFrameVectorMemCommonSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.IsotropicLift

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def kerR (H : HermSp M V) (w : V) : Submodule E V where
  carrier := {v | H.h v w = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_add_left, ha, hb, add_zero]
  zero_mem' := H.h_zero_left w
  smul_mem' c v hv := by
    simp only [Set.mem_setOf_eq] at *
    rw [H.h_smul_left, hv, mul_zero]

theorem h_swap_zero (H : HermSp M V) {x y : V} (h : H.h x y = 0) : H.h y x = 0 := by
  rw [H.h_herm, h]; simp

theorem X_le_perp (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  intro x hx
  have hk : H.X Fr.f ≤ kerR H (Fr.f b.castSucc) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Fr.h_iso a.castSucc b.castSucc (Or.inl (Fin.castSucc_ne_last a))
  exact h_swap_zero H (hk hx)

theorem sub_mem_X_of_mem_N (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    {v : V} (hv : v ∈ H.perp (H.X Fr.f)) : n v - v ∈ H.X Fr.f := by
  have hXP := X_le_perp H Fr
  suffices key : ∀ g ∈ Fr.N, ∀ v ∈ H.perp (H.X Fr.f), g v - v ∈ H.X Fr.f ∧ g.symm v - v ∈ H.X Fr.f from
    (key n hn v hv).1
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨hu, -, hperp⟩ := hg
    intro v hv
    refine ⟨hperp v hv, ?_⟩
    have hw : g.symm v ∈ H.perp (H.X Fr.f) := by
      intro x hx
      have hgx : g x ∈ H.X Fr.f := by
        have := hperp x (hXP hx)
        have e : g x = (g x - x) + x := by abel
        rw [e]; exact Submodule.add_mem _ this hx
      rw [← hu (g.symm v) x, LinearEquiv.apply_symm_apply]
      exact hv _ hgx
    have h1 := hperp _ hw
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : g.symm v - v = -(v - g.symm v) := by abel
    rw [e]; exact Submodule.neg_mem _ h1
  | one =>
    intro v _
    exact ⟨by simp, by show v - v ∈ _; simp⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    intro v hv
    have hm : ∀ x, (g₁ * g₂) x = g₁ (g₂ x) := fun _ => rfl
    have hms : ∀ x, (g₁ * g₂).symm x = g₂.symm (g₁.symm x) := fun _ => rfl
    obtain ⟨a2, b2⟩ := ih₂ v hv
    obtain ⟨a1, b1⟩ := ih₁ v hv
    have hv2 : g₂ v ∈ H.perp (H.X Fr.f) := by
      have e : g₂ v = (g₂ v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP a2) hv
    have hv1 : g₁.symm v ∈ H.perp (H.X Fr.f) := by
      have e : g₁.symm v = (g₁.symm v - v) + v := by abel
      rw [e]; exact Submodule.add_mem _ (hXP b1) hv
    refine ⟨?_, ?_⟩
    · rw [hm]
      have e : g₁ (g₂ v) - v = (g₁ (g₂ v) - g₂ v) + (g₂ v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₁ _ hv2).1 a2
    · rw [hms]
      have e : g₂.symm (g₁.symm v) - v = (g₂.symm (g₁.symm v) - g₁.symm v) + (g₁.symm v - v) := by abel
      rw [e]; exact Submodule.add_mem _ (ih₂ _ hv1).2 b1
  | inv g _ ih =>
    intro v hv
    exact ⟨(ih v hv).2, (ih v hv).1⟩

theorem z_mem_LamStd (H : HermSp M V) {r : ℕ} (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)}
    (hL : Fr.IsInner L) : Fr.z ∈ Fr.LamStd L := by
  obtain ⟨-, -, xz, hxz, hxzL, -⟩ := hL
  have hs : ∀ a, H.h Fr.z (Fr.es a) = 0 := fun a => h_swap_zero H (Fr.h_sz a)
  have he : ∀ a, H.h Fr.z (Fr.e a) = 0 := fun a =>
    Fr.h_iso (Fin.last r) a.castSucc (Or.inr (Fin.castSucc_ne_last a))
  refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, xz, ?_, hxzL⟩
  · rw [hs a]; exact zero_mem _
  · rw [he a]; exact zero_mem _
  · rw [hxz]
    simp [FrameD.prF, hs, he]

end Gen

variable {D : D7}

theorem exists_add_mem : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D)
    (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS),
    (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D,
    Submodule.IsLattice D.host.E Λ →
    (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) →
    ∃ x ∈ G.fl.X, G.fl.z + x ∈ Λ := by
  intro D T G Z A hA Λ hΛ hloc
  obtain ⟨π, hπX, hπmem⟩ : ∃ π : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ G.fl.X, π x = x) ∧ ∀ x, π x ∈ G.fl.X := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective G.fl.X.subtype (Submodule.ker_subtype _)
    refine ⟨G.fl.X.subtype ∘ₗ g, fun x hx => ?_, fun x => (g x).2⟩
    have := congrArg (fun f => ((f ⟨x, hx⟩ : G.fl.X) : (VS D).V)) hg
    exact this
  obtain ⟨Λ₁, hΛ₁⟩ : ∃ N : LV D, N = Λ ⊔ Submodule.span (𝓞 D.host.E) {G.fl.z} := ⟨_, rfl⟩
  obtain ⟨Λ₂, hΛ₂⟩ : ∃ N : LV D, N = Λ ⊔ Λ₁.map (π.restrictScalars (𝓞 D.host.E)) := ⟨_, rfl⟩
  have hfg : Λ₂.FG := by
    rw [hΛ₂, hΛ₁]; exact hΛ.fg.sup ((hΛ.fg.sup (Submodule.fg_span_singleton _)).map _)
  have hz : G.fl.z ∈ Λ₂ := by
    refine GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z hfg fun p => ?_
    obtain ⟨n, hn, L, hL, hlat⟩ := hloc p
    have hzp : (A p).z = baseChange₂ D p G.fl.z := by
      show (A p).f (Fin.last _) = _
      rw [hA p]
      simp [frFac, frame, FlagG.fvec]
    have hperp : (A p).z ∈ (locH Z p).perp ((locH Z p).X (A p).f) := by
      obtain ⟨-, -, xz, hxz, -, -⟩ := hL
      rw [← hxz]; exact xz.2
    have hnz : n (A p).z ∈ lattice₂ D Z.M p Λ := by
      rw [hlat]
      exact Submodule.mem_map_of_mem (z_mem_LamStd _ (A p) hL)
    have hxX := sub_mem_X_of_mem_N _ (A p) hn hperp
    have hfix : (locH Z p).X (A p).f ≤ LinearMap.eqLocus (GlobalTheory.LocExt.locEnd p π) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      show (GlobalTheory.LocExt.locEnd p π) ((A p).f a.castSucc) = (A p).f a.castSucc
      rw [hA p]
      rw [map_smul, GlobalTheory.LocExt.locEnd_bcP, GlobalTheory.LocExt.frame_castSucc,
        hπX _ (Submodule.subset_span ⟨a, rfl⟩)]
      show _ = frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)
      rw [GlobalTheory.LocExt.frame_castSucc]
    have hx1 : n (A p).z - (A p).z ∈ lattice₂ D Z.M p Λ₁ := by
      rw [hΛ₁]
      refine Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz) ?_
      rw [hzp]
      exact Submodule.subset_span ⟨G.fl.z, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), rfl⟩
    have hx2 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) ∈ lattice₂ D Z.M p (Λ₁.map (π.restrictScalars (𝓞 D.host.E))) := by
      rw [GlobalTheory.FrameProj.localLattice_map Z p π (GlobalTheory.LocExt.locEnd p π) (fun x => (GlobalTheory.LocExt.locEnd_bcP p π x).symm) Λ₁]
      exact Submodule.mem_map_of_mem hx1
    have hx3 : (GlobalTheory.LocExt.locEnd p π) (n (A p).z - (A p).z) = n (A p).z - (A p).z := hfix hxX
    rw [hx3] at hx2
    have e : baseChange₂ D p G.fl.z = n (A p).z - (n (A p).z - (A p).z) := by rw [hzp]; abel
    rw [e, hΛ₂]
    exact Submodule.sub_mem _ (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_left hnz)
      (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_right hx2)
  rw [hΛ₂] at hz
  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.1 hz
  obtain ⟨w, -, rfl⟩ := hy
  refine ⟨-(π w), Submodule.neg_mem _ (hπmem w), ?_⟩
  have e : G.fl.z + -(π w) = l := by
    rw [← hly]; simp
  rw [e]; exact hl

end GlobalTheory.IsotropicLift
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Norms

theorem sqrt_norm_eq (D : D7) (x : D.host.E) :
    Real.sqrt |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ w : InfinitePlace D.host.E, w x := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∏ w : InfinitePlace D.host.E, w x ^ w.mult = (∏ w : InfinitePlace D.host.E, w x) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => by rw [(IsTotallyComplex.isComplex w).mult_eq_two]
  rw [← Rat.cast_abs, ← h1, h2]
  exact Real.sqrt_sq (Finset.prod_nonneg fun w _ => w.1.nonneg _)

theorem prod_natPow (D : D7) (g m : ℕ) :
    ∏ w : InfinitePlace D.host.E, w ((g : D.host.E) ^ m) = ((g : ℝ) ^ m) ^ D.R.f := by
  rw [← Formalism.MainNotions.LatticeGluingRadicals.d_card D, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun w _ => by rw [map_pow, InfinitePlace.map_natCast]

theorem localInvariantNorm_eq_prod_infinitePlaces_div (D : D7) (T T' : D.host.E) (Z : Formalism.L2.SG.CntLocal.MatZ D) :
    Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram T T' Z =
      (∏ w : InfinitePlace D.host.E, w (Formalism.L2.SG.CntLocal.GZ T T' Z)) / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f := by
  unfold Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram
  rw [sqrt_norm_eq, ← prod_natPow, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun w _ => by rw [map_div₀]

theorem rd_pow_f (D : D7) : D.host.rdE ^ D.R.f = |(NumberField.discr D.host.F : ℝ)| := by
  have h := Formalism.MainNotions.BridgeLemma.szf_rd_pow D
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq] at h
  have hrd := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  refine (pow_left_inj₀ (by positivity) (abs_nonneg _) two_ne_zero).1 ?_
  rw [h]; push_cast; rw [abs_pow]

theorem one_le_tprod_real {ι : Type} (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i) : 1 ≤ ∏' i, a i := by
  by_cases h : Multipliable a
  · refine ge_of_tendsto' h.hasProd fun s => ?_
    exact Finset.one_le_prod₀ (fun i _ => ha i)
  · rw [tprod_eq_one_of_not_multipliable h]

theorem one_le_nM {K V : Type} [Field K] [NumberField K] [StarRing K] (F : Type) [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    1 ≤ Formalism.L2.SG.Pf.Cnt.nM F h U M := by
  unfold Formalism.L2.SG.Pf.Cnt.nM
  refine one_le_tprod_real _ fun p => one_le_pow₀ ?_
  have h0 : p.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField F)
  have h1 : Ideal.absNorm p.1 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h1

theorem m_eq (D : D7) : D.R.m = 2 * D.R.rS + 2 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Ranks.rS
  omega

theorem norms_generic : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Λ : LV D) (w : Point D.host.E (D.R.rS + 1)), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → IsRowLat D (X.Fu u) Λ → G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G') → IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w → (∀ a, 1 ≤ ∏ v : InfinitePlace D.host.E, (D.host.rdE ^ (2 * (endIdx (toPts w) a * (2 * D.R.rS + 1 - endIdx (toPts w) a))))⁻¹ * v (endMin (toPts w) a) ^ 2) ∧ ((gS D : ℝ)) ^ ((2 * D.R.rS + 2) * Fintype.card (InfinitePlace D.host.E)) ≤ NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ∧ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) * Formalism.L2.SG.MassDataConc.ngFac D = PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
  intro D X Y u u' hT G' Λ w hzt hP hrow hE hcell
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' : G'.fl.z ∈ Λ := hE.1.1.1
  have hX' := hE.2.2.2.1.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ Λ := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame G' b ∈ Λ := PtPf.frame_mem _ hz' hX'
  have hrd := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  have hg : (0 : ℝ) < (gS D : ℕ) := by exact_mod_cast Formalism.MainNotions.LatticeGluingRadicals.z_gS_pos D
  have hGeq := LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) G' _ hcell
  set P : ℝ := ∏ v : InfinitePlace D.host.E, v (Gval (lf D (X.Fu u)) G') with hPdef
  have hNG : NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) =
      ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * P := by
    unfold NGPt
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D, hGeq, inv_pow,
      ← pow_mul, ← pow_mul, mul_comm D.R.f]
    rfl
  have hN0 : Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
      (ZhatL (lf D (X.Fu u)) G') = P / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f := localInvariantNorm_eq_prod_infinitePlaces_div D _ _ _
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have hj : endIdx (toPts w) a ≤ D.R.rS + 1 := (toPts w).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := LeadingMinorIntegrality.lead_mem hun (lf D (X.Fu u)) G' hz hX hz' hX' _ hj
    rw [← LeadingMinorIntegrality.lead_cell _ _ hcell, ← LeadingMinorIntegrality.endMin_eq] at e
    have hE5 := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    have h0 : endMin (toPts w) a ≠ 0 := (hE5 a).2
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D]
    have hsq := LeadingMinorIntegrality.prod_sq_ge _ o ho (by rw [e]; exact h0)
    rw [e] at hsq
    rw [inv_pow, ← div_eq_inv_mul, one_le_div (by positivity), ← pow_mul, mul_comm _ D.R.f, pow_mul]
    exact hsq
  · have hI := Formalism.L2.SG.Pf.Cnt.mmInt_of_EZ hT (Y.rowsOK u) hzt rfl hP hrow hE
    have hn := PI.UnitaryGroupMassFormula.CntFormula.R6.norm_mass_of_jordan D u u' hT (X.Fu u) (Y.what₂ u) (Y.rowsOK u) _ G' hzt rfl hP hI
    have h1 := one_le_nM D.host.F (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G')
      (Formalism.L2.SG.Pf.Cnt.MMof D (X.Fu u) G')
    replace h1 := h1.trans_eq hn
    rw [zpow_neg, zpow_natCast, ← rd_pow_f] at h1
    replace h1 : 1 ≤ ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ *
        (P / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f) := hN0 ▸ h1
    rw [← mul_div_assoc, one_le_div (by positivity)] at h1
    rw [hNG, Formalism.MainNotions.LatticeGluingRadicals.d_card D, ← m_eq, pow_mul]
    exact h1
  · have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [hN0, hNG, hv]
    unfold Formalism.L2.SG.MassDataConc.ngFac PN.abelian₂
    rw [sqrt_norm_eq, prod_natPow, ← mul_pow, div_mul_cancel₀ _ (by positivity)]
    have e : D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) * D.R.f) =
        ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1))) ^ (D.R.k - 1) := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [e, ← mul_pow, mul_inv_cancel_left₀ (by positivity)]

end GlobalTheory.GenMass.Norms
end
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.InvLenMomentGap

theorem inv_len_moment_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS hT ν q hν hq w hw a
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  have hS' := hS
  obtain ⟨hN, hF, hG, hSF⟩ := hS'
  have hb : 1 ≤ b := by
    obtain ⟨hk, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
    have e1 := h7 (Fin.last _) (by simp only [Fin.val_last]; omega)
    have e2 := h8 (Fin.last _)
    have e3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have e4 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := one_le_pow₀ e3
    have e5 := neg_abs_le (lam (Fin.last _))
    linarith [e1.2]
  have hdg : 0 < dg ν := (hSF ν hν).2.1
  obtain ⟨m1, -, m3, m4⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hH.1.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq
    (hF ν hν) hG
  refine GlobalTheory.T.weightedMass_highestToLowestKType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν
    (fun y => (y a)⁻¹ ^ (2 * q)) _ (by fun_prop) (fun y => Even.pow_nonneg (even_two_mul q) _) ?_ w hw
  intro Q E hQ hE v hv hv1
  have hmass := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν).1 v v.2
  have hv1' : ‖(v : (R ν).H)‖ = 1 := hv1
  simp only [one_mul, hv1', one_pow, ENNReal.ofReal_one] at hmass
  have hpos : ∀ᵐ x ∂νq, 1 ≤ lenA k r z (Matrix.of x) (Fin.last r) ∧ ∀ c, 0 < lenA k r z (Matrix.of x) c := by
    filter_upwards [m1] with x hx
    obtain ⟨e1, e2⟩ := GlobalTheory.T.last_majorant_length_sq_ge_and_pos k r z hG.1 hG.2.1 _ hx
    refine ⟨?_, fun c => (e2 c).1⟩
    have := (e2 (Fin.last r)).1
    nlinarith
  have hmeas : AEMeasurable (fun x : Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) νq :=
    (((m4 (lb ν) (hSF ν hν).1.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _
  have key := GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one (Mt k r) νq r q
    (fun c x => lenA k r z (Matrix.of x) c.succ / lenA k r z (Matrix.of x) c.castSucc)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (b ^ 2)
    (Finset.univ.filter (fun c : Fin r => a.val ≤ c.val))
    (fun c => (m3 _).div (m3 _))
    (fun c => by
      filter_upwards [hpos] with x hx
      exact div_nonneg (hx.2 _).le (hx.2 _).le)
    hmeas (fun x => by positivity) hmass (one_le_pow₀ hb)
    (fun c => by
      have := Gp91.GlobalTheory.T.family_setup_cayley_bound hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ hE ν hν
        0 (r * q) (by omega) c v hv
      rwa [hv1, one_pow, mul_one] at this)
  have hpw : (b ^ 2) ^ (2 * (r * q)) = (b ^ (2 * r)) ^ (2 * q) := by
    rw [← pow_mul, ← pow_mul]; congr 1; ring
  rw [← hpw]
  refine le_trans (lintegral_mono_ae ?_) key
  filter_upwards [hpos] with x hx
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [GlobalTheory.InvLenMoment.prod_ratio (fun c => lenA k r z (Matrix.of x) c) hx.2 a]
  refine pow_le_pow_left₀ (inv_nonneg.2 (hx.2 a).le) ?_ _
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hx.1 (hx.2 a).le

end GlobalTheory.InvLenMomentGap
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_clsOm_le_datBd : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E) (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS) (A : Finset (GTu Y u)), A.Nonempty → (∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) → ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤ GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x := by
  intro D large₂ X Y u hStd W HW he Λ j x δ d N A hA hT
  obtain ⟨hK, -, -, -, hf, -, -, -, -, -, hV, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd
  have hgS : 1 ≤ gS D := by omega
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨-, -, hj0, hδ0, hAd0, hTm0, hg0, -⟩ := hT t₀ ht₀
  obtain ⟨-, -, hLDel, hLDb, -⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t₀ (N t₀) hAd0
  obtain ⟨-, hx1, -, -, hfW⟩ := GlobalTheory.T.embeddedDatum_of_term_definiteSpace D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t₀)
    (dI D) (N t₀) (gS D) Λ hgS he hAd0 hTm0
  obtain ⟨-, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS (N t₀) (gS D) Λ hgS hTm0
  rw [hg0] at hx1
  rw [hLDel, hj0, hδ0] at hDel1
  rw [hLDb, hj0, hδ0] at hDb1
  let G : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) → Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := fun b =>
    if hb : ∃ t ∈ A, frCls Λ t = b then Ft hb.choose else F0 X u
  have hGb : ∀ b ∈ A.image (frCls Λ), ∃ t ∈ A, frCls Λ t = b ∧ G b = Ft t := by
    intro b hb
    have hb' : ∃ t ∈ A, frCls Λ t = b := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := hb'.choose_spec
    exact ⟨hb'.choose, h1, h2, by simp only [G, dif_pos hb']⟩
  have key := GlobalTheory.DegAsm.sum_weights_per_datum D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (dI D)
    (gS D) j (Tu D u) x (fun l => star (δ l)) Λ d (k2Del D j δ) (DbL D j δ) (Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS))
    (A.image (frCls Λ)) G hgS hx1 hDel1 hDb1 he ?_ ?_ ?_
  · have hsum : ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b =
        ∑ b ∈ A.image (frCls Λ), GlobalTheory.DegAsm.omI (F0 X u) (G b) (dI D) Λ := by
      refine Finset.sum_congr rfl fun b hb => ?_
      obtain ⟨t, ht, hbt, hG⟩ := hGb b hb
      obtain ⟨-, hlt, -⟩ := hT t ht
      rw [hG, ← hbt, clsOm_frCls hK Λ t hlt]
      unfold omT
      rw [hlt]
    rw [hsum]
    refine key.trans (le_of_eq ?_)
    rw [show Module.finrank D.host.E W = D.R.k by omega, hf]
    rfl
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, hTmt, hgt, -⟩ := hT t ht
    obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t (N t) hAdt
    refine ⟨N t, ?_, hTmt, a1.trans hjt, a2, ?_, ?_, hgt⟩
    · rw [hG]; exact hAdt
    · rw [a3, hjt, hδt]
    · rw [a4, hjt, hδt]
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, -, -, hdt⟩ := hT t ht
    obtain ⟨-, -, -, -, a5⟩ := GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t (N t) hAdt
    refine ⟨?_, ?_⟩
    · rw [hG, ← hjt, a5, hδt]
    · rw [hG]; exact hdt
  · intro b hb b' hb' hE
    obtain ⟨t, -, hbt, hG⟩ := hGb b hb
    obtain ⟨t', -, hbt', hG'⟩ := hGb b' hb'
    rw [hG, hG'] at hE
    rw [← hbt, ← hbt']
    exact (frCls_eq_iff hK Λ t t').2 hE

end GlobalTheory.TypeAsm.PerRow
end
