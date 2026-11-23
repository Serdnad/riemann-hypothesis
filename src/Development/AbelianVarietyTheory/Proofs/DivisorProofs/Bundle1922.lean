module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.localAddCharUnramified_of_splitsCompletelyAbovePlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully D.host.E v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr W.ψ v := by
  first | exact @GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully | exact GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully | (intros; apply GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaAdmitted

theorem summable_one_add_norm_inv_pow {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

variable (F : Type) [Field F] [NumberField F]

theorem norm_thetaSum_pureA_le {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  set L := GlobalTheory.WeilM.denomLattice F κ N with hLdef
  set k := Module.finrank ℤ L + 1 with hkdef
  have hu : Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := summable_one_add_norm_inv_pow L (Nat.lt_succ_self _)
  set M := ∑' z : L, ((1 + ‖z‖)⁻¹) ^ k with hMdef
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hM0 : 0 ≤ M := tsum_nonneg fun z => by positivity
  refine ⟨Finset.Iic (k, 0), B * 2 ^ k * M, by positivity, fun f => ?_⟩
  set S := (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ) f with hSdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hf : ∀ x, ‖f x‖ ≤ 2 ^ k * S * ((1 + ‖x‖)⁻¹) ^ k := by
    intro x
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl f x
    rw [norm_iteratedFDeriv_zero] at h
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  let Sset : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ L}
  have hsupp : ∀ ξ, ξ ∉ Sset → g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) = 0 := by
    intro ξ hξ
    by_contra h0
    apply hξ
    refine fun i => ?_
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  have hΦ : GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn := GlobalTheory.WeilM.summable_norm_of_mem_schA F hΦ
  let a : (κ → F) → ℂ := fun ξ => GlobalTheory.WeilM.pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
  have ha : ∀ ξ, a ξ = f (fun i => mixedEmbedding F (ξ i)) *
      g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) := fun ξ => GlobalTheory.WeilM.pureA_algebraMap F f g ξ
  have hsupa : Function.support (fun ξ => ‖a ξ‖) ⊆ Sset := by
    intro ξ hξ
    by_contra h
    apply hξ
    simp only [ha, hsupp ξ h, mul_zero, norm_zero]
  let j : Sset → L := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hle : ∀ ξ : Sset, ‖a ξ‖ ≤ B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := by
    intro ξ
    have h1 := hB (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))
    have h2 : ‖f (fun i => mixedEmbedding F (ξ.1 i))‖ ≤ 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := hf (j ξ)
    rw [ha, norm_mul]
    calc ‖f (fun i => mixedEmbedding F (ξ.1 i))‖ * ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))‖
        ≤ (2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k) * B := mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := by ring
  have hsumS : Summable fun ξ : Sset => B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k :=
    (hu.comp_injective hj).mul_left _
  calc ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)‖ = ‖∑' ξ, a ξ‖ := rfl
    _ ≤ ∑' ξ, ‖a ξ‖ := norm_tsum_le_tsum_norm hsn
    _ = ∑' ξ : Sset, ‖a ξ‖ := (tsum_subtype_eq_of_support_subset hsupa).symm
    _ ≤ ∑' ξ : Sset, B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k :=
        Summable.tsum_le_tsum hle (hsn.subtype _) hsumS
    _ = B * 2 ^ k * S * ∑' ξ : Sset, ((1 + ‖j ξ‖)⁻¹) ^ k := tsum_mul_left
    _ ≤ B * 2 ^ k * S * M := by
        gcongr
        exact tsum_comp_le_tsum_of_inj hu (fun z => by positivity) hj
    _ = B * 2 ^ k * M * S := by ring

theorem exists_admitted_form_eq_adelicThetaDistribution_alt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  intro F _ _ κ _
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (GlobalTheory.WeilM.thetaLin F κ)
  have hl' : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := fun Φ hΦ => by
    have := LinearMap.congr_fun hl ⟨Φ, hΦ⟩
    simpa using this
  refine ⟨l, ?_, hl'⟩
  intro g hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun f => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)) ?_ ?_ (norm_thetaSum_pureA_le F hg), fun f => ?_⟩
  · intro f₁ f₂
    have : GlobalTheory.WeilM.pureA F (f₁ + f₂) g = GlobalTheory.WeilM.pureA F f₁ g + GlobalTheory.WeilM.pureA F f₂ g := by
      funext x; simp [GlobalTheory.WeilM.pureA, add_mul]
    rw [this, GlobalTheory.WeilM.thetaSum_add F (hmem f₁) (hmem f₂)]
  · intro c f
    have : GlobalTheory.WeilM.pureA F (c • f) g = c • GlobalTheory.WeilM.pureA F f g := by
      funext x; simp [GlobalTheory.WeilM.pureA, mul_assoc]
    rw [this, GlobalTheory.WeilM.thetaSum_smul]
    rfl
  · rw [hl' _ (hmem f)]
    rfl

end GlobalTheory.ThetaAdmitted
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.traceSymplectic_self_zero_splitSupported : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
    (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∨ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) →
    ∀ ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E),
      symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u = 0 := by
  first | exact @GlobalTheory.VacIso.symp_self_eq_zero | exact GlobalTheory.VacIso.symp_self_eq_zero | (intros; apply GlobalTheory.VacIso.symp_self_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)), U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) →
    ∃ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v)) ∧
      IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ∧
      (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) ∈ O ∧
        ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v) → g ∈ K) ∧ (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ⊆ U := by
  first | exact @GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place | exact GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place | (intros; apply GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.lintegral_normSq_componentTensor_eq_const_mul : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (r : (κ → AF F) → ℂ),
    @Measurable _ _ (borel _) _ r →
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) →
    ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ K : Set (κ → Fv F v), IsCompact K → (interior K).Nonempty →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ φ : (κ → Fv F v) → ℂ, Continuous φ → HasCompactSupport φ →
      ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul | exact GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul | (intros; apply GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.exists_rational_darboux_coordinates_tensor_hermitian : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) := by
  first | exact @GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood | exact GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood | (intros; apply GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.exists_subgroup_symplecticAnnihilator_localField : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ {κ : Type} [Fintype κ] (N : Set ((κ → Fv F v) × (κ → Fv F v))), N ∈ nhds 0 →
    ∃ Y : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)),
      (∀ w' : (κ → Fv F v) × (κ → Fv F v), (∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1) → w' ∈ N) ∧
      ∃ N' ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w' ∈ N', ∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1 := by
  first | exact @GlobalTheory.SympDualNbhd.exists_dual_nbhd | exact GlobalTheory.SympDualNbhd.exists_dual_nbhd | (intros; apply GlobalTheory.SympDualNbhd.exists_dual_nbhd <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.tensorLatticeSplitPlace_eq_add_componentParts : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γA ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γB ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
        γ = γA + γB ∧ γA.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
          γB.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 := by
  first | exact @GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts | exact GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts | (intros; apply GlobalTheory.SplitPlaceLat.latAtV_eq_add_parts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.eventually_selfDualLattice_indicator_is_vacuum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  first | exact @GlobalTheory.VacIndic.eventually_isVac_indicator | exact GlobalTheory.VacIndic.eventually_isVac_indicator | (intros; apply GlobalTheory.VacIndic.eventually_isVac_indicator <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.standardAddChar_symplectic_local_lattice_eq_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (θ : 𝓞 E) (b : AF F),
    GlobalTheory.AdelicU.evFin F v b ∈ v.adicCompletionIntegers F →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (b * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') = 1 := by
  first | exact @GlobalTheory.LatVacArith.psi_symp_latAtV | exact GlobalTheory.LatVacArith.psi_symp_latAtV | (intros; apply GlobalTheory.LatVacArith.psi_symp_latAtV <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.TraceDualChar

theorem psi_trivial_on_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ z ∈ GlobalTheory.EvAdm.scaledInt F κ a,
      ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
  intro F _ _ ψ hψ κ _ a _ b hb z hz

  have hrat : ∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ψ (((0 : InfiniteAdeleRing F), ∑ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
    intro ξ hξ
    obtain ⟨k, hk⟩ := hb ξ hξ
    set q : F := ∑ i, ξ i * b i with hq
    have e1 : (∑ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hq, map_sum]; simp only [map_mul]
    rw [e1]
    set y : AF F := (((algebraMap F (InfiniteAdeleRing F) q), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F) with hy
    have e2 : (show AF F from ((0 : InfiniteAdeleRing F), algebraMap F (FiniteAdeleRing (𝓞 F) F) q)) + y =
        algebraMap F (AF F) q := by
      rw [hy]
      show (show AF F from ((0 : InfiniteAdeleRing F) + algebraMap F (InfiniteAdeleRing F) q,
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q + 0)) = algebraMap F (AF F) q
      rw [zero_add, add_zero]
      rfl
    have hAt : At (evI F) y := by
      intro u hu
      have hu1 : u.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
      show (u.1 * algebraMap F (InfiniteAdeleRing F) q, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
      rw [hu1, zero_mul, mul_zero]
    have hev : evI F y = mixedEmbedding F q := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      rfl
    have hyv : ψ y = 1 := by
      rw [hψ.2.2 y hAt, hev, GlobalTheory.PsiNontriv.trace_mixedEmbedding, hk]
      rw [show ((((k : ℚ) : ℝ) : ℂ)) = (k : ℂ) by push_cast; ring]
      rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-k)
    have h3 := congrArg ψ e2
    rw [AddChar.map_add_eq_mul, hyv, mul_one, hψ.2.1] at h3
    exact h3

  by_contra hne
  set G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun z =>
    ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) with hG
  have hGc : Continuous G := by
    refine hψ.1.comp ?_
    refine Continuous.prodMk continuous_const ?_
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  have hU : IsOpen ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∩ G ⁻¹' {1}ᶜ) :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).inter (isOpen_compl_singleton.preimage hGc)
  have hd : DenseRange (fun ξ : κ → F => fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) :=
    DenseRange.piMap fun _ => GlobalTheory.AdeleCharTwist.denseRange_fin
  obtain ⟨ξ, hξ1, hξ2⟩ := hd.exists_mem_open hU ⟨z, hz, hne⟩
  exact hξ2 (hrat ξ hξ1)

end GlobalTheory.TraceDualChar
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_supportedAdele_splitPlace_matrix_coordinate_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  first | exact @GlobalTheory.VacLift.exists_lift | exact GlobalTheory.VacLift.exists_lift | (intros; apply GlobalTheory.VacLift.exists_lift <;> assumption)
end
