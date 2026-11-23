module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle296
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle294
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle311
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle306
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle163
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle245
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompareIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle174
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle287
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import ReciprocityTheory.BasicDefinitions.ExistsUnique
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem senle_exists_coker {k G : Type} [Field k] [Group G] (A B : Ob k G)
    (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (C : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom B C q ∧ Function.Surjective q ∧ Function.Exact j q := by
  have hle : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (B.ρ g) := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨A.ρ g x, hj g x⟩
  obtain ⟨C, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) hle)
  refine ⟨C, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => ?_,
    e.surjective.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    rfl
  · simp [Submodule.Quotient.mk_eq_zero]

theorem senle_exists_ker {k G : Type} [Field k] [Group G] (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (C : Ob k G) (s : (Fin C.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom C A s ∧ Function.Injective s ∧ Function.Exact s p := by
  apply GlobalTheory.Models.SubModel.exists_ker <;> assumption

theorem sen_push_pre_le : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (B A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (w w' : ZMod n → ℤ) (N : Lats k n B.m), F.Obj B → IsHom A₁ B j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → ABC (F.D B) w w' N → ∀ i x, sen ((F.D A).γ i) (F.push A₁ A p (F.pre A₁ B j N) i) x ≤ sen ((F.D B).γ i) (N i) x := by
  intro k G _ _ l n _ _ _ R F B A₁ A j p w w' N hB hj hji hp hps hN i x
  have hA₁ : F.Obj A₁ := F.obj_sub A₁ B j hj hji hB
  obtain ⟨C, q, hq, hqs, hex⟩ := senle_exists_coker A₁ B j hj
  obtain ⟨K, s, hs, hsi, hex'⟩ := senle_exists_ker A₁ A p hp
  have h1 := GlobalTheory.T.senMultiplicity_additive_exact_sequence F A₁ B C j q N hB hj hq hji hqs hex i (hN.1 i) (hN.2.2 i) x
  have hsat := GlobalTheory.PhiGam.Sat.main R (F.D B) (F.D A₁) (F.map A₁ B j) (F.map_inj A₁ B j hA₁ hB hj hji)
    (F.map_φ A₁ B j hA₁ hB hj) (F.map_γ A₁ B j hA₁ hB hj) w w' N hN.1 hN.2.1 hN.2.2
  have h2 := GlobalTheory.T.senMultiplicity_additive_exact_sequence F K A₁ A s p (F.pre A₁ B j N) hA₁ hs hp hsi hps hex' i (hsat.1 i) (hsat.2.2 i) x
  omega

end GlobalTheory.Models
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise

namespace GlobalTheory.UnramCocycle

theorem conj_mem_ine_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g σ : G F Ω) (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  apply GlobalTheory.TripleUnramified.conj_mem_Ine_of_smul <;> assumption

def kerSub {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : Subgroup Γ where
  carrier := {n | x.1 n = 0 ∧ ∀ m, ρ n m = m}
  one_mem' := ⟨by simpa using x.2.2 1 1, fun m => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [x.2.2, ha, hb]; simp, fun m => ?_⟩
    rw [map_mul, mul_apply_eq_comp, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    · have h := x.2.2 a a⁻¹
      rw [mul_inv_cancel, h1, ha, ha', zero_add] at h
      exact h.symm
    · conv_lhs => rw [← ha' m]
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

theorem kerSub_normal {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : (kerSub ρ x).Normal where
  conj_mem := by
    intro n hn g
    obtain ⟨hx, hρ⟩ := hn
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    ·
      rw [x.2.2, x.2.2, hx, map_zero, add_zero, map_mul, mul_apply_eq_comp, hρ, ← x.2.2,
        mul_inv_cancel, h1]
    · rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hρ,
        ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]

theorem kerSub_isClosed {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (hρ : ContAction ρ) (x : Z1 ρ) :
    IsClosed (kerSub ρ x : Set Γ) := by

  have h1 : IsClosed {n : Γ | x.1 n = 0} := isClosed_eq x.2.1 continuous_const
  have hc : Continuous fun p : Γ × M => ρ p.1 p.2 := hρ
  have h2 : IsClosed {n : Γ | ∀ m, ρ n m = m} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun m =>
      isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
  exact h1.inter h2

theorem vanish_on_NS : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ ρ hρ A S htriv x hx
  have := kerSub_normal ρ x

  have hle : NS Ω S ≤ kerSub ρ x := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ (kerSub_isClosed ρ hρ x)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_compl_iff, exists_prop] at hσ
    obtain ⟨v, hv, B, hB, hσB⟩ := hσ

    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hB
    have hσ' : σ ∈ Ine (F := F) (g • A.1 v) := by rw [hg, mem_Ine]; exact hσB
    have hc := conj_mem_ine_of_smul (A.1 v) g σ hσ'

    have hzero : x.1 (g⁻¹ * σ * g) = 0 := by
      have hu := hx v hv
      unfold Formalism.GaloisCohomology.unrAt H1ur at hu
      rw [LinearMap.mem_ker] at hu
      unfold resH1 at hu
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hu
      obtain ⟨m, hm⟩ := hu
      have hmem : g⁻¹ * σ * g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hc
      have h := hm ⟨⟨g⁻¹ * σ * g, hmem⟩, (Subgroup.mem_subgroupOf).2 hc⟩

      have h' : x.1 (g⁻¹ * σ * g) = ρ (g⁻¹ * σ * g) m - m := h
      rw [htriv v hv (A.1 v) (A.2 v) _ hc, sub_self] at h'
      exact h'
    have hk : g⁻¹ * σ * g ∈ kerSub ρ x := ⟨hzero, htriv v hv (A.1 v) (A.2 v) _ hc⟩
    have h := (kerSub_normal ρ x).conj_mem _ hk g
    have e : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    rwa [e] at h
  exact fun n hn => hle hn

end GlobalTheory.UnramCocycle
end

section

noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitFor_of_tie (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W RA RW inclR φR gR πA)
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E := by
  intro e₀ h₀
  obtain ⟨e₁, f₀, hf₀, hj, hN⟩ := E.one_e
  obtain ⟨u, hu, hT⟩ := W.one_line
  have huT : u ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hf₀ ▸ Submodule.mem_top : e₀ ∈ Submodule.span O {f₀})
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (h₀ ▸ Submodule.mem_top : f₀ ∈ Submodule.span O {e₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] e₀ := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hde : d • (c • e₁) = e₁ := by
    apply E.jD_inj
    rw [map_smul, hje, hj, ← hd, TensorProduct.tmul_smul]
  refine ⟨c • e₁, hje, ⟨fun x y hxy => ?_, ?_⟩, ?_, fun g => ?_, ?_⟩
  · have h1 := congrArg (E.jD W.one) hxy
    simp only at h1
    rw [E.jD_smul, E.jD_smul, hje, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
    exact GlobalTheory.EtaleExact.ioE_injective E
      (GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one u hu huT e₀ h₀ _ _ h1)
  · have htop : Submodule.span W.EE {c • e₁} = ⊤ := by
      refine GlobalTheory.EtaleExact.eq_top_DD E hm W.one _ ?_
      rw [eq_top_iff]
      rintro z -
      have h1 : ((1 : RW) ⊗ₜ[O] e₀ : TW RW W.one) ∈ Submodule.span RW
          (E.jD W.one '' (Submodule.span W.EE {c • e₁} : Submodule W.EE (W.DD W.one))) :=
        Submodule.subset_span ⟨c • e₁, Submodule.mem_span_singleton_self _, hje⟩
      induction z using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | add a b ha hb => exact Submodule.add_mem _ ha hb
      | tmul r t =>
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1
          (h₀ ▸ Submodule.mem_top : t ∈ Submodule.span O {e₀})
        have h2 : (r ⊗ₜ[O] (a • e₀) : TW RW W.one) = (a • r) • ((1 : RW) ⊗ₜ[O] e₀) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
        rw [h2]
        exact Submodule.smul_mem _ _ h1
    intro z
    exact Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : z ∈ Submodule.span W.EE {c • e₁})
  · apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  · obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  · rw [hN]
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) d, by rw [algebraMap_smul, hde]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) c, by rw [algebraMap_smul]⟩

end Generic

theorem unitPart : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H), GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitPart l P AI H F := by
  intro l _ P AI H F K s LL h
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  have hp : (P.PD K).p = l := P.PD_p K
  refine unitFor_of_tie Subtype.val_injective _
    (GlobalTheory.EtaleExact.map_ne_top_of_tie (F.E K s LL h).tie ?_ ?_)
  · rw [hp]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL
  · rw [hp]
    exact GlobalTheory.EtaleExact.sep_RW LL

end GlobalTheory.WachUnit
end
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TopWindow

theorem exists_topData_galData : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → 5 ≤ (P.PD K).p →
    ∀ (t : ℕ) (h w η : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (typ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool)
      (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
      (χ : ℕ → ↥(GK K) →* (↥(OL LL))ˣ), tableLineDegreeTwo.TopHyp (P.PD K) (H.W K 1 LL hA.2.2).emb t h w η typ U T.ρ χ →
      (∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 T.V) →
      ∃ (r : ℕ) (D : TopData (Module.finrank ℚ_[l] ↥(K0 K)) r) (ε : ↥(GK K) →* (↥(OL LL))ˣ),
        GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL (H.W K 1 LL hA.2.2).emb D
          (GalData.mk lam T (χ 1) ε) ∧ D.t = t ∧
        (∀ i a, ((D.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
        ∀ c ∈ Finset.Icc 1 t,
          (GalData.mk lam T (χ 1) ε : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)).chi c = χ c := by
  intro l _ P H K LL hA lam hlam h5 t h w η typ U T χ hyp hc
  have hp : (P.PD K).p = l := P.PD_p K
  have hS : Standing P K LL (H.W K 1 LL hA.2.2).emb lam :=
    (GlobalTheory.SenCompare.standing_iff P H lam).2 ⟨hp ▸ h5, hA, hlam⟩
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hS⟩
  obtain ⟨ht, hposition, -, hcrys, hmult, hchi⟩ := hyp
  rw [hp] at hposition
  obtain ⟨D, hDt, hD, t1, t2, t3⟩ := GlobalTheory.TopWindow.exists_topData_of_positionHyps l _ t _ h w η typ U
    (Fact.out : l.Prime).two_le ht hc hposition
  obtain ⟨-, hcont1, hcrys1, hjump1⟩ := hchi 1 (Finset.mem_Icc.2 ⟨le_rfl, ht⟩)
  have hcyc : ∀ g, tableLineDegreeTwo.charL (LL := ↥LL.1) (GlobalTheory.AdmLoc.CycWitness.cycO P K LL) g =
      Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g := fun g => Units.ext (GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL g)
  refine ⟨_, D, GlobalTheory.AdmLoc.CycWitness.cycO P K LL,
    ⟨hS, ⟨rfl, ⟨hcrys, fun i τ hτ a => ?_⟩, ⟨hcont1, hcrys1, fun i τ hτ a => ?_⟩,
      GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL⟩, t1, t2, t3⟩, hDt, fun i a => (hD i).2.2 a, fun c hc' => ?_⟩
  · rw [(hD i).2.1]
    exact hmult i τ (AlgHom.ext fun x => hτ x) a
  · refine (hjump1 i τ (AlgHom.ext fun x => hτ x) a).trans ?_
    show _ = ((Multiset.count a {D.w i} : ℕ) : ℤ)
    rw [(hD i).1, Multiset.count_singleton]
    push_cast
    simp only [add_sub_cancel_right]
  · obtain ⟨hχc, -⟩ := hchi c hc'
    refine MonoidHom.ext fun g => ?_
    apply Units.map_injective (f := (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom) Subtype.val_injective
    change tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1 * GlobalTheory.AdmLoc.CycWitness.cycO P K LL ^ (-((c : ℤ) - 1))) g =
      tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c) g
    rw [hχc g, ← hcyc g]
    simp [tableLineDegreeTwo.charL, map_zpow]

end GlobalTheory.TopWindow
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.coeff_det_pencil_mem_heckeAlgebra : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ a b : X → Matrix (Fin n) (Fin n) O, InRing T rep a → InRing T rep b → ∀ j : ℕ, (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) + (b x).map (Polynomial.C (R := O)))).coeff j) ∈ T := by
  first | exact @GlobalTheory.SpanRing.coeff_det_pencil_mem | exact GlobalTheory.SpanRing.coeff_det_pencil_mem | (intros; apply GlobalTheory.SpanRing.coeff_det_pencil_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep : ∀ (l : ℕ) [Fact l.Prime] {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {n r t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (π : X) (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))), 2 ≤ r → Submodule.span A (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ eB e1 : X → Matrix (Fin n) (Fin n) A, (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧ (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧ ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧ ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0) := by
  first | exact @GlobalTheory.SpanIdem.exists_orthogonal_idempotents | exact GlobalTheory.SpanIdem.exists_orthogonal_idempotents | (intros; apply GlobalTheory.SpanIdem.exists_orthogonal_idempotents <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.ConjLatticeSelmer

theorem extCond_eq_bkG (L : LocTheory) {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂)
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [Algebra ℤ_[l₁] O₀] [Module.Finite ℤ_[l₁] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O] [Module.Finite ℤ_[l₂] O] [TopologicalSpace O]
    (B₀ : LocBridge l₁ E Ω Gw O₀) (B : LocBridge l₂ E Ω Gw O) (h₀ : ∀ x, x ∈ A ↔ ‖B₀.j x‖ ≤ 1)
    (h₁ : ∀ x, x ∈ A ↔ ‖B.j x‖ ≤ 1) (f : O₀ →+* O) (hf : Function.Injective f) {k : ℕ}
    (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (M : ↥Gw →* Matrix (Fin k) (Fin k) O) (hM : M = mapM f M₀) :
    extCond f hf (WKG M₀) (Br.bkG B₀ (L l₁) (WKG M₀) M₀) (WKG M) = Br.bkG B (L l₂) (WKG M) M := by
  subst h hM
  cases Subsingleton.elim i₁ i₂
  obtain ⟨σ, hσ⟩ := GlobalTheory.EmbUnitBallConj.exists_conj l₁ Ω B₀.j B.j fun x => (h₀ x).symm.trans (h₁ x)
  have he : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l₁) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l₁) * σ⁻¹ := by
    intro g
    refine GlobalTheory.padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed l₁ Ω B.j _ _ fun x => ?_
    rw [B.e_comm, ← hσ, ← hσ, ← B₀.e_comm]
    simp
  have hz := DFunLike.congr_fun
    (padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O))
  exact le_antisymm (GlobalTheory.BlochKatoBaseChangeLe.extCond_le_bkG l₁ (L l₁) E Ω Gw O₀ O B₀ B σ he f hf hz k M₀)
    (GlobalTheory.BlochKatoBaseChange.bkG_le_extCond l₁ (L l₁) E Ω Gw O₀ O B₀ B σ he f hf hz k M₀)

variable (D : D7)

theorem selT_eq_selG (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O a)ˣ)
    (hψ : ∀ v ∈ placesOver D.host.E (D.nd.l a), ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1) :
    selT D.loc D.ntwbr _ s (D.nd.Q a) (D.ntw.twist₂ a) (twO_inj D.ntw a) ψ =
      Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (↑(D.nd.S a) ∪ ↑(D.nd.Q a))
        (latTpsi D.ntw _ s (D.ntw.twist₂ a) ψ) := by
  have hl := D.ntw.twOf_l a
  have hS : setS D.ntw (D.ntw.twOf a) = ↑(D.nd.S a) := by
    rw [← TwistedTriples.badS_eq D a]
    unfold setS TwistedTriples.badS
    rw [hl]
  unfold selT Br.selG
  congr 1
  funext v
  unfold Formalism.GaloisCohomology.bkCond
  rw [hS]
  by_cases hv : v ∈ placesOver D.host.E (D.nd.l a)
  · have hv' : v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by rw [hl]; exact hv
    refine (if_pos hv').trans (Eq.trans ?_ (if_pos hv).symm)
    unfold condL Br.LlG
    rw [dite_eq_left hv, dite_eq_left hv']
    have := IsAlgClosure.isAlgClosed D.host.E (K := D.nd.Om)
    refine extCond_eq_bkG D.loc hl (D.nd.plOm.1 v) (D.ntwbr _ v hv') (D.nbr a v hv) (D.ntwbr_ind _ v hv')
      (D.nbr_ind a v hv) (D.ntw.twist₂ a) (twO_inj D.ntw a) ((latT D.ntw _ s).comp (decS D.nd v))
      ((latTpsi D.ntw _ s (D.ntw.twist₂ a) ψ).comp (decS D.nd v)) ?_
    ext g i j
    simp [latTpsi, twistM, mapM, hψ v hv g.1 g.2]
  · have hv' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by rw [hl]; exact hv
    exact (if_neg hv').trans (if_neg hv).symm

theorem nlen_congr {O : Type} [CommRing O] (l : ℕ) (M N : Type) [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (h : Module.length O M = Module.length O N) :
    nlen (O := O) l M = nlen (O := O) l N := by
  unfold nlen lenUnit
  rw [h]

theorem sPiTop_eq_sTLoc (a : D.nd.Loc) (π : D.nd.X a)
    (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (s : D.ntw.Sig (D.ntw.twOf a))
    (U : GL (Fin D.R.r) (D.nd.O a))
    (hU : ∀ g, WpO D.nd a ρ π g * (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) =
      (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) * latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g) :
    sPiTop D a ρ π = sTLoc D a s := by
  unfold sPiTop sTLoc sT
  rw [selT_eq_selG D a s _ fun v hv => D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v), D.ntw.twOf_l]
  exact nlen_congr _ _ _ (GlobalTheory.T.selG_length_eq_of_conj _ _ D.nd.plOm (D.nd.l a) (D.nd.O a) (D.loc (D.nd.l a)) (D.nbr a)
    (↑(D.nd.S a) ∪ ↑(D.nd.Q a)) _ _ _ U hU).symm

end GlobalTheory.ConjLatticeSelmer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.finiteDimensional_Dst_of_isSst' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → FiniteDimensional ℚ_[l] ↥(Dst P ρ) := by
  first | exact @GlobalTheory.Pst.finiteDimensional_Dst_of_isSst | exact GlobalTheory.Pst.finiteDimensional_Dst_of_isSst | (intros; apply GlobalTheory.Pst.finiteDimensional_Dst_of_isSst <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobeniusTensor_crisToSemistable_comm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (w : V ⊗[ℚ_[l]] P.R.B), phiV P ℚ_[l] V (crisIncl P ℚ_[l] V w) = crisIncl P ℚ_[l] V (φVB (P.PD K) (LL := ℚ_[l]) (V := V) w) := by
  first | exact @GlobalTheory.PMon.phiV_crisIncl_comm | exact GlobalTheory.PMon.phiV_crisIncl_comm | (intros; apply GlobalTheory.PMon.phiV_crisIncl_comm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.lTensor_semistable_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  first | exact @GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant | exact GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant | (intros; apply GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant <;> assumption)
end
