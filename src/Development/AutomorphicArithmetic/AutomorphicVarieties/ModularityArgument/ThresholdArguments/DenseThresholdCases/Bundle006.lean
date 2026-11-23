module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.CohTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle009
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af
namespace UpperTheory.GalN.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
theorem mkCsd'_alt [IsCMField F] (h : AutCsd0 ι r) (u : Continuous r → _root_.UpperTheory.V.Z.Win.WitA ι r) : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r := ⟨h, u⟩
theorem autCsd0_of_isAutCsdA [IsCMField F] (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) : AutCsd0 ι r := h.1
omit [NumberField F] in
theorem isAutomorphicOverImagQuad_of_isAutQA (h : _root_.UpperTheory.V.Z.Win.IsAutQA ι r) : IsAutomorphicOverImagQuad ι r := fun hc K _ _ _ _ _ _ h2 hi => (h hc K h2 hi).1
omit [NumberField F] in
theorem isAutQA_of_isAutomorphicOverImagQuad_of_witAQ (h : IsAutomorphicOverImagQuad ι r) (u : Continuous r → _root_.UpperTheory.V.Z.Win.WitAQ ι r) : _root_.UpperTheory.V.Z.Win.IsAutQA ι r :=
  fun hc K _ _ _ _ _ _ h2 hi => ⟨h hc K h2 hi, u hc K h2 hi⟩
end Conv
end UpperTheory.GalN.V
end
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.QuadraticCharacterUnramified
end GlobalTheory.QuadraticCharacterUnramified
theorem _root_.GlobalTheory.T.inertia_le_range_of_unramified_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ η : HChar F, IsQuadCharOf K η → ∀ (u : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A u → η.UnrAt u → Ine (F := F) A ≤ (res F Ω K).range := by
  intro N F Ω _ _ _ _ _ K _ _ _ _ _ _ h2 η hq u A hA hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, ha⟩ := N.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι
    (isAlgPos_zero_of_orderDvd two_pos (GlobalTheory.QuadraticCharacterUnramified.orderDvd_two hq))
  obtain ⟨ε, hεc, -, hε, hεu⟩ := UpperTheory.exists_quadratic_sign_character F K Ω 2 h2
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv B hB =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hB).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hB hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  have hS := Filter.eventually_cofinite.1 ((GlobalTheory.QuadraticCharacterUnramified.good (K := K) hq).and hεu)
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
    (f := fun s => δ s) (f' := fun s => ε s) hδc hεc fun v hv _ B hB σ hσ => by
      obtain ⟨⟨w, hwv, hu', hval⟩, hεv⟩ := not_not.1 hv
      subst hwv
      have h1 := (hE _ hu' B hB).2 σ hσ
      have h3 := (UpperTheory.frobenius_sign_compatibility F K Ω 2 ι ε hε w hεv B hB).2 σ hσ
      have e : δ σ⁻¹ = ε σ⁻¹ := Units.ext (ι.injective (by rw [h1, h3, hval]))
      rwa [map_inv, map_inv, inv_inj] at e
  intro s hs
  have h1 : δ s = 1 := (hL.unr_iff ha (Or.inr rfl) hA).2 hu s hs
  have h3 : ε s = 1 := by
    have e : δ s = ε s := congrFun key s
    rw [← e, h1]
  exact (hε.1 s).1 h3
end
end

section




section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
theorem UpperTheory.V.Af.clozelCohC_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Published.ClozelCohC := by
  intro lit E _ _ _ a ha π Ξ h
  choose m h1 h2 using h
  have hd : ∀ τ, GlobalTheory.WignerGL.HasDualInfChar Ξ τ (m τ) := fun τ => (dualIff E a Ξ τ _).1 (h2 τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨m', e1, e2, e3⟩ := GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ
    have e : m τ = m' := msetSep _ _ fun u => by
      haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
      exact smul_left_injective ℂ one_ne_zero (((hd τ).2 u).symm.trans (e1.2 u))
    have h3 : (CG.mk π).HasInfChar τ (m τ) := h1 τ
    rw [h3.infChar_eq, e]
    exact ⟨e2, e3⟩
  obtain ⟨Ξ', hΞ'⟩ := lit.aut.coh E a ha π hreg
  choose m' g1 g2 g3 using GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ'
  have e : m = m' := by
    by_contra hne
    exact wigner E a π Ξ' m m' h1 g1 hne hΞ'
  subst e
  obtain ⟨T, hT⟩ := algIso E a Ξ' Ξ (fun τ => (m τ).map Neg.neg) (fun τ => (dualIff E a Ξ' τ _).2 (g1 τ)) h2
  exact cohTransport E a π Ξ' Ξ T hT hΞ'
end
end

section




section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.U
theorem pt_s (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : GlobalTheory.Published.PoitouTateDuality := GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hN.coh.pt
theorem locPrints_of_litN (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩
end UpperTheory.V.HV.U
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LocCompCLit
open Matrix
section
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩
private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩
end
theorem main_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → LocCompC := by
  intro H E _ _ _ a π w
  refine ⟨(LocEx.exists_isLocComp H.aut.fin E a π w).imp fun _ h => h.1, fun σ hσ => ?_⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w)
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)
end GlobalTheory.LocCompCLit
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.TypeConj
open GlobalTheory.PRep
section General
variable {G V V' W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
variable [TopologicalSpace G] [IsTopologicalGroup G]
end General
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
section Loc2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
end Loc2
section Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {n : ℕ}
end Gal
end UpperTheory.V.Hi.TypeConj
open UpperTheory.V.Hi.TypeConj in
abbrev _root_.UpperTheory.V.Hi.typeConj_s_ty : Prop :=
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion L) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ (γ : ℂ ≃+* ℂ) (σ σ' : SmIrr (GLw n w)) (f : σ.V ≃+ σ'.V), (∀ (z : ℂ) v, f (z • v) = γ z • f v) → (∀ g v, f (σ.ρ g v) = σ'.ρ g (f v)) → ∀ χ : Fin n → Dec (F := L) A →* ℂˣ, (∀ i, IsOpen ((χ i).ker : Set (Dec (F := L) A))) → IsTypeWD h (fun i => (χ i).comp (Subgroup.inclusion (Ine_le_Dec A))) (rc (algNorm σ)) → IsTypeWD h (fun i => W.pushCh γ.toRingHom ((χ i).comp (Subgroup.inclusion (Ine_le_Dec A)))) (rc (algNorm σ'))
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem cu_ext {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) [IsHausdorff I R] {S : Set Γ}
    (hS : Dense S) {f g : Γ → R} (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (h : ∀ x ∈ S, f x = g x) : f = g := by
  funext x
  refine IsHausdorff.eq_iff_smodEq (I := I).2 fun N => ?_
  rw [smul_eq_mul, Ideal.mul_top]
  letI : TopologicalSpace (R ⧸ I ^ N) := ⊥
  haveI : DiscreteTopology (R ⧸ I ^ N) := ⟨rfl⟩
  exact congrFun (Continuous.ext_on hS (hf N).continuous (hg N).continuous fun y hy => by simp only [h y hy]) x
private theorem cu_prod {n : ℕ} {M : Type} [CommGroup M] (f g : Fin n → M)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) : ∀ j, f j = g j := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hj : j ∈ Finset.univ.filter fun i => i ≤ j :=
      Finset.mem_filter.2 ⟨Finset.mem_univ j, le_rfl⟩
    have e := h j
    rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ g hj,
      Finset.prod_congr rfl (g := g) fun i hi => ih i (by
        rw [Finset.mem_erase, Finset.mem_filter] at hi
        exact lt_of_le_of_ne hi.2.2 hi.1)] at e
    exact mul_right_cancel e
private theorem cu_gen {W M k : Type} [Group W] [Group M] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : W →* kˣ) (ha : Function.Surjective a) (f g : W →* M)
    (h1 : ∀ s (y : Uo k), a s = y → f s = g s) (h2 : ∀ s, a s = unif k → f s = g s) (s : W) : f s = g s := by
  obtain ⟨p, hp⟩ := ha (unif k)
  have e := h1 (s * (p ^ ord k (a s))⁻¹) ⟨_, GlAx.val_div_ord (a s)⟩ (by
    rw [map_mul, map_inv, map_zpow, hp]
    exact (div_eq_mul_inv _ _).symm)
  rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, h2 p hp] at e
  exact mul_right_cancel e
theorem UpperTheory.V.Hi.core_unique_of_axioms_weight_char :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    ∀ (D' : W.GDet n (H.TK θ a K) H.Gq) (ψ' : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D' ψ' → D' = D ∧ ψ' = ψ := by
  intro _ L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ _ a K _ _ D ψ hU D' ψ' hU'
  refine ⟨UpperTheory.V.CA.d_gext D' D fun g i _ _ => congrFun (cu_ext _ hA.dense (hU'.cont i) (hU.cont i) ?_) g, ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    simp only [W.GDet.lam, hU.frob ⟨w, hw⟩ B σ hB hσ, hU'.frob ⟨w, hw⟩ B σ hB hσ]
  · funext v i
    have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec (H.ovr v))) := UpperTheory.weil_group_dense_in_galois_group L Ω _ _ (H.ovr v)
    refine MonoidHom.ext fun g => Units.ext (congrFun (cu_ext _ hd (hU'.ψ_cont v i) (hU.ψ_cont v i) ?_) g)
    rintro _ ⟨s, rfl⟩
    refine congrArg Units.val (cu_gen (H.art v) (hA.art_spec v).surj ((ψ' v i).comp _) ((ψ v i).comp _)
      (fun s y hy => ?_) (fun s hs => ?_) s)
    · have e := (hU'.ψ_unit v i s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) y rfl hy)
      have e' := (hU.ψ_unit v i s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) y rfl hy)
      exact mul_right_cancel (inv_injective (Units.ext
        ((Units.eq_inv_of_mul_eq_one_left e).symm.trans (Units.eq_inv_of_mul_eq_one_left e'))))
    · exact mul_right_cancel (cu_prod _ _ (fun j => Units.ext
        ((hU'.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs).trans
          (hU.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs).symm)) i)
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
end
abbrev _root_.UpperTheory.V.Hi.psRec_s_ty : Prop :=
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (IsSubquotient σ.ρ (PS ω) ↔ ∀ s, (rc (algNorm σ)).charPol s = ∏ j, (X - C (ω j (a s) : ℂ)))
end
end

section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Hi.PsIrr
open GlobalTheory.SplitRead
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem eq_of_twist {χ ψ η : kˣ →* ℂˣ}
    (φ : (detRep (Fin 1) χ).Equiv (twist (detRep (Fin 1) ψ) (detChar (Fin 1) η))) : χ = ψ * η := by
  refine MonoidHom.ext fun x => Units.ext ?_
  let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar _ x
  have hg : Matrix.GeneralLinearGroup.det g = x := by
    ext; simp [g, Matrix.GeneralLinearGroup.scalar]
  obtain ⟨y, hy⟩ := φ.surjective 1
  have h1 := LinearMap.congr_fun (φ.isIntertwining' g) y
  have hy' : φ.toLinearMap y = 1 := hy
  have h2 : detRep (Fin 1) χ g y = (χ x : ℂ) • y := by simp [detRep, hg]
  simp only [LinearMap.comp_apply, h2, map_smul, hy'] at h1
  simpa [twist, detRep, ofChar, hg, mul_comm] using h1
private theorem irr_zero (ψ : Fin 0 → kˣ →* ℂˣ) : (prinSeries ψ).IsIrreducible := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp (points (Fin 0)) ((ofChar (torusChar ψ)).comp (leviTorus k (Fin 0)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun _ => c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
  have E : (detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prinSeries ψ) :=
    Representation.Equiv.mk' ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ (fun F => F.1.1 1)
      (fun c => rfl) (fun F => Subtype.ext (Subtype.ext (funext fun g => by rw [hg g])))
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E (isIrreducible_ofChar _)
set_option synthInstance.maxHeartbeats 400000 in
private theorem irr_prin (H : GlobalTheory.Published.TotallyDisjointProductIrreducible) (n : ℕ) :
    ∀ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) →
      (∀ i j, i ≠ j → ψ i ≠ ψ j ∧ ψ i ≠ ψ j * absPow k 1) → (prinSeries ψ).IsIrreducible := by
  induction n with
  | zero => exact fun ψ _ _ => irr_zero ψ
  | succ n ih =>
    intro ψ hψ hne
    let ψ₁ : Fin n → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd 1 i)
    let ψ₂ : Fin 1 → kˣ →* ℂˣ := fun _ => ψ (Fin.natAdd n 0)
    have happ : Fin.append ψ₁ ψ₂ = ψ := by
      have : ψ₂ = fun i => ψ (Fin.natAdd n i) := funext fun i => by rw [Subsingleton.elim i 0]
      rw [this]
      exact Fin.append_castAdd_natAdd
    have h₁ : (prinSeries ψ₁).IsIrreducible :=
      ih ψ₁ (fun i => hψ _) fun i j hij => hne _ _ fun h => hij (Fin.castAdd_injective _ _ h)
    have h₂ : (prinSeries ψ₂).IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (GlobalTheory.PrinSat.oneEquiv _ (hψ _)) (isIrreducible_ofChar _)
    let σ₁ : Irr k n := ⟨_, prinSeries ψ₁, isSmooth_parInd _ _, h₁⟩
    let σ₂ : Irr k 1 := ⟨_, prinSeries ψ₂, isSmooth_parInd _ _, h₂⟩
    have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
      refine H k n 1 n 1 σ₁ σ₂ _ _ _ _
        (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₁ (ψ := ψ₁) (fun i => hψ _) (.refl _))
        (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₂ (ψ := ψ₂) (fun i => hψ _) (.refl _)) ?_
      rintro a b h j hj ⟨φ⟩
      have e : ψ (Fin.castAdd 1 a) = ψ (Fin.natAdd n 0) * absPow k (j : ℂ) := eq_of_twist φ
      have hab : Fin.castAdd 1 a ≠ Fin.natAdd n 0 := fun h => by
        have hval := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, Nat.add_zero] at hval
        exact a.isLt.ne hval
      obtain rfl | rfl | rfl : j = -1 ∨ j = 0 ∨ j = 1 := by
        have := abs_le.1 hj
        omega
      · refine (hne _ _ hab.symm).2 ?_
        rw [e, mul_assoc, ← absPow_add]
        simp
      · exact (hne _ _ hab).1 (by simpa using e)
      · exact (hne _ _ hab).2 (by simpa using e)
    obtain ⟨E1⟩ := PrinProd.stage_one (k := k) ψ₁ ψ₂
    obtain ⟨E2⟩ := PrinProd.stage_two (k := k) ψ₁ ψ₂
    rw [← happ]
    exact GlobalTheory.Parabolic.isIrreducible_of_equiv (E1.trans E2) hirr
end UpperTheory.V.Hi.PsIrr
theorem UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ω : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow k 1) → (PS ω).IsIrreducible ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), π.IsIrreducible → IsSubquotient π (PS ω) → Nonempty (π.Equiv (PS ω)) := by
  intro H k _ _ _ _ n ω hω hne
  have hi : (PS ω).IsIrreducible := by
    refine PsIrr.irr_prin H.loc.disj n _
      (fun i => (hω i).mul (isSmoothChar_of_isUnram (isUnram_absPow k _))) fun i j hij => ⟨fun h => ?_, fun h => ?_⟩
    · exact (hne i j hij).1 (mul_right_cancel h)
    · rw [mul_right_comm] at h
      exact (hne i j hij).2 (mul_right_cancel h)
  exact ⟨hi, fun V _ _ π hπ hs => (hs.nonempty_equiv hπ hi).map fun e => e.symm⟩
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg
open IsLocalRing Matrix Formalism.MainNotions.N GlobalTheory.GalOfCusp
namespace UpperTheory.V.U3
namespace Dat
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
def IsAutIAlt [IsCMField K] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l))
    (hr : HasMult D.η r) : Prop :=
  _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (D.rhoK r hr) (cycBar K Ω l)⁻¹)
end Dat
end UpperTheory.V.U3
end
end
end
