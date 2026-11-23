module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle312
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle196
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle318
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle317
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.Lift.ThOps

theorem exists_restrict {Θ M : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M] (j : Θ →ₗ[ℂ] M)
    (hj : Function.Injective j) (A : Module.End ℂ M) (hA : ∀ f, ∃ g, j g = A (j f)) :
    ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = A (j f) := by
  choose a ha using hA
  exact ⟨{ toFun := a
           map_add' := fun f g => hj (by simp only [map_add (f := _), ha])
           map_smul' := fun c f => hj (by simp only [map_smul, ha, RingHom.id_apply]) }, ha⟩

theorem isCCR_restrict {Θ M κ : Type} [DecidableEq κ] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M]
    (j : Θ →ₗ[ℂ] M) (hj : Function.Injective j) {x d : κ → Module.End ℂ Θ} {x₀ d₀ : κ → Module.End ℂ M}
    (hx : ∀ k f, j (x k f) = x₀ k (j f)) (hd : ∀ k f, j (d k f) = d₀ k (j f)) (h : GlobalTheory.Mem.Lift.IsCCR x₀ d₀) :
    GlobalTheory.Mem.Lift.IsCCR x d := by
  refine ⟨fun k l => LinearMap.ext fun f => hj ?_, fun k l => LinearMap.ext fun f => hj ?_,
    fun k l => LinearMap.ext fun f => hj ?_⟩
  · simpa only [Module.End.mul_apply, hx] using LinearMap.congr_fun (h.1 k l) (j f)
  · simpa only [Module.End.mul_apply, hd] using LinearMap.congr_fun (h.2.1 k l) (j f)
  · have := LinearMap.congr_fun (h.2.2 k l) (j f)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hx, hd] at this ⊢
    rw [this]
    split_ifs <;> simp


open Matrix GlobalTheory.RealWeil in
theorem exists_ops {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B)
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) {Θ : Type} [AddCommGroup Θ] [Module ℂ Θ] (J : Θ →ₗ[ℂ] B)
    (hJ : Function.Injective J) (hs : ∀ f, Sm ρ (J f)) (hk : ∀ v f, ∃ g, J g = dH ρ v (J f)) :
    ∃ x d : ι → Module.End ℂ Θ, IsCCR x d ∧
      ∀ (X : Matrix ι ι ℂ) (f : Θ), J ((∑ k, ∑ l, X k l • (x k * d l)) f) = nOp ρ H X (J f) := by
  obtain ⟨x₀, d₀, hx₀, hd₀, hc⟩ := exists_isCCR_xOp_dOp ι H hH hd B ρ hρ
  let j : Θ →ₗ[ℂ] smS ρ := J.codRestrict _ hs
  have hj : Function.Injective j := fun f g e => hJ (congrArg Subtype.val e)
  have h1 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = x₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • Pi.single k 1) f
    refine ⟨g₁ - Complex.I • g₂, Subtype.ext ?_⟩
    rw [hx₀]
    change J _ = xOp ρ k (J f)
    rw [xOp, map_sub, map_smul, e₁, e₂]
  have h2 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = d₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (H⁻¹ *ᵥ Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • H⁻¹ *ᵥ Pi.single k 1) f
    refine ⟨(-(1 / (4 * Real.pi)) : ℂ) • (g₁ + Complex.I • g₂), Subtype.ext ?_⟩
    rw [hd₀]
    change J _ = dOp ρ H k (J f)
    rw [dOp, map_smul, map_add (f := _), map_smul, e₁, e₂]
  choose x hx using h1
  choose d hd' using h2
  refine ⟨x, d, isCCR_restrict j hj hx hd' hc, fun X f => ?_⟩
  have ex : ∀ k f, J (x k f) = xOp ρ k (J f) := fun k f => (congrArg Subtype.val (hx k f)).trans (hx₀ k _)
  have ed : ∀ k f, J (d k f) = dOp ρ H k (J f) := fun k f => (congrArg Subtype.val (hd' k f)).trans (hd₀ k _)

  simp only [nOp, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul, ex, ed]

end GlobalTheory.Mem.Lift.ThOps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


open GlobalTheory.RealWeil in
theorem GlobalTheory.Mem.Lift.exists_isCCR_theta : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  intro D θ σ h ψ hψ S T
  let J : thetaSub ψ S T →ₗ[ℂ] BB ψ S T :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO S T → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ S T (J f).1 := fun f => (hc f).symm ▸ f.2
  have hs : ∀ f, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) (J f) := fun f => sm_of_theta h hψ _ (ht f)
  have hk : ∀ v f, ∃ g, J g = dH (rhoV hψ σ S T) v (J f) := by
    intro v f
    obtain ⟨F', hF', hd⟩ := exists_deriv h hψ (J f) (ht f) v
    refine ⟨⟨F'.1, hF'⟩, QB_ext fun w => ?_⟩
    rw [hc]
    exact (hd w).unique (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (hs f)))
  obtain ⟨x, d, hxd, hn⟩ := ThOps.exists_ops (HM S T) HM_herm HM_det (rhoV hψ σ S T) (isHeis_rhoB h hψ) J hJ hs hk
  refine ⟨x, d, hxd, fun X f F hF => ?_⟩
  have e : F = J f := QB_ext fun w => by rw [hF, hc]
  rw [e, ← hn, hc]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_star : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsAutFunSm θ V (fun g => star (φ g)) := by
  first | exact @GlobalTheory.Mem.AutConj.isAutFunSm_star | exact GlobalTheory.Mem.AutConj.isAutFunSm_star | (intros; apply GlobalTheory.Mem.AutConj.isAutFunSm_star <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilOriented

theorem exists_extend {G M M' : Type} [Monoid G] [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (p : Submodule ℂ M) (E : M ≃ₗ[ℂ] M') (om : G →* Module.End ℂ p) :
    ∃ om' : G →* Module.End ℂ M', ∀ (g : G) (Φ : p), om' g (E Φ.1) = E (om g Φ).1 := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  let T : (p × q) ≃ₗ[ℂ] M' := (Submodule.prodEquivOfIsCompl p q hq).trans E
  have hT : ∀ Φ : p, T (Φ, 0) = E Φ.1 := fun Φ => by simp [T]
  refine ⟨{ toFun := fun g => T.toLinearMap ∘ₗ (LinearMap.prodMap (om g) LinearMap.id) ∘ₗ T.symm.toLinearMap
            map_one' := ?_
            map_mul' := fun a b => ?_ }, fun g Φ => ?_⟩
  · ext x
    simp
  · ext x
    simp
  · simp [← hT]

theorem lintegral_eq_of_integral_eq {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    {f f' : G → ℂ} (hf : Continuous f) (hf' : Continuous f') (hp : ∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖)
    (hp' : ∀ γ ∈ Γ, ∀ w, ‖f' (γ + w)‖ = ‖f' w‖) {μ : Measure G} {𝓕 : Set G} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖f' w‖ ^ 2 ∂μ) :
    ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f' w‖ₑ ^ 2 ∂μ := by
  have key := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov).2
  obtain ⟨N, hN⟩ := key f hf hp
  obtain ⟨N', hN'⟩ := key f' hf' hp'
  obtain ⟨h0, h1, h2, h3⟩ := hN μ 𝓕 hμ h𝓕
  obtain ⟨-, -, h2', h3'⟩ := hN' μ 𝓕 hμ h𝓕
  rw [h3, h3'] at h
  have : N = N' := NNReal.coe_injective (mul_left_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h)
  rw [h2, h2', this]

theorem norm_periodic {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) : ∀ γ ∈ ratL W V, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (hf.quasi γ w)
  rw [norm_mul, hψ.1.2.1, one_mul] at this
  exact this

theorem exists_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), admitted V W χ χ' → V.rank < W.rank → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  intro D ψ hψ V W χ χ' om ha hr hw
  obtain ⟨e, hc, hcs, he, hrat, hsm, hheis, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  let E : (WA V W → ℂ) ≃ₗ[ℂ] (WO V W → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.toEquiv
  obtain ⟨omO, hom⟩ := exists_extend (ThS ψ V W) E om
  have hom' : ∀ p (Φ : ThS ψ V W), omO p (fun x => Φ.1 (e x)) = fun x => (om p Φ).1 (e x) := hom
  have hsurj : ∀ f, IsThetaFunO ψ V W f → ∃ Φ : ThS ψ V W, f = fun x => Φ.1 (e x) := fun f hf => by
    have e1 : f = fun x => (fun y => f (e.symm y)) (e x) := by funext x; simp
    refine ⟨⟨fun y => f (e.symm y), mem_ThS.2 ((hth ψ _).1 ?_)⟩, e1⟩
    rw [← e1]; exact hf
  have hTh : ∀ Φ : ThS ψ V W, IsThetaFunO ψ V W fun x => Φ.1 (e x) := fun Φ => (hth ψ _).2 (mem_ThS.1 Φ.2)
  have hact : ∀ g h x, e (actO V W g h x) = actHom V W g h (e x) := fun g h x => by
    rw [he, he]; exact (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x
  refine ⟨omO, ⟨hψ, ha.2.1.1, ha.2.2.1.1, ha.2.2.2.1, ha.2.2.2.2, fun p f hf => ?_, fun g h w₀ f hf => ?_,
    fun γ hγ γ' hγ' f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_,
    fun ε hε g h hg hh x y hx hy => ?_⟩, fun p Φ => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']; exact hTh _
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    let Φ' : ThS ψ V W := ⟨Heisenberg₂ ψ V W (e w₀) Φ.1,
      mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis hψ (mem_ThS.1 Φ.2) _)⟩
    rw [hheis, hom', hheis, hact, ← hw.Heisenberg₂ g h (e w₀) Φ Φ' rfl]
    exact hom' _ Φ'
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    simp only [map_zero]
    exact hw.aut γ hγ γ' hγ' Φ
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    simp only [hom']
    exact hw.cont Φ (e w)
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨j1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D V W
    have : BorelSpace (WA V W) := ⟨rfl⟩
    have : BorelSpace (WO V W) := ⟨rfl⟩
    obtain ⟨ν, hν, hF, hint⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WO V W) e.symm hcs
      (by simpa using hc) (ratL V W) (ratL W V) (fun x => by rw [← hrat, e.apply_symm_apply]) μ 𝓕 hμ h𝓕
    refine lintegral_eq_of_integral_eq (ratL W V) hK hcov (hTh _).cont (hTh _).cont (norm_periodic hψ (hTh _))
      (norm_periodic hψ (hTh _)) hμ h𝓕 ?_
    rw [← hint, ← hint]
    simp only [e.apply_symm_apply]
    exact hw.unit ν _ hν hF p Φ
  · obtain ⟨r, hr0, hℓ⟩ := hw.split ε hε g h hg hh x y hx hy
    refine ⟨r, hr0, fun ℓ hinv f hf => ?_⟩
    obtain ⟨Φ, rfl⟩ := hsurj f hf
    have := hℓ (ℓ ∘ₗ E.toLinearMap ∘ₗ (ThS ψ V W).subtype) (fun u hu Ψ Ψ' hΨ => ?_) Φ
    · rw [hom']
      unfold splitFac at this
      rw [if_pos hr.le] at this
      exact this
    · have hu' : cA D ε • e.symm u = e.symm u := by
        apply e.injective
        rw [hsm, e.apply_symm_apply]
        exact Matrix.ext hu
      have := hinv (e.symm u) (fun i j => congrFun (congrFun hu' i) j) _ (hTh Ψ)
      rw [hheis, e.apply_symm_apply, ← hΨ] at this
      exact this
  · simp only [← he]
    exact hom' p Φ

end GlobalTheory.Mem.WeilOriented
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

noncomputable section

namespace GlobalTheory.Mem.Col2.CurveLat

theorem exists_periodPair_mul_image {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : 𝓞 K →+* ℂ) (hσ : Function.Injective σ) (a : 𝓞 K) (ha : (σ a).im ≠ 0) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ c : 𝓞 K, z = δ * σ c := by
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans hK)
  have hs : ∀ x : 𝓞 K, σ x = b.repr x 0 * σ (b 0) + b.repr x 1 * σ (b 1) := by
    intro x
    have := congrArg σ (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ (b 0) ≠ 0 := (map_ne_zero_iff σ hσ).2 (b.ne_zero 0)
  have h0 : (σ (b 1) * starRingEnd ℂ (σ (b 0))).im ≠ 0 := by
    intro h0
    have e := hs (a * b 0)
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ (b 0))).im) e
    simp only [map_mul] at e'
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨δ * σ (b 0), δ * σ (b 1), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e0
    have e : (x : ℂ) * σ (b 0) + (y : ℂ) * σ (b 1) = 0 := by
      apply mul_left_cancel₀ hδ
      simp only [Complex.real_smul] at e0
      linear_combination e0
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 1)).im * e1 - (σ (b 1)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 0)).re * e2 - (σ (b 0)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m • b 0 + n • b 1, by simp; ring⟩
    · rintro ⟨x, rfl⟩
      exact ⟨b.repr x 0, b.repr x 1, by rw [hs x]; ring⟩

theorem not_isIntegral_half : ¬ IsIntegral ℤ (1 / 2 : ℂ) := by
  intro h
  have h1 : IsIntegral ℤ (1 / 2 : ℚ) := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 ?_
    simpa using h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have h2 : (2 * y : ℚ) = 1 := by
    simp only [eq_intCast] at hy
    rw [hy]; norm_num
  have h3 : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem not_isIntegral_of_re {z : ℂ} (hz : z.re = 1 / 4) : ¬ IsIntegral ℤ z := by
  intro h
  have h1 : IsIntegral ℤ (starRingEnd ℂ z) := h.map (starRingEnd ℂ).toIntAlgHom
  have h2 := h.add h1
  rw [Complex.add_conj, hz] at h2
  apply not_isIntegral_half
  have e : ((2 * (1 / 4) : ℝ) : ℂ) = 1 / 2 := by
    push_cast
    norm_num
  rwa [e] at h2

variable {R : Ranks} (H : Host R)

def embO : 𝓞 H.K →+* ℂ := (H.φ₀.comp H.K.val.toRingHom).comp (algebraMap (𝓞 H.K) H.K)

theorem mem_lamOf_top (δ z : ℂ) : z ∈ Th.lamOf H ⊤ δ ↔ ∃ c : 𝓞 H.K, z = δ * embO H c := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, -, rfl⟩ := hx
      exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add (f := _), mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, mul_neg]⟩
  · rintro ⟨c, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, rfl⟩

theorem exists_periodPair_lamOf (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Th.lamOf H ⊤ δ ↔ z ∈ L.lattice := by
  have hK : Module.finrank ℚ H.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq
  have hinj : Function.Injective (embO H) :=
    (H.φ₀.comp H.K.val.toRingHom).injective.comp RingOfIntegers.coe_injective
  have ha : (embO H ⟨_, HostK.isIntegral_half H⟩).im ≠ 0 := by
    have e : embO H ⟨_, HostK.isIntegral_half H⟩ = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
      rw [← HostK.φ₀_sqrt]
      change (H.φ₀.comp H.K.val.toRingHom) ((1 + (⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ : H.K)) / 2) = _
      rw [map_div₀, map_add (f := _), map_one, map_ofNat]
      rfl
    have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
    rw [e]
    simp [hd.ne']
  obtain ⟨L, hL⟩ := exists_periodPair_mul_image hK (embO H) hinj _ ha δ hδ
  exact ⟨L, fun z => by rw [mem_lamOf_top, hL]⟩

theorem not_mem_lamOf (δ : ℂ) (hδ : δ ≠ 0) {z : ℂ} (hz : z.re = 1 / 4) : δ * z ∉ Th.lamOf H ⊤ δ := by
  rw [mem_lamOf_top]
  rintro ⟨c, hc⟩
  apply not_isIntegral_of_re hz
  rw [mul_left_cancel₀ hδ hc]
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) c).map (embO H).toIntAlgHom

end GlobalTheory.Mem.Col2.CurveLat

namespace GlobalTheory.Mem.Col2

open CurveLat

theorem exists_curve_lattice : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  intro R H
  obtain ⟨L₁, h₁⟩ := exists_periodPair_lamOf H 1 one_ne_zero
  have hΔ := (GlobalTheory.LatticeInvariants.invariants_dictionary L₁ _ h₁).2.2.1
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Th.lamOf H ⊤ 1)) (n := 12) (by norm_num)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hδ]; norm_num)
  obtain ⟨L, hL⟩ := exists_periodPair_lamOf H δ hδ0
  refine ⟨δ, L, δ, hδ, AddSubgroup.ext fun z => (hL z).symm, ?_, ?_, ?_⟩
  · exact (mem_lamOf_top H δ _).2 ⟨1, by rw [map_one]; ring⟩
  · have := not_mem_lamOf H δ hδ0 (z := (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring
  · have := not_mem_lamOf H δ hδ0 (z := (1 - Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring

end GlobalTheory.Mem.Col2

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.exists_rowBasis_from_referenceTuple_quotient : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (E : Hs) (jE : E.T →ₗ[ℂ] (y.C F.lv2).Amb 0), Function.Injective jE → LinearMap.range jE = (y.C F.lv2).EEc b → ∃ n c Xo, RrT F y b jE n c Xo := by
  first | exact @GlobalTheory.Mem.R3.Rw.rrT_exists | exact GlobalTheory.Mem.R3.Rw.rrT_exists | (intros; apply GlobalTheory.Mem.R3.Rw.rrT_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.exists_complexification_of_definiteGroupForms' : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (m : Mat1 K G) (e : MonoidAlgebra K G), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (∀ y, IsIntegral ℤ (o y)) → m.Laws σ e → ∃ s : Sp1 O (σ.comp o) G, Nonempty (Tie1 σ m s) := by
  intro K O _ _ _ _ o σ G _ _ m e hσ ho hm
  first
  | exact SpOfMat.exists_complexification_of_definiteGroupForms K O o σ G m e hσ ho hm
  | exact SpOfMat.exists_complexification_of_definiteGroupForms K O o σ G m e hσ ho hm hm.lat
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.lowestKType_restriction_injective_on_multiplicity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), ∀ w ∈ (y.L F.lv2).MultW i, w ∘ₗ (y.L F.lv2).embK i = 0 → w = 0 := by
  first | exact @GlobalTheory.Mem.R3.Rw.LowRes.multW_lowRes_inj | exact GlobalTheory.Mem.R3.Rw.LowRes.multW_lowRes_inj | (intros; apply GlobalTheory.Mem.R3.Rw.LowRes.multW_lowRes_inj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.liftHilbertModel_injective_contains_goodForms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), Function.Injective (R.toRealDat.HW i (sg0 D A3.A)).e ∧ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) ≤ LinearMap.range (R.toRealDat.HW i (sg0 D A3.A)).e ∧ ∀ u v, (y.L F.lv2).ipWc i (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e u)) (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e v)) = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  first | exact @GlobalTheory.LiftHilbertModel.hilbert_model_lift | exact GlobalTheory.LiftHilbertModel.hilbert_model_lift | (intros; apply GlobalTheory.LiftHilbertModel.hilbert_model_lift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.exists_hilbertChain_of_level_over_tops : ∀ (D : D7) (C : ChainReal D) (b : Bool) (U : D.what₂.Tup → Prop) (Top : D.what₂.Tup → Hs) (jX : ∀ μ, (Top μ).T →ₗ[ℂ] C.AmbX), 2 ≤ D.R.m → PeterssonHilbertSpace.IsHermPos (C.EEc b) (C.ipE b) → (∀ μ, C.EEc b ≤ C.CC b μ 0 ∧ C.CCXP b μ ≤ C.CCX b μ ∧ PeterssonHilbertSpace.IsHermPos (C.CCX b μ) (C.ipXP b μ) ∧ ∀ j, j ≤ D.R.m - 1 → C.CCP b μ j ≤ C.CC b μ j ∧ PeterssonHilbertSpace.IsHermPos (C.CC b μ j) (C.ipP b μ j)) → (∀ μ, PeterssonHilbertSpace.IsHermPos (C.CC b μ 0) (C.ipE b)) → (∀ μ, U μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = C.CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipXP b μ (jX μ x) (jX μ x')) → ∃ (EE : Hs) (Mult : D.what₂.Tup → ℕ → Hs) (multZero : ∀ μ, (Mult μ 0).T ≃ₗᵢ[ℂ] EE.T) (multTop : ∀ μ, (Mult μ D.R.m).T ≃ₗᵢ[ℂ] (Top μ).T) (io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T) (jE : EE.T →ₗ[ℂ] C.Amb 0) (jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j), Function.Injective jE ∧ LinearMap.range jE = C.EEc b ∧ (∀ x x', ⟪x, x'⟫_ℂ = C.ipE b (jE x) (jE x')) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → Function.Injective (jM μ j) ∧ LinearMap.range (jM μ j) = C.CCP b μ j ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jM μ j x) (jM μ j x')) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ 1).T) (h : jM μ 1 v ∈ C.CC b μ 1), ⟪x, multZero μ (io μ 0 v)⟫_ℂ = C.ipE b (jE x) (C.ioC b μ 0 ⟨jM μ 1 v, h⟩ : C.Amb 0)) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j + 1 ≤ D.R.m - 1 → ∀ x (v : (Mult μ (j + 1)).T) (h : jM μ (j + 1) v ∈ C.CC b μ (j + 1)), ⟪x, io μ j v⟫_ℂ = C.ipP b μ j (jM μ j x) (C.ioC b μ j ⟨jM μ (j + 1) v, h⟩ : C.Amb j)) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ D.R.m).T) (v' : (Mult μ (D.R.m - 1 + 1)).T), HEq v' v → ∀ h : jX μ (multTop μ v) ∈ C.CCX b μ, ⟪x, io μ (D.R.m - 1) v'⟫_ℂ = C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x) (C.ioX b μ ⟨jX μ (multTop μ v), h⟩ : C.Amb (D.R.m - 1))) ∧ (∀ μ, ¬ U μ → ∀ j, io μ j = 0) := by
  first | exact @GlobalTheory.ChainHilb.exists_chainHilb | exact GlobalTheory.ChainHilb.exists_chainHilb | (intros; apply GlobalTheory.ChainHilb.exists_chainHilb <;> assumption)
end
