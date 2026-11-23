module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle483
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle485
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle486
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.LiftGen

open GlobalTheory.RealWeil

theorem deriv_eq_of_norm {B H : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Φ : B →L[ℂ] H) {u v : ℝ → B} {A G A' : B} (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0)
    (hn : ∀ t : ℝ, ‖Φ (v t - v 0 - (t : ℂ) • A')‖ = ‖Φ (u t - u 0 - (t : ℂ) • A)‖) : Φ G = Φ A' := by
  have h1 : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  have h2 : HasDerivAt (fun t => Φ (v t)) (Φ G) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  refine h2.unique ?_
  rw [hasDerivAt_iff_isLittleO] at h1 ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
  refine h1.congr_left fun t => ?_
  have := hn t
  rw [map_sub, map_sub, map_sub, map_sub, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul] at this
  simp only [sub_zero]
  exact this.symm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem deriv_om (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (p : GA D S × GA D T) {u v : ℝ → BB ψ S T} {A G : BB ψ S T}
    (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0) (hut : ∀ t, IsThetaFunO ψ S T (u t).1)
    (hA : IsThetaFunO ψ S T A.1) (e : ∀ t, ((v t).1 : WO S T → ℂ) = om p (u t).1) :
    (G.1 : WO S T → ℂ) = om p A.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  let A' : BB ψ S T := toB hψ _ (hW.om_pres p _ hA)
  have hA' : (A'.1 : WO S T → ℂ) = om p A.1 := coe_toB _ _ _
  have hk : ∀ a b : BB ψ S T, IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have key : toL2 _ _ (μ.restrict 𝓕) G = toL2 _ _ (μ.restrict 𝓕) A' := by
    refine deriv_eq_of_norm _ hu hv fun t => ?_
    have e1 : ((u t - u 0 - (t : ℂ) • A).1 : WO S T → ℂ) =
        ((u t).1 : WO S T → ℂ) - ((u 0).1 : WO S T → ℂ) - (t : ℂ) • (A.1 : WO S T → ℂ) := rfl
    have e2 : ((v t - v 0 - (t : ℂ) • A').1 : WO S T → ℂ) = om p (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1, map_sub, map_sub, map_smul, ← e, ← e, ← hA']
      rfl
    have h3 : IsThetaFunO ψ S T (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (hut t) (hut 0)) ((thetaSub ψ S T).smul_mem _ hA)
    exact hk _ _ h3 e2
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (G - A')
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((G - A').1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (G - A').1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  rw [← hA']
  exact sub_eq_zero.1 h5

theorem hasDerivAt_om : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∀ p w, HasDerivAt (fun t => om (p * γ t) F.1 w) (om p (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F).1 w) 0 := by
  intro D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨x, d, -, hxd⟩ := GlobalTheory.T.exists_ccr_operators_thetaFunctions D θ σ h ψ hψ S T
  refine ⟨lam, fun F hF p w => ?_⟩
  obtain ⟨u, hu, hud⟩ := hlam F hF
  have hA : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F).1 := by
    have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
    rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
    exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem lam hF)
  have : IsTopologicalGroup (GA D S) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S).2.2.2.2.1
  have : IsTopologicalGroup (GA D T) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T).2.2.2.2.1
  have hn : ∀ V : HSp D, (GinfC V).Normal := fun V => MonoidHom.normal_ker _
  obtain ⟨lam', hlam'⟩ := GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm D θ σ h ψ hψ S T om hW hc (fun t => p * γ t * p⁻¹)
    ((continuous_const.mul hγ).mul continuous_const) (fun s t => by rw [hadd]; group)
    (fun t => ⟨(hn S).conj_mem _ (hinf t).1 p.1, (hn T).conj_mem _ (hinf t).2 p.2⟩)
    (mM θ S T p * X * mM θ S T p⁻¹) (fun k l => by
      simp only [map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (HasDerivAt.fun_sum fun i _ => (hX i j).const_mul _).mul_const _)
  obtain ⟨v, hv, hvd⟩ := hlam' (toB hψ _ (hW.om_pres p _ hF)) (by rw [coe_toB]; exact hW.om_pres p _ hF)
  have e : ∀ t, ((v t).1 : WO S T → ℂ) = om (p * γ t) F.1 := fun t => by
    rw [hv, coe_toB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  have key := deriv_om hψ hW p hud hvd (fun t => by rw [hu]; exact hW.om_pres _ _ hF) hA
    (fun t => by rw [e, hu, map_mul, Module.End.mul_apply])
  rw [← key]
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hvd
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact (congrFun (e t) w).symm

end GlobalTheory.Mem.LiftGen
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

theorem _root_.GlobalTheory.T.twistedEmbeddingMatrixSubstitution_mem_ratSpan : ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ),
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → twSub (embT D) M s P0 ∈ Formalism.L2.Forms.RatSpan D lam := by
  first | exact @GlobalTheory.IntegralityCompare.twSub_mem_ratSpan | exact GlobalTheory.IntegralityCompare.twSub_mem_ratSpan | (intros; apply GlobalTheory.IntegralityCompare.twSub_mem_ratSpan <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftCusp

theorem exists_bound {Z H : Type} [Group Z] [TopologicalSpace Z] [MeasurableSpace Z] [Group H] [TopologicalSpace H]
    (Γ : Subgroup Z) (Δ : Subgroup H) (μ : Measure Z) [μ.IsOpenPosMeasure] (𝓕 : Set Z)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hc : IsCompact (closure 𝓕)) (C : Set H) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Δ, ∃ c ∈ C, h = γ * c) (K : Z × H → ℂ) (hK : Continuous K)
    (hinv : ∀ γ ∈ Γ, ∀ δ ∈ Δ, ∀ z h, K (γ * z, δ * h) = K (z, h)) : ∃ B : ℝ, ∀ p, ‖K p‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hc.prod hC).exists_bound_of_continuousOn hK.continuousOn
  refine ⟨B, fun ⟨z, h⟩ => ?_⟩
  obtain ⟨δ, hδ, c, hcC, rfl⟩ := hcov h
  have hae : ∀ᵐ z ∂μ, ‖K (z, δ * c)‖ ≤ B := by
    filter_upwards [h𝓕.ae_covers] with z hz
    obtain ⟨γ, hγ⟩ := hz
    have := hinv γ⁻¹ (inv_mem γ.2) δ hδ (γ * z) c
    rw [inv_mul_cancel_left] at this
    rw [this]
    exact hB _ ⟨subset_closure hγ, hcC⟩
  have hcl : IsClosed {z : Z | ‖K (z, δ * c)‖ ≤ B} :=
    isClosed_le (hK.comp (Continuous.prodMk_left _)).norm continuous_const
  exact hcl.closure_subset (μ.dense_of_ae hae z)

theorem swap_of_bound {Z H : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Z) (ν : Measure H) (A : Set Z) (B : Set H) (hA : μ A ≠ ⊤) (hB : ν B ≠ ⊤)
    (K : Z × H → ℂ) (hK : Continuous K) (c : ℝ) (hc : ∀ p, ‖K p‖ ≤ c) :
    ∫ z in A, ∫ h in B, K (z, h) ∂ν ∂μ = ∫ h in B, ∫ z in A, K (z, h) ∂μ ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hA.lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hB.lt_top⟩
  exact integral_integral_swap (f := fun z h => K (z, h))
    (Integrable.of_bound hK.aestronglyMeasurable c (Filter.Eventually.of_forall hc))

theorem continuous_family {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H : IsWeilDatumO ψ S T χS χT om)
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ))
    (hL : ∀ x, IsThetaFunO ψ S T (L x)) :
    Continuous fun q : (GA D S × GA D T) × X => om q.1 (L q.2) 0 := by
  let b := Module.finBasis ℂ X
  have e : (fun q : (GA D S × GA D T) × X => om q.1 (L q.2) 0) =
      fun q => ∑ i, b.coord i q.2 * om q.1 (L (b i)) 0 := by
    funext q

    conv_lhs => rw [← b.sum_repr q.2, map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul]
    rfl
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp continuous_snd).mul
      ((H.om_cont _ (hL _) 0).comp continuous_fst)

theorem zcusp_lift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (∀ x h g ξ, IsoVec T ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin S.rank → AE D, ∑ k, heisO ψ S T (along S T ξ (a k)) (om (h, g) (L x)) = 0) → ZCusp T (lift om ν 𝓕 fun h => L (F h)) := by
  intro D ψ S T χS χT om H hpos X _ _ _ L hL F hF hFinv ν 𝓕 hν h𝓕 hav ξ hξ μ 𝓖 hμ h𝓖 g
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig S.gram
  have i1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig T.gram
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable S
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable T
  have : BorelSpace (ZI T ξ) := Subtype.borelSpace _
  have : SecondCountableTopology (ZI T ξ) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨⟨μ₀, 𝓖₀, hμ₀, h𝓖₀, hc₀⟩, hfin, -⟩ := GlobalTheory.TransvMeasure.transvection_measure D θ T hθ ξ hξ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  have hG : μ 𝓖 ≠ ⊤ := (hfin μ 𝓖 hμ h𝓖).2
  have hN : ν 𝓕 ≠ ⊤ := GlobalTheory.TransvMeasure.measure_ne_top_of_cocompact (GQ S) hC (fun x => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩) ν h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ]; exact hG.lt_top⟩

  have hint : ∀ f, IsThetaFunO ψ S T f →
      Integrable (fun z : ZI T ξ => om (1, (z : GA D T)) f 0) (μ.restrict 𝓖) := by
    intro f hf
    obtain ⟨hc, hi⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om H f hf
    have hK : Continuous fun p : ZI T ξ × GA D S => thetaKO om p.2 (p.1 : GA D T) f :=
      hc.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
    obtain ⟨B, hB⟩ := exists_bound _ (GQ S) μ₀ 𝓖₀ h𝓖₀ hc₀ C hC hcov _ hK
      fun γ hγ δ hδ z h => hi δ hδ γ hγ h z
    exact Integrable.of_bound (hK.comp (Continuous.prodMk_left 1)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => hB (z, 1))

  have hin : ∀ h x, ∫ z in 𝓖, thetaKO om h ((z : GA D T) * g) (L x) ∂μ = 0 := by
    intro h x
    have hf : IsThetaFunO ψ S T (om (h, g) (L x)) := H.om_pres _ _ (hL x)
    have e : ∀ z : ZI T ξ, thetaKO om h ((z : GA D T) * g) (L x) = om (1, (z : GA D T)) (om (h, g) (L x)) 0 := by
      intro z
      have h1 : om (h, (z : GA D T) * g) = om (1, (z : GA D T)) * om (h, g) := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      unfold thetaKO
      rw [h1]
      rfl
    simp only [e]
    obtain ⟨n, hn, a, ha⟩ := hav x h g ξ hξ
    have h1 := integral_finsetSum (μ := μ.restrict 𝓖) Finset.univ
      (fun (k : Fin n) _ => hint _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all H.std hf (along S T ξ (a k))))
    have h2 : ∀ z : ZI T ξ,
        ∑ k, om (1, (z : GA D T)) (heisO ψ S T (along S T ξ (a k)) (om (h, g) (L x))) 0 = 0 := by
      intro z

      rw [← Finset.sum_apply, ← map_sum, ha, map_zero]
      rfl
    simp only [h2, GlobalTheory.T.integral_om_heisO_along_eq_integral_om D ψ S T χS χT om H hpos ξ hξ μ 𝓖 hμ h𝓖 _ hf, integral_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hn.ne')
  have hK : Continuous fun p : ZI T ξ × GA D S => thetaKO om p.2 ((p.1 : GA D T) * g) (L (F p.2)) :=
    (continuous_family H L hL).comp
      ((continuous_snd.prodMk ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).prodMk
        (hF.comp continuous_snd))
  obtain ⟨B, hB⟩ := exists_bound _ (GQ S) μ₀ 𝓖₀ h𝓖₀ hc₀ C hC hcov _ hK fun γ hγ δ hδ z h => by
    have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om H _ (hL (F h))).2 δ hδ γ hγ h (z * g)
    rw [← this, ← mul_assoc]
    simp only [hFinv δ hδ]
    rfl
  have key := swap_of_bound μ ν 𝓖 𝓕 hG hN _ hK B hB
  simp only [hin, integral_zero] at key
  exact key

end GlobalTheory.DefLiftCusp
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_den_idem {Q w : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε) (hw : w ≠ Q)
    (a : E ⊗[F] Formalism.L2.Herm.Af F) :
    ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ ∃ hm : iA F E (algebraMap (𝓞 E) E t) * (ε * a) ∈ Formalism.L2.Herm.intAf F E,
      resS F w ⟨_, hm⟩ = 0 := by
  obtain ⟨N, hN, hNa⟩ := GlobalTheory.PlaceDatum.exists_den_adele (F := F) (E := E) a
  have hN0 : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have hv0 : Q.intValuation (N : 𝓞 E) ≠ 0 := Q.intValuation_ne_zero _ hN0
  set k : ℕ := (-(WithZero.log (Q.intValuation (N : 𝓞 E)))).toNat with hk
  have hvk : Q.intValuation (N : 𝓞 E) = WithZero.exp (-(k : ℤ)) := by
    have h1 := Q.intValuation_le_one (N : 𝓞 E)
    rw [← WithZero.exp_log hv0] at h1 ⊢
    have h2 : WithZero.log (Q.intValuation (N : 𝓞 E)) ≤ 0 := by
      rw [← WithZero.exp_le_exp]; simpa using h1
    congr 1
    rw [hk]; omega
  obtain ⟨t, htk, htw⟩ : ∃ t ∈ Q.asIdeal ^ k, t ∉ w.asIdeal := by
    by_contra hn
    push Not at hn
    have hle : Q.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hn
    exact hw (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm
  have hNE : ((N : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hval : Q.valuation E ((t : E) * ((N : 𝓞 E) : E)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, show (t : E) = algebraMap (𝓞 E) E t from rfl,
      show ((N : 𝓞 E) : E) = algebraMap (𝓞 E) E (N : 𝓞 E) from rfl,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hvk,
      mul_inv_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), one_mul]
    exact (Q.intValuation_le_pow_iff_mem t k).2 htk
  have hNc : ((N : ℕ) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E ((N : 𝓞 E) : E) := by simp
  have hinv : iA F E ((N : 𝓞 E) : E) * iA F E (((N : 𝓞 E) : E))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hNE, map_one]
  have e : iA F E (algebraMap (𝓞 E) E t) * (ε * a) =
      ε * iA F E ((t : E) * ((N : 𝓞 E) : E)⁻¹) * ((N : E ⊗[F] Formalism.L2.Herm.Af F) * a) := by
    rw [hNc, map_mul, show algebraMap (𝓞 E) E t = (t : E) from rfl]
    linear_combination (-(iA F E (t : E) * ε * a)) * hinv
  have hm : iA F E (algebraMap (𝓞 E) E t) * (ε * a) ∈ Formalism.L2.Herm.intAf F E := by
    rw [e]; exact mul_mem (h.mul_mem_of_val hval) hNa
  have hm2 : ε * (iA F E (algebraMap (𝓞 E) E t) * a) ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_left_comm]; exact hm
  refine ⟨t, htw, hm, ?_⟩
  have e2 : (⟨_, hm⟩ : Formalism.L2.Herm.intAf F E) = ⟨_, hm2⟩ := Subtype.ext (mul_left_comm _ _ _)
  rw [e2]
  exact h.resS_eq_zero hw hm2

section Lat

variable [StarRing E] {n : ℕ} [NeZero n]

theorem pullV_mul_idem {ε : E ⊗[F] Formalism.L2.Herm.Af F} (x g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hg : ε • ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) = (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)
    (v : Fin n → E) (i : Fin n) :
    pullV (x * g⁻¹) v i = pullV x v i +
      ε * ((((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ pullV x v) i) := by
  rw [pullV_mul_inv]
  conv_lhs => rw [← sub_add_cancel (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) 1, ← hg]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, add_comm]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem mem_localization_globLat_mul_inv_of_ne {Q w : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε) (hw : w ≠ Q)
    (x g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hg : ε • ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) = (g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)
    (v : Fin n → E) (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) :
    v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat (x * g⁻¹) (stdLat E n)) ∧
      ∀ i, redA w (pullV (x * g⁻¹) v i) = redA w (pullV x v i) := by
  obtain ⟨s, hs, hsu⟩ := pullV_den hv
  set c := ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ pullV x v with hc
  choose t ht hm hz using fun i => exists_den_idem h hw (c i)
  have hT : (∏ i, t i) ∉ w.asIdeal := fun hT => by
    obtain ⟨i, _, hi⟩ := (w.isPrime.prod_mem_iff).1 hT
    exact ht i hi
  have hTc : ∀ i, iA F E (algebraMap (𝓞 E) E (∏ j, t j)) * (ε * c i) ∈ Formalism.L2.Herm.intAf F E := by
    intro i
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
    rw [hr, map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E (t i))), mul_assoc]
    exact mul_mem (iA_mem r) (hm i)
  refine ⟨(Formalism.L2.Col.mem_locP w _ v).2 ⟨s * ∏ j, t j, fun hh => (w.isPrime.mem_or_mem hh).elim hs hT,
    (mem_globLat _ _).2 fun i => ?_⟩, fun i => ?_⟩
  · rw [pullV_osmul, pullV_mul_idem x g hg, map_mul, map_mul, mul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm (iA F E (algebraMap (𝓞 E) E s)), mul_assoc]
      exact mul_mem (iA_mem _) (hsu i)
    · rw [mul_assoc]
      exact mul_mem (iA_mem _) (hTc i)
  · have h1 : iA F E (algebraMap (𝓞 E) E (s * t i)) * pullV x v i ∈ Formalism.L2.Herm.intAf F E := by
      rw [map_mul, map_mul, mul_comm (iA F E (algebraMap (𝓞 E) E s)), mul_assoc]
      exact mul_mem (iA_mem _) (hsu i)
    have h2 : iA F E (algebraMap (𝓞 E) E (s * t i)) * (ε * c i) ∈ Formalism.L2.Herm.intAf F E := by
      rw [map_mul, map_mul, mul_assoc]
      exact mul_mem (iA_mem _) (hm i)
    have hst : s * t i ∉ w.asIdeal := fun hh => (w.isPrime.mem_or_mem hh).elim hs (ht i)
    rw [pullV_mul_idem x g hg, redA_add w hst h1 h2]
    have h0 : redA w (ε * c i) = 0 := redA_eq w (ht i) (hm i) (by rw [mul_zero, hz i])
    rw [h0, add_zero]

end Lat

theorem decoRaw_mul_idem [StarRing E] {n : ℕ} [NeZero n] (ST SG : Finset (Pl E)) (Q : Pl E)
    (ε : E ⊗[F] Formalism.L2.Herm.Af F) (h : IdemOf F Q ε) (hQT : Q ∉ ST) (hQG : Q ∉ SG)
    (y b : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hb : ε • (b.1 - 1) = b.1 - 1) :
    (decoRaw ST SG (y * b)).f = (decoRaw ST SG y).f ∧ (decoRaw ST SG (y * b)).be = (decoRaw ST SG y).be := by
  have hb' : ε • (((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) =
      ((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 := by
    have e : ((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 =
        -(((b⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          ((b : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1)) := by
      rw [Matrix.mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      abel
    rw [e, smul_neg, ← Matrix.mul_smul]
    congr 2
  have hiff : ∀ w : Pl E, w ≠ Q → ∀ v : Fin n → E,
      v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat (y * b) (stdLat E n)) ↔
        v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) := by
    intro w hw v
    constructor
    · intro hv
      have := (mem_localization_globLat_mul_inv_of_ne h hw (y * b) b hb v hv).1
      rwa [mul_inv_cancel_right] at this
    · intro hv
      have := (mem_localization_globLat_mul_inv_of_ne h hw y b⁻¹ hb' v hv).1
      rwa [inv_inv] at this
  have hred : ∀ w : Pl E, w ≠ Q → ∀ v : Fin n → E,
      v ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) →
        ∀ i, redA w (pullV (y * b) v i) = redA w (pullV y v i) := by
    intro w hw v hv i
    have := (mem_localization_globLat_mul_inv_of_ne h hw y b⁻¹ hb' v hv).2 i
    rwa [inv_inv] at this
  refine ⟨funext fun P => funext fun v => ?_, funext fun w => funext fun v => ?_⟩
  · have hP : P.1 ≠ Q := fun e => hQT (e ▸ P.2)
    simp only [decoRaw]
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n))
    · rw [if_pos ((hiff P.1 hP v).2 hv), if_pos hv, hred P.1 hP v hv]
    · rw [if_neg (fun h' => hv ((hiff P.1 hP v).1 h')), if_neg hv]
  · have hP : w.1 ≠ Q := fun e => hQG (e ▸ w.2)
    simp only [decoRaw]
    by_cases hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n))
    · rw [if_pos ((hiff w.1 hP v).2 hv), if_pos hv]
      funext i
      exact hred w.1 hP v hv i
    · rw [if_neg (fun h' => hv ((hiff w.1 hP v).1 h')), if_neg hv]

end GlobalTheory.InertNbr
end
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  first | exact @GlobalTheory.FlagFibreInt.lintegral_dens_glue | exact GlobalTheory.FlagFibreInt.lintegral_dens_glue | (intros; apply GlobalTheory.FlagFibreInt.lintegral_dens_glue <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

theorem _root_.GlobalTheory.T.frameTransport_eta_isHeckeElement_lifts : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf (Vc X.toD7 i)) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    (envL X I hX U Xg tr L cV i t).isT x g := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.eta_isHecke | exact GlobalTheory.Mem.R3.LiftBrg.eta_isHecke | (intros; apply GlobalTheory.Mem.R3.LiftBrg.eta_isHecke <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2


theorem _root_.GlobalTheory.T.tame_heckeCharacter_split_place_local_component : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (χ : Formalism.L2.Host.HChar L), χ.TameAt s.w → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ) (a : 𝓞 L) (k : Lˣ), (k : L) = (a : L) → Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 → Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) < 1 → ξ u = χ.locK s.w k := by
  first | exact @GlobalTheory.HeckeSplitComp.main | exact GlobalTheory.HeckeSplitComp.main | (intros; apply GlobalTheory.HeckeSplitComp.main <;> assumption)
end
