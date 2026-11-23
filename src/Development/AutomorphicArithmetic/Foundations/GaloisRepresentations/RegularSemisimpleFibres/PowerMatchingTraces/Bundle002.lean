module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.G

private theorem isOpen_ker_chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) :
    IsOpen {g : Gw n v | χ.loc v (Matrix.GeneralLinearGroup.det g) = 1} := by
  have h := (isOpen_ker_finIdele K (χ.1.comp (finId K)) (χ.2.1.comp (continuous_finId K))).preimage
    ((Matrix.GeneralLinearGroup.continuous_det (n := Fin n)).comp (CuspSub.continuous_locGL (a := n) v))
  convert h using 1
  ext g
  exact Iff.of_eq (congrArg (fun u => χ.1 u = 1) (finId_det_locGL v g).symm)

private theorem isLocallyConstant_chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) :
    IsLocallyConstant (chiAt n χ v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Gw n v => x⁻¹ * y := continuous_const.mul continuous_id
  have hm : (fun y : Gw n v => x⁻¹ * y) ⁻¹' {g : Gw n v | χ.loc v (Matrix.GeneralLinearGroup.det g) = 1} ∈ nhds x :=
    ((isOpen_ker_chiAt n χ v).preimage hc).mem_nhds (by simp)
  filter_upwards [hm] with y hy
  have hy' : χ.loc v (Matrix.GeneralLinearGroup.det (x⁻¹ * y)) = 1 := hy
  rw [map_mul, map_mul, map_inv, map_inv] at hy'
  have e : χ.loc v (Matrix.GeneralLinearGroup.det y) = χ.loc v (Matrix.GeneralLinearGroup.det x) :=
    (inv_mul_eq_one.1 hy').symm
  simp only [chiAt, e]

theorem chiBasic : ChiBasic := by
  intro K _ _ n χ v
  refine ⟨isLocallyConstant_chiAt n χ v, fun g => ?_, fun f hf => ?_⟩
  · simp [chiAt, HChar.loc, ← Units.val_mul]
  · exact ⟨hf.1.mul (isLocallyConstant_chiAt n χ v), hf.2.mul_right⟩

end UpperTheory.Gal.InertialTypesAlt.G
end
end

section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

namespace UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces

private theorem finTrace_zero {V : Type} [AddCommGroup V] [Module ℂ V] :
    HasFinTrace (0 : V →ₗ[ℂ] V) 0 := by
  have key : ∀ (R : Submodule ℂ V) (h : ∀ v ∈ R, (0 : V →ₗ[ℂ] V) v ∈ R),
      LinearMap.trace ℂ R ((0 : V →ₗ[ℂ] V).restrict h) = 0 := by
    intro R h
    have e : (0 : V →ₗ[ℂ] V).restrict h = 0 := rfl
    rw [e, map_zero]
  exact ⟨by rw [LinearMap.range_zero]; infer_instance, key _ _⟩

private theorem finTrace_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c : ℂ} (b : ℂ)
    (h : HasFinTrace A c) : HasFinTrace (b • A) (b * c) := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, zero_mul]
    exact finTrace_zero
  obtain ⟨hf, rfl⟩ := h
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    intro R hR h1 h2
    subst hR
    have e : (b • A).restrict h1 = b • A.restrict h2 := rfl
    rw [e, map_smul, smul_eq_mul]
  have hr : LinearMap.range (b • A) = LinearMap.range A := LinearMap.range_smul _ _ hb
  exact ⟨by rw [hr]; exact hf, key _ hr _ _⟩

private theorem isInt_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {A : V →ₗ[ℂ] V} (d : ENNReal) (hdt : d ≠ ⊤)
    (hA : IsIntegralOp m ρ f A) : IsIntegralOp (d • m) ρ f ((d.toReal : ℂ) • A) := fun v l =>
  ⟨(hA v l).1.smul_measure hdt, by
    rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]⟩

private theorem finite_comp {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) (I : V ≃ₗ[ℂ] V)
    (h : FiniteDimensional ℂ (LinearMap.range A)) :
    FiniteDimensional ℂ (LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V))) := by
  have e : LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V)) = LinearMap.range A :=
    LinearMap.range_comp_of_range_eq_top A (LinearEquiv.range I)
  rw [e]
  exact h

end UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces

open UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces in
theorem UpperTheory.Gal.InertialTypesAlt.G.trBasic :
    UpperTheory.Gal.InertialTypesAlt.G.TrBasic := by
  intro G _ _ _ m τ I f
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨A, hA, hF⟩
    exact ⟨_, A, hA, finite_comp A I hF.1, rfl⟩
  · rintro t t' ⟨A, hA, -, rfl⟩ ⟨B, hB, -, rfl⟩
    obtain rfl := hA.unique hB
    rfl
  · intro d hd
    refine ⟨?_, ?_⟩
    · rintro z ⟨A, hA, hF⟩
      exact ⟨_, isInt_smul d hd hA, finTrace_smul A _ hF⟩
    · rintro t ⟨B, hB, hF⟩
      refine ⟨_, isInt_smul d hd hB, ?_⟩
      have e : ((d.toReal : ℂ) • B) ∘ₗ (I : τ.V →ₗ[ℂ] τ.V) = (d.toReal : ℂ) • (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) := rfl
      rw [e]
      exact finTrace_smul _ _ hF
end

section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

open GroundTheory.Global.IdeleGroup PositivityTheory.RgJS

namespace UpperTheory.Gal.InertialTypesAlt.G.WP

variable {K : Type} [Field K] [NumberField K]

private theorem module_local (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule K (Neutral.B1.localIdele K v x)).1 : ℝ) = ‖(x : v.adicCompletion K)‖ := by
  have : Neutral.B1.localIdele K v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x := by
    apply Units.ext
    rfl
  rw [this]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_of_val (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℤ)
    (h : Valued.v x = WithZero.exp n) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp [WithZero.log_exp]

private theorem pow_loc {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← module_local]
  exact h _

private theorem pow_unr {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v := fun x hx => by
  apply Units.ext
  rw [pow_loc h, norm_of_val v _ 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]
  simp

private theorem pow_val {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) :
    ((χ.val v : ℂˣ) : ℂ) = ((Formalism.ConjugateSelfDual.normV v : ℕ) : ℂ) ^ (-s) := by
  have e : χ.val v = χ.loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) := rfl
  have e2 : (Formalism.ConjugateSelfDual.normV v : ℕ) = Ideal.absNorm v.asIdeal := by
    rw [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, pow_loc h, norm_of_val v _ (-1) (Formalism.L2.Host.unif_spec v), e2, zpow_neg_one, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_pos.ne), Complex.cpow_neg]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem val_pow {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (w : HeightOneSpectrum (𝓞 E)) (f : ℕ) (hf : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f) :
    χ'.val w = χ.val (w.under (𝓞 F)) ^ f := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_val h, pow_val h', hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
    Complex.natCast_cpow_natCast_mul]

private theorem weak_twist {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (π : CuspSub F n) (P : CuspSub E n) (H : WeakBC (Cusp.cx π).sat (Cusp.cx P).sat) :
    WeakBC (Cusp.cx (π.twist χ)).sat (Cusp.cx (P.twist χ')).sat := by
  refine Filter.Eventually.mono H fun w hw f hf => ?_
  obtain ⟨B, hB, hB'⟩ := hw f hf
  refine ⟨B.map (· * χ.val (w.under (𝓞 F))), ?_, ?_⟩
  · have := satake_twist_holds F n (CG.mk π) χ _ B (pow_unr h _) hB
    rwa [CG.twist_mk] at this
  · have := satake_twist_holds E n (CG.mk P) χ' w _ (pow_unr h' _) hB'
    rw [CG.twist_mk] at this
    change (CG.mk (P.twist χ')).HasSat w _
    convert this using 1
    simp [Multiset.map_map, val_pow h h' w f hf, mul_pow]

end UpperTheory.Gal.InertialTypesAlt.G.WP

open UpperTheory.Gal.InertialTypesAlt.G.WP in
theorem UpperTheory.Gal.InertialTypesAlt.G.weakPow :
    UpperTheory.Gal.InertialTypesAlt.G.WeakPow := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n _ z χ χ' h h' π P H
  exact weak_twist h h' π P H
end
