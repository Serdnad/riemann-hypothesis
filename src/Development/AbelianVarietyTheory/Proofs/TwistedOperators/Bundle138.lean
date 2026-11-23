module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Formalism.LocalRingCardinality.DataHost
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
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.FinRealComm

private theorem eq_map_inl_fst_add_map_inr_snd_tmul {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E) :
    z = TensorProduct.map (LinearMap.inl F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
        TensorProduct.map (LinearMap.inr F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.map_tmul, ← TensorProduct.add_tmul]
    congr 1
    ext <;> simp
  | add u v hu hv =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    conv_lhs => rw [hu, hv]
    abel

theorem tensor_prod_ext {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (x y : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  rw [eq_map_inl_fst_add_map_inr_snd_tmul x, eq_map_inl_fst_add_map_inr_snd_tmul y, h1, h2]

theorem GA_ext_inf_fin {D : D7} (V : HSp D) (x y : GA D V)
    (h1 : infHom V x = infHom V y) (h2 : finHom V x = finHom V y) : x = y := by
  have hm : (matHom V x).1 = (matHom V y).1 := by
    ext i j
    have e1 := congrArg (fun g => g.1 i j) h1
    have e2 := congrArg (fun g => g.1 i j) h2
    simp only [infHom, finHom, MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map,
      MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e1 e2
    exact tensor_prod_ext _ _ e1 e2
  exact Subtype.ext (Units.ext hm)

theorem finite_real_points_commute :
    ∀ {D : D7} (V : HSp D) (a b : GA D V), a ∈ GfC V → b ∈ GinfC V → a * b = b * a := by
  intro D V a b ha hb
  have ha' : infHom V a = 1 := ha
  have hb' : finHom V b = 1 := hb
  apply GA_ext_inf_fin V
  · rw [map_mul, map_mul, ha', one_mul, mul_one]
  · rw [map_mul, map_mul, hb', one_mul, mul_one]

end GlobalTheory.FinRealComm
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct InnerProductSpace in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.thetaLift_translate_of_kernel_fixed : ∀ {G H S Sinf Ds Dt : Type} [Group G] [Group H]
    [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (It : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt),
    _root_.Formalism.IndefR.Lift.IsIo ν 𝓕 th pt It CCs CCt io →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (It φ v) = 0) → u = 0) →
    ∀ (k : G) (k' : H) (a a' : ℂ), (∀ g h φ, a * th (g * k) (h * k') (pt φ) = a' * th g h (pt φ)) →
    (∀ (F : CCs) φ v g, ∫ h in 𝓕, th g (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') ∂ν =
      ∫ h in 𝓕, th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h ∂ν) →
    ∀ (F F' : CCs) (u : CCt), (∀ v h, (F' : Ds →ₗ[ℂ] (H → ℂ)) v h = a' * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) →
    (∀ v g, (u : Dt →ₗ[ℂ] (G → ℂ)) v g = a * ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) v (g * k)) →
    io F' = u := by
  intro G H S Sinf Ds Dt _ _ _ _ _ _ _ _ _ ν 𝓕 th pt It CCs CCt io hio hker k k' a a' hth hinv
    F F' u hF' hu
  refine sub_eq_zero.mp (hker (io F' - u) fun φ v => ?_)
  funext g
  simp only [Submodule.coe_sub, LinearMap.sub_apply, Pi.sub_apply, Pi.zero_apply]
  rw [sub_eq_zero, ← hio.eq F' φ v g, hu, ← hio.eq F φ v (g * k)]
  unfold _root_.Formalism.IndefR.Lift.liftInt
  rw [← hinv F φ v (g * k), ← integral_const_mul]
  congr 1
  funext h
  rw [hF', show a * (th (g * k) (h * k') (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k')) =
    (a * th (g * k) (h * k') (pt φ)) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * k') from
    (_root_.mul_assoc _ _ _).symm, hth]
  ring

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem fundamentalDomain_setIntegral_mul_right :
    ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ k : G, Measure.map (fun g => g * k) μ = μ → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ → IntegrableOn (fun g => f (g * k)) 𝓕 μ ∧ ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  intro G _ _ _ _ Γ _ μ _ 𝓕 h𝓕 k hk f hf hi
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h𝓕.integrableOn_iff h2 hinv]
    exact (hmp.integrableOn_comp_preimage hemb).2 hi
  · rw [h𝓕.setIntegral_eq h2 hinv]
    exact hmp.setIntegral_preimage_emb hemb f 𝓕

end GlobalTheory
end
