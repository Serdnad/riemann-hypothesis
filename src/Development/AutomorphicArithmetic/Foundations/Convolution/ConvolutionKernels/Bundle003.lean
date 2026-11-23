module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdNormOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle001
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.CuspidalProjection.Global

@[expose] public section

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.twAdj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ) (φ : L2 μ),
      (ContinuousLinearMap.adjoint θ.U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (θ.e (Quotient.out y))) := by
  intro K _ _ n μ _ θ φ
  have hp' : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, θ.e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by rw [← θ.mem_gam, θ.e.apply_symm_apply]
  obtain ⟨h1, q1⟩ := qmapPres (Gam K n) μ θ.e θ.mem_gam θ.pres
  obtain ⟨h2, q2⟩ := qmapPres (Gam K n) μ θ.e.symm hg' hp'
  have key : ContinuousLinearMap.adjoint θ.U φ = Lp.compMeasurePreserving _ q1 φ := by
    refine ext_inner_right ℂ fun ψ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
    have a1 := q1.quasiMeasurePreserving.ae_eq_comp (θ.U_spec ψ)
    have m : AEStronglyMeasurable (fun y => ⟪(φ : RightCosetSpace (Gam K n) → ℂ) y, (θ.U ψ : RightCosetSpace (Gam K n) → ℂ) y⟫_ℂ)
        (Measure.map (fun y : RightCosetSpace (Gam K n) => mk (Gam K n) (θ.e (Quotient.out y))) (quotientMeasure (Gam K n) μ)) := by
      rw [q1.map_eq]
      exact (Lp.aestronglyMeasurable φ).inner (Lp.aestronglyMeasurable _)
    have e1 := integral_map q1.measurable.aemeasurable m
    rw [q1.map_eq] at e1
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [a1, Lp.coeFn_compMeasurePreserving φ q1] with y hy hz
    rw [hz]
    simp only [Function.comp_apply] at hy ⊢
    rw [hy, h2, θ.e.symm_apply_apply]
    congr 2
    exact Quotient.out_eq y
  rw [key]
  exact Lp.coeFn_compMeasurePreserving φ q1
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.twOpEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (e : G1 K n ≃ₜ* G1 K n), (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) → MeasurePreserving e μ μ →
      ∃ U : L2 μ →L[ℂ] L2 μ,
        (∀ φ : L2 μ, (U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
          fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e.symm (Quotient.out y)))) ∧
        ∀ φ : L2 μ, (ContinuousLinearMap.adjoint U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
          fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out y))) := by
  intro K _ _ n μ _ e hg hp
  have hp' : MeasurePreserving e.symm μ μ := hp.symm e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by rw [← hg, e.apply_symm_apply]
  obtain ⟨h1, q1⟩ := qmapPres (Gam K n) μ e hg hp
  obtain ⟨h2, q2⟩ := qmapPres (Gam K n) μ e.symm hg' hp'
  let U : L2 μ →L[ℂ] L2 μ := (Lp.compMeasurePreservingₗᵢ ℂ _ q2).toContinuousLinearMap
  have hU : ∀ ψ : L2 μ, (U ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
      fun y => (ψ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e.symm (Quotient.out y))) :=
    fun ψ => Lp.coeFn_compMeasurePreserving ψ q2
  refine ⟨U, hU, fun φ => ?_⟩
  have key : ContinuousLinearMap.adjoint U φ = Lp.compMeasurePreserving _ q1 φ := by
    refine ext_inner_right ℂ fun ψ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
    have a1 := q1.quasiMeasurePreserving.ae_eq_comp (hU ψ)
    have m : AEStronglyMeasurable (fun y => ⟪(φ : RightCosetSpace (Gam K n) → ℂ) y, (U ψ : RightCosetSpace (Gam K n) → ℂ) y⟫_ℂ)
        (Measure.map (fun y : RightCosetSpace (Gam K n) => mk (Gam K n) (e (Quotient.out y))) (quotientMeasure (Gam K n) μ)) := by
      rw [q1.map_eq]
      exact (Lp.aestronglyMeasurable φ).inner (Lp.aestronglyMeasurable _)
    have e1 := integral_map q1.measurable.aemeasurable m
    rw [q1.map_eq] at e1
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [a1, Lp.coeFn_compMeasurePreserving φ q1] with y hy hz
    rw [hz]
    simp only [Function.comp_apply] at hy ⊢
    rw [hy, h2, e.symm_apply_apply]
    congr 2
    exact Quotient.out_eq y
  rw [key]
  exact Lp.coeFn_compMeasurePreserving φ q1
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

private theorem mapTrans (K : Type) [Field K] [NumberField K] (n : ℕ) (σ τ : K ≃+* K)
    (g : AdelicGLn.AdelicGL K n) :
    (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap (σ.trans τ)) g : AdelicGLn.AdelicGL K n) =
      Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap τ)
        (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.2 σ τ _

private theorem mapRefl (K : Type) [Field K] [NumberField K] (n : ℕ)
    (g : AdelicGLn.AdelicGL K n) :
    (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap (RingEquiv.refl K)) g : AdelicGLn.AdelicGL K n) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.1 _

private noncomputable def resMap (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (g : G1 K n) :
    G1 K n :=
  ⟨Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n),
    (UpperTheory.ConvolutionTheory.K.adNormOne K n σ g).1.2 g.2⟩

private theorem resMap_trans (K : Type) [Field K] [NumberField K] (n : ℕ) (σ τ : K ≃+* K) (g : G1 K n) :
    resMap K n τ (resMap K n σ g) = resMap K n (σ.trans τ) g :=
  Subtype.ext (mapTrans K n σ τ g).symm

private theorem resMap_refl (K : Type) [Field K] [NumberField K] (n : ℕ) (g : G1 K n) :
    resMap K n (RingEquiv.refl K) g = g :=
  Subtype.ext (mapRefl K n g)

private theorem resMap_cont (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) :
    Continuous (resMap K n σ) := by
  apply Continuous.subtype_mk _ _
  exact (show Continuous (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) :
      AdelicGLn.AdelicGL K n → AdelicGLn.AdelicGL K n) from
    (continuous_id.matrix_map (Formalism.L2.Host.CT.continuous_adMap σ)).units_map _).comp
      continuous_subtype_val

private theorem resMap_iter (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (m : ℕ) (g : G1 K n) :
    (resMap K n σ)^[m] g = resMap K n (σ ^ m) g := by
  induction m with
  | zero => exact (resMap_refl K n g).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, resMap_trans, pow_succ']
    rfl

theorem UpperTheory.ConvolutionTheory.K.galEquiv :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K), ∃ e : G1 K n ≃ₜ* G1 K n,
      (∀ g : G1 K n, ((e g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n)) ∧
      (∀ g : G1 K n, ((e.symm g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.symm) (g : AdelicGLn.AdelicGL K n)) ∧
      (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) ∧ ∃ m : ℕ, 0 < m ∧ ∀ g, (⇑e)^[m] g = g := by
  intro K _ _ n σ
  obtain ⟨m, hm, hσ⟩ := UpperTheory.ConvolutionTheory.K.autOrder K σ
  refine ⟨{ toFun := resMap K n σ
            invFun := resMap K n σ.symm
            left_inv := fun g => by rw [resMap_trans, RingEquiv.self_trans_symm, resMap_refl]
            right_inv := fun g => by rw [resMap_trans, RingEquiv.symm_trans_self, resMap_refl]
            map_mul' := fun g h => Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ))
              (g : AdelicGLn.AdelicGL K n) (h : AdelicGLn.AdelicGL K n))
            continuous_toFun := resMap_cont K n σ
            continuous_invFun := resMap_cont K n σ.symm },
    fun _ => rfl, fun _ => rfl, fun g => ?_, m, hm, fun g => ?_⟩
  · exact (UpperTheory.ConvolutionTheory.K.adNormOne K n σ g).2
  · change (resMap K n σ)^[m] g = g
    rw [resMap_iter, hσ]
    exact resMap_refl K n g
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.galCusp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (σ : K ≃+* K) (e : G1 K n ≃ₜ* G1 K n),
      (∀ g : G1 K n, ((e g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n)) →
      (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) → MeasurePreserving e μ μ → ∀ φ ψ : L2 μ, φ ∈ cuspidalL2 μ →
      ((ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out y)))) → ψ ∈ cuspidalL2 μ := by
  intro K _ _ n μ _ σ e he hg hp φ ψ hφ hψ r hr hrn
  obtain ⟨h1, -⟩ := qmapPres (Gam K n) μ e hg hp
  obtain ⟨a1, a2, a3⟩ := adBasic K
  have hinv : ∀ (τ : K ≃+* K) a, Formalism.L2.Host.CT.adMap τ.symm (Formalism.L2.Host.CT.adMap τ a) = a := fun τ a => by
    rw [← a3, RingEquiv.self_trans_symm, a2]
  let s : (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) ≃ₜ+ (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) :=
    { toFun := fun X p => Formalism.L2.Host.CT.adMap σ (X p)
      invFun := fun X p => Formalism.L2.Host.CT.adMap σ.symm (X p)
      left_inv := fun X => funext fun p => hinv σ _
      right_inv := fun X => funext fun p => hinv σ.symm _
      map_add' := fun X Y => funext fun p => map_add _ _ _
      continuous_toFun := continuous_pi fun p => (Formalism.L2.Host.CT.continuous_adMap σ).comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => (Formalism.L2.Host.CT.continuous_adMap σ.symm).comp (continuous_apply p) }
  set ν := AutomorphicForm.unipMeasure K n r with hν
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : (Measure.map s ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν s
  haveI : (Measure.map s.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν s.symm
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map s ν = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hq : Measure.QuasiMeasurePreserving s.symm ν ν :=
    ⟨s.symm.continuous.measurable.aemeasurable, by
      rw [Measure.isAddLeftInvariant_eq_smul (Measure.map s.symm ν) ν]
      exact Measure.smul_absolutelyContinuous⟩
  have hL : ∀ (τ : K ≃+* K) (X : AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K), X ∈ AutomorphicForm.unipLattice K n r →
      (fun p => Formalism.L2.Host.CT.adMap τ (X p)) ∈ AutomorphicForm.unipLattice K n r := by
    rintro τ _ ⟨ξ, rfl⟩
    exact ⟨fun p => τ (ξ p), funext fun p => (a1 τ (ξ p)).symm⟩
  have hD := (AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain (K := K) (n := n) (r := r))
  have hD' : IsAddFundamentalDomain (AutomorphicForm.unipLattice K n r)
      (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r) ν := by
    refine hD.preimage_of_equiv hq (e := fun g => ⟨s g, hL σ g g.2⟩) ⟨fun a b h => ?_, fun b => ?_⟩ fun g X => ?_
    · exact Subtype.ext (s.injective (congrArg Subtype.val h))
    · exact ⟨⟨s.symm b, hL σ.symm b b.2⟩, Subtype.ext (s.apply_symm_apply _)⟩
    · change s.symm (s g + X) = g + s.symm X
      rw [map_add (f := _), s.symm_apply_apply]
  have hu : ∀ X, e (unipOne (K := K) (n := n) r X) = unipOne (K := K) (n := n) r (s X) := by
    intro X
    refine Subtype.ext ?_
    rw [he]
    ext i j : 2
    change Formalism.L2.Host.CT.adMap σ (AutomorphicForm.unipMatrix X i j) = AutomorphicForm.unipMatrix (s X) i j
    simp only [AutomorphicForm.unipMatrix, Matrix.add_apply, AutomorphicForm.blockEntry_apply, Matrix.one_apply, map_add (f := _)]
    congr 1
    · split_ifs <;> simp
    · split_ifs
      · rfl
      · exact map_zero _
  have key : ∀ y, ctFun (K := K) (n := n) r (fun z => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out z)))) y =
      (c : ℝ) • constantTermL2 μ r φ (e y) := by
    intro y
    let F : (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) → ℂ := fun X => φ (mk (Gam K n) (unipOne (K := K) (n := n) r X * e y))
    have e1 := setIntegral_map_equiv (μ := ν) s.toHomeomorph.toMeasurableEquiv F
      (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r)
    have e2 : s.toHomeomorph.toMeasurableEquiv ⁻¹' (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r) =
        AutomorphicForm.unipFundamentalDomain K n r := by
      ext X
      change s.symm (s X) ∈ AutomorphicForm.unipFundamentalDomain K n r ↔ _
      rw [s.symm_apply_apply]
    rw [e2] at e1
    change ∫ X in _, F X ∂Measure.map s ν = ∫ X in _, F (s X) ∂ν at e1
    rw [hc, Measure.restrict_smul, integral_smul_nnreal_measure] at e1
    have e3 : ∫ X in s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r, F X ∂ν =
        ∫ X in AutomorphicForm.unipFundamentalDomain K n r, F X ∂ν := by
      refine hD'.setIntegral_eq hD fun ξ X => ?_
      change φ (mk (Gam K n) (unipOne (K := K) (n := n) r (ξ + X) * e y)) = _
      rw [unipOne_add, mul_assoc, mk_mul_of_mem (unipOne_mem_rationalGLOne r ξ)]
    rw [e3] at e1
    simp only [ctFun, constantTermL2, h1, map_mul, hu]
    exact e1.symm
  have h4 : ∀ᵐ y ∂μ, constantTermL2 μ r φ (e y) = 0 := hp.quasiMeasurePreserving.ae ((hφ : IsCuspidalL2 μ φ) r hr hrn)
  filter_upwards [ae_ctFun_congr μ r hψ, h4] with y hy1 hy2
  rw [constantTermL2, hy1, key, hy2, smul_zero, Pi.zero_apply]
end
