module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle293
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle504
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Std.Tactic.BVDecide.Normalize.Bool
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.AvgCoeff

open MeasureTheory

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]

    rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finsetSum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem coeffSpan_finiteDimensional {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | (apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan ..)

theorem coeffSpan_mulRight {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) (k' : K)
    {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) : (fun k => f (k * k')) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (· * k')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ℓ, w, rfl⟩
    exact Submodule.subset_span ⟨ℓ, ρ k' w, funext fun k => by simp [LinearMap.funLeft, map_mul]⟩
  exact this hf

end GlobalTheory.AvgCoeff

namespace GlobalTheory.CuspKFin

open Formalism.REAL GlobalTheory.Published.AutFin GlobalTheory.AvgCoeff

theorem kFinAt_avg_of_kFinAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ),
    IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ),
    GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ →
    GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  intro D θ hθ N ψ hψ τ τ' e he hK
  obtain ⟨W, i1, i2, i3, ρ, hρc, hρ⟩ := hK
  refine ⟨W, i1, i2, i3, ρ, hρc, fun x => ?_⟩
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := coeffSpan_finiteDimensional ρ
  have hec : Continuous e := by
    obtain ⟨F, -, heF, hc, -⟩ := he
    exact hc e heF
  have hAc : Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ').comp_continuous GlobalTheory.SeriesToClosure.continuous_conjK
      fun k => conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k
  have hmem : ∀ k' : Formalism.REAL.KG (N.M.ε τ'), (fun k => ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
    intro k'
    by_cases h : τ' = τ
    · subst h
      have h2 := coeffSpan_mulRight ρ k' (hρ x)
      convert h2 using 2 with k
      rw [mul_assoc]
      congr 2
      simp only [kAt]
      rw [← GlobalTheory.SeriesToClosure.at_mul hθ (N.M.fr_unit τ') (N.M.fr_gram τ')
        (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k'))]
      rfl
    · have hc : ∀ k, kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') =
          atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k := fun k =>
        GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm h) _
          (conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k) _ (conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k')
      have h2 := hρ (x * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))
      convert h2 using 2 with k
      rw [mul_assoc, hc, ← mul_assoc]
  have hcont : ∀ k, Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')) := fun k =>
    hec.mul (hψ.cont.comp (continuous_const.mul hAc))
  have key := GlobalTheory.AvgCoeff.integral_mem (muK (N.M.ε τ')) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun k' k => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')))
    (fun k' => Submodule.smul_mem _ (e k') (hmem k')) (fun k => GlobalTheory.ExpansionAverage.integrable_K (hcont k))
  exact key

end GlobalTheory.CuspKFin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.LeftRegularRepresentation

def leftRep {K : Type} [Group K] (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F) :
    Representation ℂ K F where
  toFun a :=
    { toFun := fun φ => ⟨fun k => φ.1 (a⁻¹ * k), hF _ φ.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ k
    simp
  map_mul' a b := by
    ext φ k
    simp [mul_assoc]

theorem dual_mem_span {K : Type} (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (ℓ : Module.Dual ℂ F) :
    ℓ ∈ Submodule.span ℂ (Set.range fun y : K => (LinearMap.proj y).comp F.subtype) := by
  have h : (Submodule.span ℂ (Set.range fun y : K =>
      ((LinearMap.proj y).comp F.subtype : Module.Dual ℂ F))) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push Not at hc
    exact hz (Subtype.ext (funext fun y => hc _ ⟨y, rfl⟩))
  rw [h]
  trivial

theorem isContRep_leftRep {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) : GlobalTheory.Published.AutFin.IsContRep (leftRep F hF) := by
  intro ℓ w
  induction dual_mem_span F ℓ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact (hc _ w.2).comp (continuous_inv.mul continuous_const)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

theorem conv_mem {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) {e : K → ℂ} (he : e ∈ F) {f : K → ℂ} (hf : Continuous f) :
    (fun a => ∫ k, e k * f (a * k) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan (leftRep F hF) := by
  have hi : ∀ φ : F, Integrable (fun k => φ.1 k * f k) μ := fun φ =>
    ((hc _ φ.2).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ℓ : Module.Dual ℂ F :=
    { toFun := fun φ => ∫ k, φ.1 k * f k ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  refine Submodule.subset_span ⟨ℓ, ⟨e, he⟩, funext fun a => ?_⟩
  change _ = ∫ k, e (a⁻¹ * k) * f k ∂μ
  rw [← integral_mul_left_eq_self (fun k => e (a⁻¹ * k) * f k) a]
  simp only [inv_mul_cancel_left]

theorem kFinAt_avg : ∀ (D : Formalism.BasicNotions.D7) (θ : Formalism.IndefR.Datum.InfFam D), Formalism.L2.Theta.IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : Formalism.L2.Theta.GA D (GlobalTheory.Grid.Node.V N) → ℂ), Formalism.L2.Theta.IsAutFunSm θ (GlobalTheory.Grid.Node.V N) ψ → ∀ (τ : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D)) (e : ↥(Formalism.REAL.KG (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ)) → ℂ), GlobalTheory.TypeSum.KFinFun (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) e → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ (GlobalTheory.Grid.Node.V N) τ (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) (Formalism.IndefR.Mult.DSModel.fr (GlobalTheory.Grid.Node.M N) τ) e ψ) := by
  intro D θ hθ N ψ hψ τ e he
  obtain ⟨F, hfd, heF, hc, hF⟩ := he
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hmem := GlobalTheory.Published.AutFin.conj_mem_UH hP hJ
  have hd : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hK : Continuous fun k : Formalism.REAL.KG (N.M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hk : Continuous (GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ)) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
      ((continuous_const.matrix_mul hK).matrix_mul continuous_const) hmem
  have hmul : ∀ a b, GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (a * b) =
      GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) a * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) b := by
    intro a b
    unfold GlobalTheory.Published.AutFin.kAt
    rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ (hmem a) (hmem b)]
    congr 1
    have e1 : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
    rw [e1]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  refine ⟨F, inferInstance, inferInstance, hfd, leftRep F fun φ h a => (hF φ h a).1,
    isContRep_leftRep F _ hc, fun x => ?_⟩
  have h := conv_mem (Formalism.REAL.muK (N.M.ε τ)) F (fun φ h a => (hF φ h a).1) hc heF
    (f := fun k => ψ (x * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k))
    (hψ.cont.comp (continuous_const.mul hk))
  simp only [hmul, ← mul_assoc] at h
  exact h

end GlobalTheory.LeftRegularRepresentation

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.fockAlgebraicThetaVectors_stable_lineDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X), ∀ Φ ∈ algF ψ θ ε A B,
      ∀ L : ℝ →+ WO (sgn ε M) X, Continuous L → (∀ t, (L t).map (finPart D) = 0) →
        (fun x => deriv (fun t : ℝ => heisO ψ (sgn ε M) X (L t) Φ x) 0) ∈ algF ψ θ ε A B := by
  first | exact @GlobalTheory.SquareComm.LineDeriv.deriv_line_mem_algF | exact GlobalTheory.SquareComm.LineDeriv.deriv_line_mem_algF | (intros; apply GlobalTheory.SquareComm.LineDeriv.deriv_line_mem_algF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
noncomputable section

namespace GlobalTheory.CartanLinTransfer

variable {D : D7}

theorem phi_smul_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AE D) :
    θ τ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 1 • a)) = θ τ (infPart D a) := by
  rw [GlobalTheory.ArchLineSum.infPart_smul, map_mul, GlobalTheory.ArchLineSum.theta_realAd hθ, Complex.ofReal_one, one_mul]

theorem phi_incM {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : Type} (J : Matrix m n D.host.E) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).map ((θ τ).comp (infPart D)) = J.map (tauE D τ) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, ← (hθ τ).1]
  rfl

theorem cartH_gram {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
  have hu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hJ : (Formalism.REAL.Jm (A.ε τ))ᴴ = Formalism.REAL.Jm (A.ε τ) := by
    ext a b; by_cases h : a = b
    · subst h; simp [Formalism.REAL.Jm, Matrix.conjTranspose_apply]; split_ifs <;> simp
    · simp [Formalism.REAL.Jm, Matrix.conjTranspose_apply, h, Ne.symm h]
  have hJJ : Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ) = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext a; split_ifs <;> simp
  rw [← A.fr_gram τ, Fr.cart, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_nonsing_inv]
  have h1 : ((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ = 1 := Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hu.star)
  have h2 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        simp only [Matrix.mul_assoc]
    _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * ((A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ))) * A.fr τ := by
        rw [h1, h2, Matrix.mul_one, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem cart_frSgn' (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (frSgn ε A).cart τ = (if ε then -1 else 1 : ℂ) • A.cart τ := by
  cases ε
  · simp [Fr.cart, frSgn]
  · have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
      ext a b
      by_cases hab : a = b
      · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
      · simp [Formalism.REAL.Jm, hab]
    show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = _
    rw [h, Matrix.mul_neg, Matrix.neg_mul]; simp [Fr.cart]

end GlobalTheory.CartanLinTransfer

namespace GlobalTheory.CartanLinTransfer

theorem map_conj_conj {m n : Type} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
  ext i j; simp

theorem map_conj_smul {m n : Type} (c : ℂ) (M : Matrix m n ℂ) :
    (c • M).map (starRingEnd ℂ) = (starRingEnd ℂ c) • M.map (starRingEnd ℂ) := by
  ext i j; simp

theorem map_conj_transpose {m n : Type} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j; simp [Matrix.conjTranspose_apply]

theorem alg_step {m n k : ℕ} (e : Fin m ≃ Fin k) (Ac G : Matrix (Fin n) (Fin n) ℂ) (Bc : Matrix (Fin m) (Fin m) ℂ)
    (P P' : Matrix (Fin n) (Fin k) ℂ) (s : ℂ) (hs : starRingEnd ℂ s = s) (hAG : Acᴴ * G = G * Ac)
    (h : P'.map (starRingEnd ℂ) =
      Complex.I • ((-s) • Ac * P.map (starRingEnd ℂ) * ((Matrix.reindex e e Bc).map (starRingEnd ℂ))ᵀ)) :
    P'ᵀ.submatrix e id * (s • G) = Complex.I • (Bc * (Pᵀ.submatrix e id * (s • G)) * (s • Ac)) := by
  have h2 := congrArg (fun M => M.map (starRingEnd ℂ)) h
  simp only [map_conj_conj, map_conj_smul, Matrix.map_mul, Matrix.transpose_map, Complex.conj_I, map_neg, hs] at h2
  rw [h2]
  have hsub : (Matrix.reindex e e Bc).submatrix e e = Bc := by
    ext i j; simp [Matrix.reindex_apply]
  have hprod : ∀ K : Matrix (Fin n) (Fin n) ℂ,
      (Matrix.reindex e e Bc * (Pᵀ * K)).submatrix e id = Bc * (Pᵀ.submatrix e id * K) := by
    intro K
    rw [← Matrix.submatrix_mul_equiv (Matrix.reindex e e Bc) (Pᵀ * K) e e id, hsub]
    congr 1
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul, map_conj_transpose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul, Pi.smul_apply, smul_smul]
  rw [hprod]
  simp only [Matrix.mul_assoc, hAG]
  congr 1
  ring

end GlobalTheory.CartanLinTransfer


open GlobalTheory.CartanLinTransfer in
theorem GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u u' : Matrix (Fin S.rank) (Fin d) (AE D),
      (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
        Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ)) →
    ∀ τ, compAt θ τ (GlobalTheory.VacTransfer.archLine cS u' 1) =
      cplxO ((frSgn ε A).cart τ) (B.cart τ) (compAt θ τ (GlobalTheory.VacTransfer.archLine cS u 1)) := by
  intro D θ hθ ε S X A B d e Bs Vs Ws hBs cS hcS u u' hu τ
  obtain ⟨τw, hemb, hV, hW⟩ := hBs (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
  set w : InfinitePlace D.host.F := InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) with hw
  have hembR : (Bs.emb w).1 = (starRingEnd ℂ).comp (tauE D τw) := RingHom.ext hemb
  have hτ : τw = τ := by
    apply (GlobalTheory.CMTypePlaces.places_bijective D).1
    have h2 := (Bs.emb w).2
    rw [hembR] at h2
    have h3 := congrArg InfinitePlace.mk h2
    have hc : (starRingEnd ℂ).comp ((tauE D τw).comp (algebraMap D.host.F D.host.E)) =
        ComplexEmbedding.conjugate ((tauE D τw).comp (algebraMap D.host.F D.host.E)) :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [InfinitePlace.mk_embedding, RingHom.comp_assoc, hc, InfinitePlace.mk_conjugate_eq] at h3
    exact h3
  rw [hτ] at hembR hV hW
  have hcomp : ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding := by
    rw [← hembR]; exact (Bs.emb w).2
  have hE : Bs.emb w = ⟨(starRingEnd ℂ).comp (tauE D τ), hcomp⟩ := Subtype.ext hembR
  have hpi : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = starRingEnd ℂ (((θ τ).comp (infPart D)) y) := by
    intro y; rw [hE]; exact GlobalTheory.ConjInfExp.piInf_eq θ hθ τ w hcomp y
  have hmap : ∀ v : Matrix (Fin S.rank) (Fin d) (AE D),
      v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (v.map ((θ τ).comp (infPart D))).map (starRingEnd ℂ) := by
    intro v; ext i j; simp only [Matrix.map_apply, hpi]
  have hu1 := hu w
  rw [hmap, hmap, hV, hW] at hu1
  have hz : ∀ v : Matrix (Fin S.rank) (Fin d) (AE D), compAt θ τ (GlobalTheory.VacTransfer.archLine cS v 1) =
      (v.map ((θ τ).comp (infPart D)))ᵀ.submatrix e id * ((if ε then -1 else 1 : ℂ) • gramAt D S τ) := by
    intro v
    show (cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 1 • v)).map ((θ τ).comp (infPart D)) = _
    rw [hcS, Matrix.map_mul, phi_incM hθ]
    congr 1
    · ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, id,
        RingHom.comp_apply, phi_smul_realAd hθ]
    · ext i j
      cases ε <;> simp [gramAt, Matrix.smul_apply]
  have hsgn : (if ε then 1 else -1 : ℂ) = -(if ε then -1 else 1 : ℂ) := by cases ε <;> simp
  have hs : starRingEnd ℂ (if ε then -1 else 1 : ℂ) = (if ε then -1 else 1 : ℂ) := by cases ε <;> simp
  rw [hsgn] at hu1
  rw [hz, hz, cart_frSgn', cplxO]
  exact alg_step e (A.cart τ) (gramAt D S τ) (B.cart τ) _ _ _ hs (cartH_gram A τ) hu1
end
end
