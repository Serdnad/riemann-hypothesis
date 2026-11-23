module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle190
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle422
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle035
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TendstoSlopeOfArchimedeanPairing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle507
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SchwartzFunctionSlopeEstimate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

section
noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
namespace GlobalTheory.LieScal
open scoped Classical in
theorem lie_algebra_acts_by_scalar : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → VacLine → LieScalar := by
  intro hP hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom
  obtain ⟨ω₀, c₀, hH, hc, hact⟩ := _root_.GlobalTheory.T.isGeneric_localComponent hP hD hV F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ν, hν, hmul, hνc, hν0⟩ := _root_.GlobalTheory.T.metaplectic_splitting_unique_up_to_character hP F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.T.realLift_characterTrace_hasDerivAt hP F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0
  unfold cA at *
  refine ⟨fun w => c₀ w + k w, ?_⟩
  intro γ hγ Y hY T g hg l hl
  have hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) := fun t => hγ.2 _
  have hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
      fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g)) := by
    funext t; rw [hν _ (hH1 t) (pureA F (Φ T) g) (hpm (Φ T)), map_smul, smul_eq_mul]
  show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0
  rw [e1]
  have h3 := (hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)
  have hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by rw [ofAdd_zero, map_one]
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hν1 : ν 1 = 1 := by
    have := hmul 1 1 h1m h1m
    rw [mul_one] at this
    exact (mul_eq_left₀ (hν0 1 h1m)).mp this.symm
  beta_reduce at h3
  simp only [hγ0, hν1, map_one, Module.End.one_apply, one_mul] at h3
  refine h3.congr_deriv ?_
  have e2 : sumPl (fun w => fockAct2 P Q R S (Y w) + (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) =
      sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) +
        (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (Tens F P Q R S)) := by
    simp only [add_mul, add_smul, ← add_assoc]
    exact sumPl_add_smul (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _
  rw [e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul]
  have key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g := by
    intro z f f'; funext x; simp [pureA]; ring
  rw [key, map_add (f := _), map_smul, smul_eq_mul]
end GlobalTheory.LieScal
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weil_lie_algebra_scalar_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := by
  first | exact @_root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar | exact _root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar | (intros; apply _root_.GlobalTheory.LieScal.lie_algebra_acts_by_scalar <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DerPol
theorem polarization_pair_derivation (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (F := F) E w) (χX χW : Chr F E) (om : Rep σ X W) (hcm : IsCMExt F E σ) (hψ : IsStd ψ)
    (hW : M.IsWeil ψ χX χW om) :
    ∀ γ ∈ Lines σ W, ∃ δ : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f ∈ M.Pol ψ τ,
      δ f ∈ M.Pol ψ τ ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro γ hγ
  obtain ⟨m, u, v, c, c₀, hat, hQ⟩ := _root_.GlobalTheory.T.oscillator_lie_action_quadratic hP M ψ χX χW om hcm hψ hW γ hγ
  choose Du hDu using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (u i) (hat i).1
  choose Dv hDv using fun i => GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine M ψ hψ (v i) (hat i).2
  have closed : ∀ w, At (evI F) w → ∀ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ w) f (D f)) → ∀ f ∈ M.Pol ψ τ, D f ∈ M.Pol ψ τ := by
    intro w hw D hD f hf
    rw [Model.Pol, Submodule.mem_sInf] at hf ⊢
    intro N hN
    exact hN.2 w hw f (hf N hN) (D f) (hD f)
  refine ⟨∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id, fun f hf => ⟨?_, ?_⟩⟩
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ hf)
    exact closed _ (hat i).1 _ (hDu i) _ (closed _ (hat i).2 _ (hDv i) _ hf)
  · intro r hr x
    choose F₁ hF₁ using fun t : ℝ => _root_.GlobalTheory.T.theta_action_archimedean_locality hP M ψ χX χW om hcm hψ hW (γ (Multiplicative.ofAdd t)) (hγ.2 _) f
    have hd := hQ f (fun i => Dv i f) (fun i => Du i (Dv i f)) (fun i => hDv i f) (fun i => hDu i _) F₁ hF₁
      (fun i => evI F (x i))
    have e : (fun t => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) x) =
        fun t => F₁ t (fun i => evI F (x i)) * r x := by
      funext t; rw [hF₁ t r hr]; rfl
    rw [e]
    refine (hd.mul_const (r x)).congr_deriv ?_
    show _ = ((∑ i, c i • (Du i ∘ₗ Dv i) + c₀ • LinearMap.id : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) f) (fun i => evI F (x i)) * r x
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul]
    congr 2
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, SchwartzMap.add_apply, ih]; simp
theorem exists_lie_derivative_model : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  exact _root_.GlobalTheory.DerPol.polarization_pair_derivation hP G.M' B.ψ B.emb X.α (X.α / X.β) om' hT.base.cm hT.base.std hT.weil' γ hγ
end GlobalTheory.DerPol
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.twist_lie_derivative_model : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')), ∀ f ∈ G.M'.Pol B.ψ B.emb,
      δ f ∈ G.M'.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  first | exact @_root_.GlobalTheory.DerPol.exists_lie_derivative_model | exact _root_.GlobalTheory.DerPol.exists_lie_derivative_model | (intros; apply _root_.GlobalTheory.DerPol.exists_lie_derivative_model <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical
end GlobalTheory.ThetaLineDeriv
namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ m f f₁ r hR hD u
  have hS := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP G.M B.ψ X.β (X.β / X.α) om hT.base.cm hT.base.std hT.weil γ hγ
  have key : ∀ i, ∃ (v : ℝ → ℂ) (w : ℂ), (∀ t : ℝ, HasSum (fun ξ : Fin a × Fin (a + a') → F =>
      G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)))
        (fun j => algebraMap F (AF F) (ξ j))) (v t)) ∧
      HasSum (fun ξ : Fin a × Fin (a + a') → F => G.M.co.rho B.ψ u (tens (evI F) (⇑(f₁ i)) (r i))
        (fun j => algebraMap F (AF F) (ξ j))) w ∧ HasDerivAt v w 0 := by
    intro i
    by_cases h0 : f i = 0
    · have ht0 : tens (evI F) (⇑(f i)) (r i) = 0 := by funext x; simp [tens, h0]
      have ht1 : tens (evI F) (⇑(f₁ i)) (r i) = 0 := by
        funext x
        have h := hD i (r i) (hR i) x
        simp only [ht0, map_zero, Pi.zero_apply] at h
        exact h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      refine ⟨fun _ => 0, 0, fun t => ?_, ?_, hasDerivAt_const _ _⟩
      · rw [ht0, map_zero, rho_zero]; exact hasSum_zero
      · rw [ht1, rho_zero]; exact hasSum_zero
    · obtain ⟨c, c', hc0, hl, hact⟩ := hS (f i)
      obtain ⟨T, hT'⟩ := GlobalTheory.ThetaSchrCont.exists_clm_hasSum G.M B.ψ hT.base.std u (f i) (r i) (hR i) h0
      have htens : tens (evI F) (⇑(f₁ i)) (r i) = tens (evI F) (⇑c') (r i) := by
        funext x
        have h1 := hD i (r i) (hR i) x
        have h2 : HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)) x)
            (tens (evI F) (⇑c') (r i) x) 0 := by
          have e : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)) x) =
              fun t => c t (fun j => evI F (x j)) * r i x := by
            funext t; rw [hact t (r i) (hR i)]; rfl
          rw [e]
          exact (hasDerivAt_eval c (f i) c' hc0 hl _).mul_const _
        exact h1.unique h2
      refine ⟨fun t => T (c t), T c', fun t => ?_, ?_, hasDerivAt_clm c (f i) c' hc0 hl T⟩
      · rw [hact t (r i) (hR i)]; exact hT' (c t)
      · rw [htens]; exact hT' c'
  choose v w hv hw hd using key
  have e1 : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, tens (evI F) (⇑(f i)) (r i)))) = ∑ i, v i t := by
    intro t

    rw [map_sum, rho_sum]
    refine HasSum.tsum_eq ?_
    convert hasSum_sum (s := Finset.univ) (fun i _ => hv i t) using 1
    funext ξ
    simp [Finset.sum_apply]
  have e2 : GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i))) = ∑ i, w i := by
    rw [rho_sum]
    refine HasSum.tsum_eq ?_
    convert hasSum_sum (s := Finset.univ) (fun i _ => hw i) using 1
    funext ξ
    simp [Finset.sum_apply]
  rw [show (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, tens (evI F) (⇑(f i)) (r i))))) = fun t => ∑ i, v i t from funext e1, e2]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  have e3 : (fun t : ℝ => ∑ i, v i t) = ∑ i, v i := by funext t; simp [Finset.sum_apply]
  rw [e3]
  exact hs
end GlobalTheory.ThetaLineDeriv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.twisted_theta_line_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally | exact _root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDerY
theorem hasDerivAt_thetaSum_along_line_y_direction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hG hW γ hγ f f₁ r hR hD u
  by_cases hf : f = 0
  ·
    subst hf
    have hR0 : Rest (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r := hR
    have ht0 : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r = 0 := by
      funext x; simp [tens]
    have h1 : tens (evI F) (⇑f₁) r = 0 := by
      funext x
      have h := hD r hR0 x
      simp only [ht0, map_zero] at h
      exact (h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))).trans rfl
    have hrho0 : M.co.rho ψ u 0 = 0 := by
      funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hth0 : GlobalTheory.WeilM.thetaSum F (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := by
      simp [GlobalTheory.WeilM.thetaSum]
    simp only [ht0, h1, map_zero, hrho0, hth0]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)
  obtain ⟨c, g, hc, hlim⟩ := _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M ψ χX χW om hψ hG hW γ hγ f r hR
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.ThetaSchrCont.exists_clm_hasSum M ψ hψ u f r hR hf
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r))))
      = fun t => Λ (c t) := by
    funext t
    rw [hc t]
    exact (hΛ (c t)).tsum_eq
  have ev : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      Continuous fun s : SInf F (Fin n × Fin d) => s y := by
    intro y
    have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
    exact (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ) y).comp h1
  have hg : tens (evI F) (⇑g) r = tens (evI F) (⇑f₁) r := by
    funext x
    have h1 := hD r hR x
    have h2 : HasDerivAt (fun t : ℝ => tens (evI F) (⇑(c t)) r x) (tens (evI F) (⇑g) r x) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      refine ((((ev _).tendsto g).comp hlim).mul_const (r x)).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, tens]
      rw [slope_def_module]
      simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
      ring
    have h3 : (fun t : ℝ => tens (evI F) (⇑(c t)) r x) =
        fun t => om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) (⇑f) r) x := by
      funext t; rw [hc t]
    rw [h3] at h2
    exact h2.unique h1
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (tens (evI F) (⇑f₁) r)) = Λ g := by
    rw [← hg]; exact (hΛ g).tsum_eq
  rw [hcurve, hend, hasDerivAt_iff_tendsto_slope]
  refine (Λ.continuous.tendsto g |>.comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp [slope_def_module, map_sub, map_smul]
end GlobalTheory.ThetaLineDerY
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.thetaSum_differentiable_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_along_line_y_direction | exact _root_.GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_along_line_y_direction | (intros; apply _root_.GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_along_line_y_direction <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ArchProdRule
open Filter Topology
open scoped Classical in
theorem archimedean_hasDerivAt_prod : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW k γ hγ T hT hadd h0 f y c hc
  have hQ : ∀ i g, ∃ q, Tendsto (fun t : ℝ => t⁻¹ • (T i t g - g)) (𝓝[≠] 0) (𝓝 q) := fun i g =>
    _root_.GlobalTheory.T.schwartz_function_slope_estimate hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i) g
  choose Q hQ using hQ
  have hcont : ∀ i t, Continuous (T i t) := fun i =>
    _root_.GlobalTheory.T.archimedean_weil_representation_continuous hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i)
  have hprod := slope_prod k T Q hcont h0 hQ f
  let ev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
  have hev : ∀ (s : ℝ) (g h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), ev (s • (g - h)) = s • (g y - h y) := by
    intro s g h
    rw [ContinuousLinearMap.map_smul_of_tower, map_sub]
    rfl
  have hevq : ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), ev g = g y := fun g => rfl
  have hci : ∀ i, c i = Q i f y := by
    intro i
    have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hc i)
    have h2 := (ev.continuous.tendsto _).comp (hQ i f)
    rw [hevq] at h2
    simp only [zero_add, h0] at h1
    refine tendsto_nhds_unique h1 (h2.congr fun t => ?_)
    exact hev _ _ _
  have hsum : (∑ i, c i) = ev (∑ i, Q i f) := by

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (hci i).trans (hevq _).symm
  rw [hasDerivAt_iff_tendsto_slope_zero, hsum]
  have hp0 : (List.ofFn fun i => T i 0).prod = 1 := by
    have e : (fun i => T i 0) = fun _ => (1 : Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) :=
      funext fun i => LinearMap.ext (h0 i)
    rw [e, List.ofFn_const, List.prod_replicate, one_pow]
  have h1 := (ev.continuous.tendsto _).comp hprod
  refine h1.congr fun t => ?_
  simp only [Function.comp_apply, zero_add, hp0]
  exact hev _ _ _
end GlobalTheory.ArchProdRule
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.archimedean_product_rule_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  first | exact @_root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod | exact _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod | (intros; apply _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod <;> assumption)
end
end
