module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftDarbouxAdelicSymplectic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle204
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle494
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle521
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle391
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle019
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

section
noncomputable section
namespace GlobalTheory.ArchRep
section Real
open MeasureTheory Filter Topology GlobalTheory.RealWeil Matrix
variable {l : Type} [Fintype l] [DecidableEq l]
end Real
section Haar
open MeasureTheory
end Haar
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.RealWeil GlobalTheory.ArchUniq
theorem exists_archimedean_component : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → VacLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGen τ C γ Y → ∀ (T : Tens F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  intro hP hDer _ F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨n, θ, φ, φ₀, hp, hq, hφ, hφu⟩ := GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_frames F E σ α β κ P Q R S τ JA JB d a b A C hCM hFr
  obtain ⟨k, hkc, hkC, hkJ, hcan⟩ := GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_orthonormal_J F E σ β R S τ JB b C hCM hFr.2.2
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨ω, hωc, hωi⟩ := GlobalTheory.T.exists_oscillator_action_normalising_schrodingerOperators _ _ P Q R S φ hφ (GlobalTheory.T.continuous_rho_apply _) (UG (cA σ) JB) k hkc hkJ
  obtain ⟨s, hsc, hsφ⟩ := GlobalTheory.T.exists_continuous_symplecticHom_of_indefiniteUnitary _ _ P Q R S φ hφ (UG (cA σ) JB) k hkc hkJ
  obtain ⟨ρ, η, hη1, hη2, hη3, hρi, hρu, hρc, hρd⟩ := realRep hP.realMetaplecticRepresentation s hsc ω hωc fun g w v => by
    obtain ⟨c, rfl⟩ := φ.surjective w
    rw [hsφ, hωi]
  obtain ⟨kk, hkk⟩ := _root_.GlobalTheory.T.realLift_characterTrace_hasDerivAt hP F E σ β R S τ JB b C hCM hFr.2.2 η (fun g h _ _ => hη1 g h) hη2.continuousOn
    fun g _ => hη3 g
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑θ.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑θ := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  clear_value toE toV
  have hS := SchrTransport.schr_coords (trP F κ) θ φ₀ hp hq
  let ρ' : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ) :=
    { toFun := fun g => toV ∘L ρ g ∘L toE
      map_one' := ContinuousLinearMap.ext fun f => by
        rw [map_one]
        exact hVE f
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => by
        simp only [map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, hEV] }
  have hρ' : ∀ g f, ρ' g f = toV (ρ g (toE f)) := fun _ _ => rfl
  clear_value ρ'
  refine ⟨ρ', fun w => kk w / 2, fun g _ => ⟨fun u hu f f₁ hf h => ?_, fun ν hν f₁ f₂ => ?_⟩, fun L f => ?_,
    fun γ hγ Y hY T L => ?_⟩
  · choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    obtain ⟨c, hc⟩ : ∃ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ, ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ :=
      ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, fun w => by
        have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
        simp only [Matrix.mul_assoc]
        rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    have hu' : At (evI F) (actB (cA σ) g u) := fun t ht => by
      rw [actB, ← Matrix.smul_mul, hu t ht, Matrix.zero_mul]
    have hc' : ∀ w, (actB (cA σ) g u).map (piInf (τ w)) = A w * (c w * (k g w)ᵀ) * (C w)ᵀ := fun w => by
      rw [actB, Matrix.map_mul, hc, Matrix.transpose_map, Matrix.mul_assoc, ← Matrix.transpose_mul, hkC,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have e1 : ⇑f₁ = schrF (trP F κ) (locV (d.e u).1, locV (d.e u).2) ⇑f := by
      funext y
      have := congrFun ((GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ u hu f fun _ => 1).symm.trans (hf fun _ => 1)) (liftV y)
      simpa only [pureA, liftV, RingEquiv.apply_symm_apply, Pi.one_apply, mul_one] using this.symm
    have e2 : ⇑(toE f₁) = rhoFun (φ c) ⇑(toE f) := by
      have := hS (locV (d.e u).1, locV (d.e u).2) ⇑(toE f)
      rw [← htoV, hVE, ← e1, ← hφu u c hu hc] at this
      rw [htoE, this]
      funext x
      simp
    have e3 := hρi g _ _ _ e2
    rw [hsφ, hφu _ _ hu' hc'] at e3
    rw [GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ _ hu', hρ', hρ', htoV, htoV, hS, e3]
  · haveI : BorelSpace ({w : InfinitePlace F // w.IsReal} → ℝ) := Pi.borelSpace
    haveI : BorelSpace ({w : InfinitePlace F // w.IsComplex} → ℂ) := Pi.borelSpace
    haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
    obtain ⟨r, hr⟩ := haar_coords ν θ
    rw [hr, hr]
    congr 1
    simp only [hρ', htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hρu]
    simp only [htoE, Function.comp_apply]
  · simp only [hρ']
    exact (hρc (L ∘L toV) (toE f)).continuousOn
  · change Multiplicative ℝ →* UG (cA σ) JB at γ
    have hkY : ∀ (t : ℝ) w, k (γ (Multiplicative.ofAdd t)) w = NormedSpace.exp (t • Y w) := fun t w =>
      hcan w _ _ ((hkC _ w).symm.trans (hY t w))
    have hYu : ∀ w, Y w ∈ upq R S := fun w => GlobalTheory.RealLiftGen.mem_upq_of (Y w) fun t => by
      have := congrArg (fun X => X.map star) (hkJ (γ (Multiplicative.ofAdd t)) w)
      simp only [GlobalTheory.RealLiftGen.map_star_mul, GlobalTheory.RealLiftGen.Jm_map_star, hkY] at this
      refine Eq.trans ?_ this
      congr 2
      ext i j
      simp
    obtain ⟨Z, hZ, hZφ, hZe⟩ := GlobalTheory.T.exists_symplecticLie_of_indefiniteUnitaryLie_rightAction _ _ P Q R S φ hφ Y hYu
    have hsZ : ∀ t : ℝ, (s (γ (Multiplicative.ofAdd t)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        NormedSpace.exp (t • Z) := fun t => Matrix.toLin'.injective (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := φ.surjective v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
      change (s (γ (Multiplicative.ofAdd t)) : Matrix _ _ ℝ) *ᵥ φ c = NormedSpace.exp (t • Z) *ᵥ φ c
      rw [hsφ, hZe]
      simp only [hkY])
    have hd := hρd (fun t => γ (Multiplicative.ofAdd t)) (hγ.1.comp continuous_ofAdd) (by exact map_one γ) Z hZ hsZ _
      (hkk γ hγ Y hY) (L ∘L toV) (toE (Φ T))
    obtain ⟨D, hD⟩ := hDer F E σ α β κ ψ JA JB d hψ
    have hΨ : ∀ c T, (toE.toLinearMap ∘ₗ Φ) (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) ((toE.toLinearMap ∘ₗ Φ) T) := by
      intro c T
      obtain ⟨u, ⟨hu, hc⟩, -⟩ := GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM fun w => A w * c w * (C w)ᵀ
      have e1 := (GlobalTheory.RealLift.actsLaws F κ (Φ T) _ _).2.2.2.2 _ (hΦ.2 u hu c hc T) (hD u hu (Φ T)).1
      ext x
      obtain ⟨y, rfl⟩ := θ.surjective x
      have e2 := SchrTransport.dRho_coords (trP F κ) θ φ₀ hp hq (locV (d.e u).1, locV (d.e u).2) (Φ T) (toE (Φ T))
        (by rw [← htoV, hVE]) y
      rw [← hφu u c hu hc] at e2
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [← e2, e1, htoE, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact (hD u hu (Φ T)).2 y
    have e3 := GlobalTheory.T.fockToSchwartz_intertwines_metaplecticQuadratic GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic _ _ P Q R S φ hφ _ hΨ Y hYu Z hZφ T
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at e3
    have hfun : (fun t : ℝ => L (ρ' (γ (Multiplicative.ofAdd t)) (Φ T))) =
        (fun t : ℝ => (L ∘L toV) (ρ (γ (Multiplicative.ofAdd t)) (toE (Φ T)))) := by
      funext t
      exact congrArg L (hρ' _ _)
    refine hfun.symm ▸ hd.congr_deriv ?_
    rw [e3, sumPl_add_smul]
    simp only [ContinuousLinearMap.comp_apply, hVE, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, smul_eq_mul, Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun w _ => by ring
end GlobalTheory.ArchRep
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

theorem _root_.GlobalTheory.T.archimedean_component_discreteSeries : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → VacLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGen τ C γ Y → ∀ (T : Tens F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  first | exact @_root_.GlobalTheory.ArchRep.exists_archimedean_component | exact _root_.GlobalTheory.ArchRep.exists_archimedean_component | (intros; apply _root_.GlobalTheory.ArchRep.exists_archimedean_component <;> assumption)
end
end

section

section
open scoped Matrix
noncomputable section
namespace GlobalTheory.MetaplecticScalarDeriv
open MeasureTheory Filter Topology GlobalTheory.RealWeil
theorem metaplectic_scalar_derivative_nonempty (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (l : Type) [Fintype l] [DecidableEq l] [Nonempty l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hZ : Z ∈ LieAlgebra.Symplectic.sp l ℝ)
    (T : ℝ → Sch l →ₗ[ℂ] Sch l) (hT0 : T 0 = LinearMap.id) (hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hTrho : ∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h →
      ⇑(T t h₁) = rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h))
    (hTiso : ∀ (t : ℝ) (h : Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2)
    (hTcont : ∀ (h : Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) :
    ∃ a : ℂ, ∀ f : Sch l,
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + quad Z f)) := by
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, -, h6⟩ := hP.realMetaplecticRepresentation l
  obtain ⟨γ, -, hγ0, hγadd, hγpr, hγd⟩ := h6 Z hZ
  have hmul : ∀ s t (f : Sch l), omS (γ s) (omS (γ t) f) = omS (γ (s + t)) f := by
    intro s t f
    rw [hγadd, map_mul]
    rfl
  have hS1 : ∀ t (f : Sch l), omS (γ (-t)) (omS (γ t) f) = f := by
    intro t f
    rw [hmul, neg_add_cancel, hγ0, map_one]
    rfl
  have hS2 : ∀ t (f : Sch l), omS (γ t) (omS (γ (-t)) f) = f := by
    intro t f
    rw [hmul, add_neg_cancel, hγ0, map_one]
    rfl
  have hmat : ∀ t (w : l ⊕ l → ℝ), NormedSpace.exp (t • Z) *ᵥ ((pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
    intro t w
    have e : pr (γ t) * pr (γ (-t)) = 1 := by rw [← map_mul, ← hγadd, add_neg_cancel, hγ0, map_one]
    have e' : (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
      congrArg (fun g : Matrix.symplecticGroup l ℝ => (g : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
    rw [← hγpr t, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
  have hU : ∀ t, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, (T t ∘ₗ (omS (γ (-t)) : Sch l →ₗ[ℂ] Sch l)) h = a • h := by
    intro t
    refine _root_.GlobalTheory.T.real_weil_representation_schur_scalar hP l _ (fun w h h₁ hh => ?_) (fun h => ?_)
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTrho t _ _ _ (intertwine_fun l _ (om (γ (-t))) (omS (γ (-t))) (h3 _) (h4 _) w h h₁ hh), hmat]
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTiso, lintegral_iso l (om (γ (-t))) (omS (γ (-t))) (h4 _)]
  choose ν _hνn hν using hU
  have hTν : ∀ t (f : Sch l), T t f = ν t • omS (γ t) f := by
    intro t f
    have := hν t (omS (γ t) f)
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hS1] using this
  obtain ⟨f0, hf0⟩ := exists_schwartz_one l
  have hν0 : ν 0 = 1 := by
    have e := congrArg (fun g : Sch l => g 0) (hTν 0 f0)
    simp only [hT0, LinearMap.id_apply, hγ0, map_one, SchwartzMap.smul_apply, smul_eq_mul, hf0] at e
    change 1 = ν 0 * (1 : Sch l →L[ℂ] Sch l) f0 0 at e
    rw [ContinuousLinearMap.one_apply, hf0, mul_one] at e
    exact e.symm
  have hνmul : ∀ s t, ν (s + t) = ν s * ν t := by
    intro s t
    set f := omS (γ (-(s + t))) f0
    have e1 : T (s + t) f = ν (s + t) • f0 := by rw [hTν, hS2]
    have e2 : T (s + t) f = (ν s * ν t) • f0 := by
      rw [hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, hmul, hS2, smul_smul, mul_comm]
    have e := congrArg (fun g : Sch l => g 0) (e1.symm.trans e2)
    simpa [hf0] using e
  have hcontS : ContinuousAt (fun t => omS (γ t) f0) 0 := by
    have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f0
    have h1 : Tendsto (fun t : ℝ => t • (t⁻¹ • (omS (γ t) f0 - f0))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • quad Z f0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hd
    rw [zero_smul] at h1
    have h2 : Tendsto (fun t : ℝ => omS (γ t) f0) (𝓝[≠] 0) (𝓝 f0) := by
      have h1' := h1.add_const f0
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hγ0, map_one]
    exact h2
  have hcontS0 : ContinuousAt (fun t => omS (γ t) f0 0) 0 := (continuous_eval l 0).continuousAt.comp hcontS
  have hS00 : omS (γ 0) f0 0 ≠ 0 := by
    rw [hγ0, map_one, ContinuousLinearMap.one_apply, hf0]
    exact one_ne_zero
  have hνc : ContinuousAt ν 0 := by
    have hq : ContinuousAt (fun t => T t f0 0 / omS (γ t) f0 0) 0 :=
      (hTcont f0 0).continuousAt.div hcontS0 hS00
    refine hq.congr ?_
    filter_upwards [hcontS0.eventually_ne hS00] with t ht
    rw [hTν, SchwartzMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ht]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' ν hν0 hνmul hνc
  refine ⟨a, fun f => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 ha
  simp only [zero_add, hν0] at hslope
  have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f
  have hν1 : Tendsto ν (𝓝[≠] 0) (𝓝 1) := by
    rw [← hν0]
    exact hνc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hν1.smul hd).add (hslope.smul_const f)
  rw [one_smul, add_comm] at hlim
  refine hlim.congr fun t => ?_
  rw [hTν]
  ext x
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]
  ring
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  intro hP l _ _ Z hZ T hT0 hTadd hTrho hTiso hTcont
  rcases isEmpty_or_nonempty l with hl | hl
  · exact main_empty l Z T hT0 hTadd hTcont
  · exact _root_.GlobalTheory.MetaplecticScalarDeriv.metaplectic_scalar_derivative_nonempty hP l Z hZ T hT0 hTadd hTrho hTiso hTcont
end GlobalTheory.MetaplecticScalarDeriv
end
end

section
open scoped Matrix

theorem _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  first | exact @_root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | exact _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DarbImage
section Generic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
end Generic
end GlobalTheory.DarbImage
namespace GlobalTheory.DarbImage
theorem theta_image_darboux_basis : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ T : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb).map T = algF ψ θ true A B) ∧
        ∀ T : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W₁ X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb).map T = algF ψ θ false A₁ B := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hG : Γ.M.IsGood Bs.ψ := hM.triple.geo.hM
  have hG' : Γ.M'.IsGood Bs.ψ := hM.triple.geo.hM'
  have hs := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hG
  have hs' := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hG'
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · refine map_eq Γ.M Bs.ψ Bs.emb _ T _ hs hT
      (_root_.GlobalTheory.T.gaussian_theta_lift_algebraic hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM)
      (fun f φ u f₁ hf hu hA h1 h2 hin => ?_) ?_
    · obtain ⟨L, hLc, hLf, hL⟩ := _root_.GlobalTheory.T.theta_pure_tensor_hasDerivAt_first hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM f φ u f₁ hf hu hA h1 h2
      rw [hL]
      exact GlobalTheory.T.fockAlgebraicThetaVectors_stable_lineDerivative D ψ θ hψ hθ true W X A B _ hin L hLc hLf
    · rw [algF, Submodule.span_le]
      rintro q ⟨g, P, hg, rfl⟩
      obtain ⟨Φ, hΦ, hΦe⟩ := _root_.GlobalTheory.T.theta_lift_onto_fockSpace hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM g P hg
      exact ⟨Φ, hΦ, by rw [hT Φ (hs hΦ), hΦe]⟩
  · refine map_eq Γ.M' Bs.ψ Bs.emb _ T _ hs' hT
      (_root_.GlobalTheory.T.pure_gaussian_theta_lift_algebraic hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM)
      (fun f φ u f₁ hf hu hA h1 h2 hin => ?_) ?_
    · obtain ⟨L, hLc, hLf, hL⟩ := _root_.GlobalTheory.T.theta_pure_tensor_hasDerivAt_second hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM f φ u f₁ hf hu hA h1 h2
      rw [hL]
      exact GlobalTheory.T.fockAlgebraicThetaVectors_stable_lineDerivative D ψ θ hψ hθ false W₁ X A₁ B _ hin L hLc hLf
    · rw [algF, Submodule.span_le]
      rintro q ⟨g, P, hg, rfl⟩
      obtain ⟨Φ, hΦ, hΦe⟩ := _root_.GlobalTheory.T.fockSpace_contained_darbouxAlgebra_theta_image hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM g P hg
      exact ⟨Φ, hΦ, by rw [hT Φ (hs' hΦ), hΦe]⟩
end GlobalTheory.DarbImage
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

theorem _root_.GlobalTheory.T.theta_image_eq_span_darboux : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ T : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb).map T = algF ψ θ true A B) ∧
        ∀ T : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W₁ X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb).map T = algF ψ θ false A₁ B := by
  first | exact @_root_.GlobalTheory.DarbImage.theta_image_darboux_basis | exact _root_.GlobalTheory.DarbImage.theta_image_darboux_basis | (intros; apply _root_.GlobalTheory.DarbImage.theta_image_darboux_basis <;> assumption)
end
end
