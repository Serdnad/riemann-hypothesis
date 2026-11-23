module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle196
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

section

open GlobalTheory.ArchUniq GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.ArchUniq.SchrTransport

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coords (P : V → V → ℝ) (hP : IsPairing P) [FiniteDimensional ℝ V] (n : ℕ) (hn : Module.finrank ℝ V = n) :
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, pPart (φ v) = C v.1) ∧ ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2 := by
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  refine ⟨C, φ, fun v => ?_, fun v y => ?_⟩
  · ext i; simp [hφ, pPart, pairCoordsL]
  · rw [pair_expand C hP y v.2]
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]

theorem schr_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (v : V × V) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    schrF P v (f ∘ C) = rhoFun (φ v) f ∘ C := by
  funext y
  have h2 : ⟪pPart (φ v), qPart (φ v)⟫ = -P v.1 v.2 := by rw [hp, real_inner_comm, hq]
  have h3 : ⟪C v.1, qPart (φ v)⟫ = -P v.1 v.2 := by rw [real_inner_comm, hq]
  simp only [schrF, rhoFun, phase, Function.comp_apply, map_add (f := _), hp, hq, h3]
  congr 2
  push_cast
  ring

theorem dRho_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (u : V × V) (g : 𝓢(V, ℂ)) (h : Sch (Fin n))
    (hg : ⇑g = ⇑h ∘ ⇑C) (y : V) :
    fderiv ℝ (⇑g) y u.1 - 2 * Real.pi * Complex.I * (P y u.2 : ℂ) * g y = dRho (φ u) h (C y) := by
  have hd : HasFDerivAt (⇑h ∘ ⇑C) ((fderiv ℝ (⇑h) (C y)).comp (C : V →L[ℝ] EuclideanSpace ℝ (Fin n))) y :=
    (h.hasFDerivAt (C y)).comp y C.hasFDerivAt
  rw [dRho_apply, hg, hd.fderiv, hp, hq]
  simp
  ring

theorem quad_eq_sum {l : Type} [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    quad X = ∑ p : (l ⊕ l) × (l ⊕ l), ((4 * Real.pi * Complex.I : ℂ)⁻¹ *
      ((((X * Matrix.J l ℝ) p.1 p.2 + (X * Matrix.J l ℝ) p.2 p.1) / 2 : ℝ) : ℂ)) •
        (dRho (Pi.single p.1 1) * dRho (Pi.single p.2 1)) := by
  rw [quad, Fintype.sum_prod_type, Finset.smul_sum]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => (4 * Real.pi * Complex.I : ℂ)⁻¹ • (((X * Matrix.J l ℝ) a b / 2 : ℝ) : ℂ) •
    (dRho (Pi.single b 1) * dRho (Pi.single a 1))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_smul]
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem haar_coords {n : ℕ} [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, 0 < k ∧ ∀ F : V → ℝ, ∫ y, F y ∂μ = k * ∫ x, F (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ),
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun F => ?_⟩
  have h1 : ∫ y, F y ∂μ = ∫ x, F (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, F (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    (∀ (A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n)),
      (∀ w, Continuous fun t => A' t w) → (∀ s t f, T' (s + t) f = T' s (T' t f)) → (∀ f, T' 0 f = f) →
      (∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f)) →
      (∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T' t f y) →
      ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℂ),
        ∀ f y, HasDerivAt (fun t => T' t f y) (quad X f y + c * f y) 0) →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro V _ _ _ _ _ μ hμ P hP n hn H A T hAc hTadd hT0 hTi hTl2 hTc
  obtain ⟨C, φ, hp, hq⟩ := coords P hP n hn
  have hS := schr_coords P C φ hp hq
  let toE : 𝓢(V, ℂ) →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n) := fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := haar_coords μ C
  have c1 : ∀ w, Continuous fun t => A' t w := by
    intro w
    exact (φ.toLinearMap.continuous_of_finiteDimensional).comp (hAc (φ.symm w))
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have c6 : ∀ f y, Continuous fun t => T' t f y := by
    intro h y
    exact hTc (toV h) (C.symm y)
  obtain ⟨X, c, hX⟩ := H A' T' c1 c2 c3 c4 c5 c6
  let eq := (Fintype.equivFin ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))).symm
  let S := X * Matrix.J (Fin n) ℝ
  refine ⟨Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)), fun i => φ.symm (Pi.single (eq i).1 1),
    fun i => φ.symm (Pi.single (eq i).2 1),
    fun i => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S (eq i).1 (eq i).2 + S (eq i).2 (eq i).1) / 2 : ℝ) : ℂ), c, ?_⟩
  intro f g₁ g₂ hg₁ hg₂ y
  have hf : ⇑f = ⇑(toE f) ∘ ⇑C := by ext x; simp [htoE]
  have h1 : ∀ i, ⇑(g₁ i) = ⇑(dRho (Pi.single (eq i).2 1) (toE f)) ∘ ⇑C := fun i => by
    ext x
    rw [hg₁, dRho_coords P C φ hp hq _ f (toE f) hf, LinearEquiv.apply_symm_apply]
    rfl
  have h2 : ∀ i, g₂ i y = dRho (Pi.single (eq i).1 1) (dRho (Pi.single (eq i).2 1) (toE f)) (C y) := fun i => by
    rw [hg₂, dRho_coords P C φ hp hq _ (g₁ i) _ (h1 i), LinearEquiv.apply_symm_apply]
  have hd := hX (toE f) (C y)
  have e1 : (fun t => T' t (toE f) (C y)) = fun t => T t f y := by
    funext t
    simp [hT', htoE, hVE]
  rw [e1] at hd
  convert hd using 1
  have e2 : toE f (C y) = f y := by simp [htoE]
  rw [e2, quad_eq_sum]
  congr 1
  simp only [h2, ContinuousLinearMap.coe_sum', Finset.sum_apply, SchwartzMap.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.mul_apply, smul_eq_mul]
  exact Equiv.sum_comp eq (fun p => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S p.1 p.2 + S p.2 p.1) / 2 : ℝ) : ℂ) *
    dRho (Pi.single p.1 1) (dRho (Pi.single p.2 1) (toE f)) (C y))

end GlobalTheory.ArchUniq.SchrTransport
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.UnitFv

theorem unitary_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v))
  (hπ : ∀ z, π₁ (cA σ z) = π₂ z) (g : GlobalTheory.DblVac.UD σ W) :   (Matrix.fromBlocks (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))))ᵀ *
    Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) *
    (Matrix.fromBlocks (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) =
  Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) := by
  set M := GlobalTheory.DblVac.matD g with hMdef
  set J₁ : Matrix (Fin d) (Fin d) (Fv F v) := (incM F W.J).map π₁ with hJ₁
  have hg : Mᵀ * dbl (incM F W.J) * M.map (cA σ) = dbl (incM F W.J) := g.2
  have hmap := congrArg (fun X => X.map π₁) hg
  simp only [Matrix.map_mul, Matrix.transpose_map] at hmap
  have h2 : (M.map (cA σ)).map π₁ = M.map π₂ := by
    rw [Matrix.map_map]; ext i j; simp [hπ]
  have hD : (dbl (incM F W.J)).map π₁ = Matrix.fromBlocks J₁ 0 0 (-J₁) := by
    simp [dbl, Matrix.fromBlocks_map, hJ₁]
    try (ext i j; simp)
  rw [h2, hD] at hmap

  have hblk : ∀ (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b : GL (Fin d) (Fv F v)),
      Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
        (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * M.toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      = Matrix.fromBlocks ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
        * M.map π * Matrix.fromBlocks (b : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b : Matrix (Fin d) (Fin d) (Fv F v)) := by
    intro π b
    have : M.map π = Matrix.fromBlocks (M.toBlocks₁₁.map π) (M.toBlocks₁₂.map π) (M.toBlocks₂₁.map π) (M.toBlocks₂₂.map π) := by
      rw [← Matrix.fromBlocks_map, Matrix.fromBlocks_toBlocks]
    rw [this, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hmid : Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * J₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * J₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))))
      = (Matrix.fromBlocks (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₁ : Matrix (Fin d) (Fin d) (Fv F v)))ᵀ * Matrix.fromBlocks J₁ 0 0 (-J₁)
        * Matrix.fromBlocks (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hinv : ∀ b : GL (Fin d) (Fv F v),
      Matrix.fromBlocks (b : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b : Matrix (Fin d) (Fin d) (Fv F v)) *
      Matrix.fromBlocks ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) = 1 := by
    intro b
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  rw [hblk π₁ b₁, hblk π₂ b₂, hmid]
  set P₁ := Matrix.fromBlocks (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₁ : Matrix (Fin d) (Fin d) (Fv F v))
  set P₂ := Matrix.fromBlocks (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 (b₂ : Matrix (Fin d) (Fin d) (Fv F v))
  set Q₁ := Matrix.fromBlocks ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
  set Q₂ := Matrix.fromBlocks ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) 0 0 ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))
  have e1 : Q₁ᵀ * P₁ᵀ = 1 := by rw [← Matrix.transpose_mul, hinv b₁, Matrix.transpose_one]
  have e2 : P₂ * Q₂ = 1 := hinv b₂
  set D := Matrix.fromBlocks J₁ 0 0 (-J₁)
  calc (Q₁ * M.map π₁ * P₁)ᵀ * (P₁ᵀ * D * P₂) * (Q₂ * M.map π₂ * P₂)
      = P₁ᵀ * ((M.map π₁)ᵀ * (Q₁ᵀ * P₁ᵀ) * D * (P₂ * Q₂) * M.map π₂) * P₂ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = P₁ᵀ * D * P₂ := by
        rw [e1, e2, Matrix.mul_one, Matrix.mul_one, hmap, Matrix.mul_assoc]

end GlobalTheory.UnitFv
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVac.BlocksPreserved

theorem blocks_keep {R : Type} [CommRing R] {d : ℕ} (S : AddSubgroup (Fin d → R))
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R)
    (h : ∀ z : Fin d ⊕ Fin d → R, z ∘ Sum.inl ∈ S → z ∘ Sum.inr ∈ S →
      (M *ᵥ z) ∘ Sum.inl ∈ S ∧ (M *ᵥ z) ∘ Sum.inr ∈ S) :
    (∀ z ∈ S, M.toBlocks₁₁ *ᵥ z ∈ S) ∧ (∀ z ∈ S, M.toBlocks₁₂ *ᵥ z ∈ S) ∧
    (∀ z ∈ S, M.toBlocks₂₁ *ᵥ z ∈ S) ∧ (∀ z ∈ S, M.toBlocks₂₂ *ᵥ z ∈ S) := by
  have eL : ∀ z : Fin d → R, (Sum.elim z 0 : Fin d ⊕ Fin d → R) ∘ Sum.inl = z := fun z => rfl
  have eR : ∀ z : Fin d → R, (Sum.elim z 0 : Fin d ⊕ Fin d → R) ∘ Sum.inr = 0 := fun z => rfl
  have fL : ∀ z : Fin d → R, (Sum.elim 0 z : Fin d ⊕ Fin d → R) ∘ Sum.inl = 0 := fun z => rfl
  have fR : ∀ z : Fin d → R, (Sum.elim 0 z : Fin d ⊕ Fin d → R) ∘ Sum.inr = z := fun z => rfl
  have a11 : ∀ z : Fin d → R, (M *ᵥ Sum.elim z 0) ∘ Sum.inl = M.toBlocks₁₁ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  have a21 : ∀ z : Fin d → R, (M *ᵥ Sum.elim z 0) ∘ Sum.inr = M.toBlocks₂₁ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁]
  have a12 : ∀ z : Fin d → R, (M *ᵥ Sum.elim 0 z) ∘ Sum.inl = M.toBlocks₁₂ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₂]
  have a22 : ∀ z : Fin d → R, (M *ᵥ Sum.elim 0 z) ∘ Sum.inr = M.toBlocks₂₂ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have := (h (Sum.elim z 0) (by rw [eL]; exact hz) (by rw [eR]; exact S.zero_mem)).1
    rwa [a11] at this
  · have := (h (Sum.elim 0 z) (by rw [fL]; exact S.zero_mem) (by rw [fR]; exact hz)).1
    rwa [a12] at this
  · have := (h (Sum.elim z 0) (by rw [eL]; exact hz) (by rw [eR]; exact S.zero_mem)).2
    rwa [a21] at this
  · have := (h (Sum.elim 0 z) (by rw [fL]; exact S.zero_mem) (by rw [fR]; exact hz)).2
    rwa [a22] at this

end GlobalTheory.DblVac.BlocksPreserved

namespace GlobalTheory.DblVac

theorem KD_blocks_keep : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro F E _ _ _ _ _ σ d W v g hg
  have h1 := BlocksPreserved.blocks_keep (GlobalTheory.InertSph.latAt W v) (matD g)
    (fun z h1 h2 => (hg.2 z ⟨h1, h2⟩).1)
  have h2 := BlocksPreserved.blocks_keep (GlobalTheory.InertSph.latAt W v) (matD g⁻¹)
    (fun z h1 h2 => (hg.2 z ⟨h1, h2⟩).2)
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

end GlobalTheory.DblVac
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open scoped Matrix Classical

namespace GlobalTheory.ArchLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}


open Classical in
def archOp (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d)) : SInf F (Fin n × Fin d) :=
  if hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁ then hx.choose else 0

def archAct (M : Model σ X W) (h : UA σ W.J)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  coordI M (actAB (cA σ) ((1 : UA σ X.J), h) (M.co.e.symm (liftV v.1, liftV v.2)))

theorem acts_archOp (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d))
    (hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁) :
    Acts (evI F) (om (1, h)) ⇑f ⇑(archOp om h f) := by
  classical
  unfold archOp
  rw [dite_eq_left hx]
  exact hx.choose_spec

theorem archAct_one (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    archAct M 1 v = v := by
  unfold archAct
  simp [actAB, coordI_lift]

end GlobalTheory.ArchLine
end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem sumOp_vec_zero {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) : sumOp W A B 0 = 0 := by
  unfold sumOp; simp

theorem form_translate_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) {Λ : Submodule R X}
    (hΛ : SelfDual γ Λ) {s : M} (hs : Fixes W Λ s) (e : M →ₗ[ℂ] ℂ) (he : ∀ a ∈ Λ, ∀ v, e (W a v) = e v) (x : X) :
    e (W x s) = if x ∈ Λ then e s else 0 := by
  split_ifs with hx
  · rw [hs x hx]
  · obtain ⟨a, ha, hne⟩ : ∃ a ∈ Λ, γ x a ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hx ((hΛ x).2 hc)
    have h1 : e (W x s) = γ a x * e (W x s) := by
      conv_lhs => rw [← he a ha (W x s)]
      rw [h.comm a x s, hs a ha, map_smul, smul_eq_mul]
    have h2 : γ a x ≠ 1 := by
      rw [h.swap x a]
      intro h3
      exact hne (inv_eq_one.1 h3)
    have h3 : (1 - γ a x) * e (W x s) = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm h2))

theorem sumOp_vacuum_lift : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs0 hs hspan Λ' hΛ' hidx
  obtain ⟨hidx', hss⟩ := sumOp_sumOp_eq_idx_smul h Λ Λ' hΛ hΛ' hidx
  obtain ⟨⟨n, f, hf, ht⟩, hfix, -⟩ := (sumOp_transversal h Λ Λ' hΛ').2.1 hidx
  have hs'fix : Fixes W Λ' (sumOp W Λ Λ' s) := hfix s hs
  have hback := hss s hs
  have hidxC : (idx Λ Λ' : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hne : sumOp W Λ Λ' s ≠ 0 := by
    intro h0
    rw [h0, sumOp_vec_zero] at hback
    exact hs0 ((smul_eq_zero.1 hback.symm).resolve_left hidxC)
  have hidx2 : idx Λ' Λ ≠ 0 := by rw [hidx']; exact hidx
  obtain ⟨⟨m, g, hg, hgt⟩, -, -⟩ := (sumOp_transversal h Λ' Λ hΛ).2.1 hidx2
  have hsum := ((sumOp_transversal h Λ' Λ hΛ).1 _ hs'fix (Fin m) g hg hgt).1
  have hsE : s = ((idx Λ Λ' : ℂ))⁻¹ • ∑ i, W (g i) (sumOp W Λ Λ' s) := by
    rw [← hsum, hback, smul_smul, inv_mul_cancel₀ hidxC, one_smul]
  have hmem : ∀ x, W x s ∈ Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) := by
    intro x

    rw [congrArg (W x) hsE, map_smul, map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [h.comp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hspan' : Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmem x
  refine ⟨⟨hne, hs'fix, hspan'⟩, fun e he1 he v hv => ?_⟩
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergVacuum_unique_of_selfDual h Λ' hΛ' _ hne hs'fix hspan' v hv
  have hes' : e (sumOp W Λ Λ' s) = 1 := by

    rw [((sumOp_transversal h Λ Λ' hΛ').1 s hs (Fin n) f hf ht).1, map_sum]
    simp only [form_translate_vacuum h hΛ hs e he, he1]
    obtain ⟨i0, hi0, huniq⟩ := ht 0 Λ'.zero_mem
    rw [Finset.sum_eq_single i0]
    · rw [if_pos (by simpa using hi0)]
    · intro j _ hj
      rw [if_neg]
      intro hjΛ
      exact hj (huniq j (by simpa using hjΛ))
    · simp
  rw [map_smul, hes', smul_eq_mul, mul_one]

end GlobalTheory.SphTheta
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.discreteSeries_pureInnerProducts_tensorProduct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), TensorLaw M := by
  first | exact @GlobalTheory.Chain.RealIt.tensorLaw | exact GlobalTheory.Chain.RealIt.tensorLaw | (intros; apply GlobalTheory.Chain.RealIt.tensorLaw <;> assumption)
end
