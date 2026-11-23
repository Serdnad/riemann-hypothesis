module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle001
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.HasDerivAtExp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle003

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace ConjugateTransportSingles

variable {k r : ℕ}

theorem inv_conj (P G : Mat k r) (hP : IsUnit P.det) : (P * G * P⁻¹)⁻¹ = P * G⁻¹ * P⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP, Matrix.mul_assoc]

theorem cJd_transport (P : Mat k r) (hP : IsUnit P.det) (x1 β : Fin (2 * r + k + 1) → ℂ) (G : Mat k r) :
    cJd (P *ᵥ x1) β (P * G * P⁻¹) = (β ᵥ* P) ⬝ᵥ (G⁻¹ *ᵥ x1) := by
  unfold cJd
  rw [inv_conj P G hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ P⁻¹ P,
    Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec, Matrix.dotProduct_mulVec]

theorem cJd_sinv (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (β : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r) (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z)
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    cJd (xJ P z) β (P * (s * x) * P⁻¹) = cJd (xJ P z) β (P * x * P⁻¹) := by
  unfold xJ
  rw [cJd_transport P hP, cJd_transport P hP]
  exact ((mult k r z hz).1 (0 : Fin (2 * r + k + 1) → ℂ) (β ᵥ* P) s hs x hx).2

theorem cJd_single (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (d : Fin (2 * r + k + 1))
    (x : Mat k r) :
    cJd (xJ P z) (Pi.single d 1) (P * x * P⁻¹) = (P *ᵥ (x⁻¹ *ᵥ xOne k r z)) d := by
  unfold xJ
  rw [cJd_transport P hP, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, Pi.single_apply]

theorem tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H) (G : Mat k r) :
    tMapD σ x1 x₀ w (Pi.single d m) G = cJd x1 (Pi.single d 1) G * coefX σ x₀ w m G := by
  unfold tMapD
  rw [Finset.sum_eq_single d]
  · simp
  · intro c _ hc
    delta coefX
    simp only [Pi.single_eq_of_ne hc, map_zero, inner_zero_right, mul_zero]
  · simp

theorem tMapD_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H) (G : Mat k r) :
    tMapD σ x1 x₀ w f G = ∑ d, tMapD σ x1 x₀ w (Pi.single d (f d)) G := by
  rw [Finset.sum_congr rfl fun d _ => tMapD_single σ x1 x₀ w d (f d) G]
  rfl

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem perI_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    CapelliMinorRestriction.perI P ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =ᵐ[μW.prod μN]
      fun p => (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • CapelliMinorRestriction.perI P ψ π (coefX σ x₀ w m) ξ g p := by
  filter_upwards [CapelliMinorRestriction.ae_S hW hN] with p hp
  delta CapelliMinorRestriction.perI
  rw [tMapD_single, cJd_sinv P hP z hz _ _ g hp hg, cJd_single P hP, mul_smul]

theorem per_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =
      (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • per P μW μN ψ π (coefX σ x₀ w m) ξ g := by
  rw [CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, ← integral_smul]
  exact integral_congr_ae (perI_tMapD_single σ z hz P hP μW μN hW hN ψ π x₀ w d m ξ g hg)

end ConjugateTransportSingles

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TransportMapLinear

open ReciprocityTheory.ChartRestriction.DS

section Cls

variable {n : ℕ}

theorem toL2_congr_on_unitary_bis (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, F g = G g) : toL2 ε F = toL2 ε G := by
  have e : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) :=
    funext fun g => h _ (unitary_matrix_mem_set ε g)
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := e ▸ hF
    rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG, MemLp.toLp_eq_toLp_iff]
    exact Filter.EventuallyEq.of_eq e
  · have hG : ¬ MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := e ▸ hF
    rw [toL2_eq_zero_of_not_memLp ε hF, toL2_eq_zero_of_not_memLp ε hG]

theorem exists_lin {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ Y) (G : Submodule ℂ Y)
    (L : Y →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (hsm : ∀ f ∈ G, IsSmoothL2 ε (L f))
    (hG : ∀ a b, ∀ f ∈ G, A a b f ∈ G)
    (hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (A a b f) g) :
    ∃ T : Y →ₗ[ℂ] smD ε (rreg ε), (∀ f ∈ G, (T f : L2 ε) = toL2 ε (L f)) ∧
      ∀ a b, ∀ f ∈ G, T (A a b f) = smE ε (rreg ε) a b (T f) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl G
  let p := G.projectionOnto q hq
  have hpG : ∀ f ∈ G, ((p f : G) : Y) = f := fun f hf => by
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨f, hf⟩)
  have hmem : ∀ f : Y, toL2 ε (L (p f)) ∈ smD ε (rreg ε) := fun f => toL2_mem_smD_of_isSmoothL2 (hsm _ (p f).2)
  have hL2 : ∀ f : Y, MemLp (fun g : Formalism.REAL.UJ ε => L (p f) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    fun f => (hsm _ (p f).2).2 []
  let T : Y →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun f => ⟨toL2 ε (L (p f)), hmem f⟩
      map_add' := fun f g => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [map_add (f := _), Submodule.coe_add, map_add (f := _)]
        exact toL2_add_smooth ε (hL2 f) (hL2 g)
      map_smul' := fun c f => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [map_smul, Submodule.coe_smul, map_smul]
        exact toL2_smul_smooth ε c _ }
  have hT : ∀ f ∈ G, (T f : L2 ε) = toL2 ε (L f) := fun f hf => by
    show toL2 ε (L (p f)) = _
    rw [hpG f hf]
  refine ⟨T, hT, fun a b f hf => ?_⟩
  have e1 : T f = ⟨toL2 ε (L f), toL2_mem_smD_of_isSmoothL2 (hsm f hf)⟩ := Subtype.ext (hT f hf)
  apply Subtype.ext
  rw [hT _ (hG a b f hf), e1, rightDerivative_toL2 (hsm f hf) a b]
  exact toL2_congr_on_unitary_bis ε fun g hg => (hder f hf a b g hg).symm

end Cls

section Lin

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tMapDL (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : H) :
    (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMapD σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f g := by
    funext x
    simp only [tMapD, coefX, Pi.add_apply, Submodule.coe_add, map_add (f := _), inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [tMapD, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

end Lin

section Line

universe u

variable {n : ℕ} {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem line (hU : IsKUnitary ε E) (X : Submodule ℂ (Fin n → D)) (Λ : Fin n → ℝ)
    (hXk : ∀ y ∈ X, ∃ S : Submodule ℂ (Fin n → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensVd E) S ∧ y ∈ S)
    (hK2 : ∀ f₁ f₂ : Fin n → D, f₁ ∈ X → f₂ ∈ X → IsKHWVec ε (LemK.tensVd E) Λ f₁ →
      IsKHWVec ε (LemK.tensVd E) Λ f₂ → ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0) :
    ∃ ys ∈ X, ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y] (B : Fin n → Fin n → Module.End ℂ Y)
      (ψ : (Fin n → D) →ₗ[ℂ] Y), (∀ a b, ε a = ε b → ∀ x ∈ X, ψ (LemK.tensVd E a b x) = B a b (ψ x)) →
      ∀ y ∈ X.map ψ, IsKHWVec ε B Λ y → ∃ c : ℂ, y = c • ψ ys := by
  classical

  have hlift : ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y] (B : Fin n → Fin n → Module.End ℂ Y)
      (ψ : (Fin n → D) →ₗ[ℂ] Y), (∀ a b, ε a = ε b → ∀ x ∈ X, ψ (LemK.tensVd E a b x) = B a b (ψ x)) →
      ∀ y ∈ X.map ψ, IsKHWVec ε B Λ y → ∃ x ∈ X, IsKHWVec ε (LemK.tensVd E) Λ x ∧ ψ x = y := by
    intro Y _ _ B ψ hψ y hy hyK
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨S, hSX, hfd, hSk, hx₀S⟩ := hXk x₀ hx₀
    obtain ⟨x, hxS, hxK, hx⟩ := LemK.exists_highest_weight_lift_pi hU ψ hfd hSk
      (fun a b hab z hz => hψ a b hab z (hSX hz)) hx₀S hyK
    exact ⟨x, hSX hxS, hxK, hx⟩
  by_cases hex : ∃ ys ∈ X, ys ≠ 0 ∧ IsKHWVec ε (LemK.tensVd E) Λ ys
  · obtain ⟨ys, hys, hys0, hysK⟩ := hex
    refine ⟨ys, hys, fun Y _ _ B ψ hψ y hy hyK => ?_⟩
    obtain ⟨x, hx, hxK, rfl⟩ := hlift Y B ψ hψ y hy hyK
    obtain ⟨c₁, c₂, hc, hsum⟩ := hK2 x ys hx hys hxK hysK
    by_cases h1 : c₁ = 0
    · exfalso
      have h2 : c₂ ≠ 0 := hc.resolve_left (not_not.2 h1)
      rw [h1, zero_smul, zero_add] at hsum
      exact hys0 ((smul_eq_zero.1 hsum).resolve_left h2)
    · refine ⟨-(c₂ / c₁), ?_⟩
      have : x = -(c₂ / c₁) • ys := by
        have h3 : c₁ • x = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hsum
        calc x = c₁⁻¹ • (c₁ • x) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
          _ = -(c₂ / c₁) • ys := by rw [h3, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [this, map_smul]
  · refine ⟨0, zero_mem _, fun Y _ _ B ψ hψ y hy hyK => ?_⟩
    obtain ⟨x, hx, hxK, rfl⟩ := hlift Y B ψ hψ y hy hyK
    have : x = 0 := by
      by_contra h0
      exact hex ⟨x, hx, h0, hxK⟩
    exact ⟨0, by rw [this, map_zero, zero_smul]⟩

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.TransportMapLinear
end
end
