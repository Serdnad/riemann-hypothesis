module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle004
import GroundTheory.AutomorphicForms.TensorProductTheorem.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.L1
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

def TermE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ k n : ℕ, Module.finrank F E = k + 1 → 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
      (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (m : ∀ u : Pl E, Measure (Gw n u)),
      (∀ u, (m u).IsHaarMeasure) →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
      (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v, RankOne μ V u.1 (T.J u.1) (T.χ u.1)) →
    ∀ (τ₀ : SmIrr (Gw n w₀.1)) (τ : ∀ v : Pl F, SmIrr (Gw n (T.mk' v).1)), Occurs μ V w₀.1 τ₀ →
      (∀ v ∈ T.sp, Occurs μ V (T.mk' v).1 (τ v)) → ∀ y : ℝ, 0 < y →
      ∃ c : ℂ, (T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ → c ≠ 0) ∧
        ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
        ∀ (e : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), Antitone e → GM.IsSideE L νE aE e 𝔢 →
        ∀ (j : ℕ) (sq : ℂ) (t : Pl F → ℂ), HasTrace (m w₀.1) τ₀.ρ ((GM.iwCoset w₀.1 (j • e)).indicator 1) sq →
          (∀ v ∈ T.sp, HasTrace (m (T.mk' v).1) (τ v).ρ (ψ v) (t v)) →
          trOn (eigIn V 𝔢.toAmp.A (y ^ (k + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) = c * sq * ∏ v ∈ T.sp, t v

end UpperTheory.ConvolutionTheory.C
end
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q}

def nsS (T : Ty σ n q w₀) : Finset (Pl F) := T.S.filter fun v => ¬ GM.Split E v

def offN (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (T : Ty σ n q w₀) : Submodule ℂ (LL μ) :=
  ⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ (nsS T : Set (Pl F))), eigL μ w (T.J w) (T.χ w)

def lvN (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) (v : Pl F) : Subgroup (Gw n (T.mk' v).1) :=
  (L.UE v).map (GM.cmp (T.mk' v))

end

def kerChr {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) (χ : G → ℂ) (h : IsChr J χ) : Subgroup G where
  carrier := {x | x ∈ J ∧ χ x = 1}
  one_mem' := by
    have h1 := h.2.2 1 J.one_mem 1 J.one_mem
    have h2 : χ 1 ≠ 0 := fun h0 => by
      have := h.2.1 1 J.one_mem
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    rw [mul_one] at h1
    exact ⟨J.one_mem, mul_left_cancel₀ h2 (by rw [← h1, mul_one])⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨J.mul_mem ha hb, by rw [h.2.2 a ha b hb, ha', hb', one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 := h.2.2 1 J.one_mem 1 J.one_mem
    have h2 : χ 1 ≠ 0 := fun h0 => by
      have := h.2.1 1 J.one_mem
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    rw [mul_one] at h1
    have h3 : χ 1 = 1 := mul_left_cancel₀ h2 (by rw [← h1, mul_one])
    refine ⟨J.inv_mem ha, ?_⟩
    have h4 := h.2.2 a ha a⁻¹ (J.inv_mem ha)
    rwa [mul_inv_cancel, h3, ha', one_mul, eq_comm] at h4

end UpperTheory.ConvolutionTheory.C
end
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.L1
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

def HasTwTrace {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (m : Measure G) (τ : SmIrr G)
    (I : τ.V ≃ₗ[ℂ] τ.V) (φ : G → ℂ) (t : ℂ) : Prop :=
  ∃ B : τ.V →ₗ[ℂ] τ.V, IsIntegralOp m τ.ρ φ B ∧ HasFinTrace (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) t

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsLocGal (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (s : Gw n w.1 →* Gw n w.1) : Prop :=
  ∀ g : GL (Fin n) (CompletionsOver E v), GM.cmp w (mapGL n (galFin σ v) g) = s (GM.cmp w g)

structure FitsV {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q} (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀)
    (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ) : Prop where
  S_eq : L.S = T.S
  test : ∀ v ∈ T.S, Test (ψ v)
  inv : ∀ v ∈ T.sp, ∀ u ∈ T.J (T.mk' v).1, ∀ g, ψ v (u * g) = ψ v g ∧ ψ v (g * u) = ψ v g
  split : ∀ v ∈ T.sp, L.φ v = GM.prodFn (Function.update
      (fun u : PlacesOver E v => ((T.J u.1 : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) (T.mk' v) (ψ v)) ∧
    ∀ g, g ∈ L.UE v ↔ ∀ u, GM.cmp u g ∈ T.J u.1
  nonsplit : ∀ v ∈ T.S, ¬ GM.Split E v → ∀ g, L.φ v g = ψ v (GM.cmp (T.mk' v) g)

end

def TwistFactor : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V Z : Submodule ℂ (LL μ))
    (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
    (τ : ∀ i, SmIrr (Gw n (w i))) (s : ∀ i, Gw n (w i) ≃ₜ* Gw n (w i)) (I : ∀ i, (τ i).V ≃ₗ[ℂ] (τ i).V) (R : LL μ →L[ℂ] LL μ),
    IsSummand μ V → Function.Injective w → (∀ i, Occurs μ V (w i) (τ i)) →
    Z ≤ V → IsClosed (Z : Set (LL μ)) → (∀ i g, ∀ v ∈ Z, rhoL μ (w i) g v ∈ Z) →
    (∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixL μ (w i) (U i))) →
    (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (rhoL μ (w i) g v) = rhoL μ (w i) (s i g) (R v)) →
    (∀ i g x, I i ((τ i).ρ g x) = (τ i).ρ (s i g) (I i x)) →
    ∃ c : ℂ, ∀ (U : ∀ i, Subgroup (Gw n (w i))) (m : ∀ i, Measure (Gw n (w i))) (φ : ∀ i, Gw n (w i) → ℂ)
      (T : Fin r → LL μ →L[ℂ] LL μ) (t : Fin r → ℂ), (∀ i, CO (U i)) → (∀ i, (m i).IsHaarMeasure) → (∀ i, Test (φ i)) →
      (∀ i, ∀ u ∈ U i, ∀ g, φ i (u * g) = φ i g) → (∀ i, IsOloc μ (w i) (m i) (φ i) (T i)) →
      (∀ i, HasTwTrace (m i) (τ i) (I i) (φ i) (t i)) →
      trOn (Z ⊓ ⨅ i, fixL μ (w i) (U i)) ((List.ofFn T).prod ∘L R) = c * ∏ i, t i

def LocGalEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (Module.finrank F E).Prime → ∀ (n : ℕ) (v : Pl F) (w : PlacesOver E v), ¬ GM.Split E v →
    (∀ u : PlacesOver E v, u = w) ∧ ∃ s : Gw n w.1 ≃ₜ* Gw n w.1, IsLocGal σ w (s : Gw n w.1 →* Gw n w.1) ∧
      ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        (∀ g x, θ.U (rhoL μ w.1 g x) = rhoL μ w.1 (s g) (θ.U x)) ∧
        ∀ (V : Submodule ℂ (LL μ)) (τ : SmIrr (Gw n w.1)), IsSummand μ V → V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
          Occurs μ V w.1 τ → ∃ I : τ.V ≃ₗ[ℂ] τ.V, ∀ g x, I (τ.ρ g x) = τ.ρ (s g) (I x)

def TermEV : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ k n : ℕ, Module.finrank F E = k + 1 → (k + 1).Prime → 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
    ∀ (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
      (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (m : ∀ u : Pl E, Measure (Gw n u)),
      (∀ u, (m u).IsHaarMeasure) →
    ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V →
      (∀ v ∈ T.S, ¬ GM.Split E v → ∀ u : PlacesOver E v,
        RankOne μ V u.1 (T.J u.1) (T.χ u.1) ∧ V ⊓ eigL μ u.1 (T.J u.1) (T.χ u.1) ≠ ⊥) →
    ∀ (τ₀ : SmIrr (Gw n w₀.1)) (τ : ∀ v : Pl F, SmIrr (Gw n (T.mk' v).1)) (g : ∀ v : Pl F, Gw n (T.mk' v).1 →* Gw n (T.mk' v).1)
      (I : ∀ v : Pl F, (τ v).V ≃ₗ[ℂ] (τ v).V), Occurs μ V w₀.1 τ₀ → (∀ v ∈ T.S, Occurs μ V (T.mk' v).1 (τ v)) →
      (∀ v ∈ T.S, ¬ GM.Split E v → IsLocGal σ (T.mk' v) (g v) ∧ ∀ x y, I v ((τ v).ρ x y) = (τ v).ρ (g v x) (I v y)) →
      ∀ y : ℝ, 0 < y →
      ∃ c : ℂ, (T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ → c ≠ 0) ∧
        ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), FitsV T L ψ →
        ∀ (e : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), Antitone e → GM.IsSideE L νE aE e 𝔢 →
        ∀ (j : ℕ) (sq : ℂ) (t : Pl F → ℂ), HasTrace (m w₀.1) τ₀.ρ ((GM.iwCoset w₀.1 (j • e)).indicator 1) sq →
          (∀ v ∈ T.sp, HasTrace (m (T.mk' v).1) (τ v).ρ (ψ v) (t v)) →
          (∀ v ∈ T.S, ¬ GM.Split E v → HasTwTrace (m (T.mk' v).1) (τ v) (I v) (ψ v) (t v)) →
          trOn (eigIn V 𝔢.toAmp.A (y ^ (k + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) = c * sq * ∏ v ∈ T.S, t v

end UpperTheory.ConvolutionTheory.C
end
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped RestrictedProduct Topology Classical

namespace UpperTheory.ConvolutionTheory.C

section SlopeTestRemainingChoices

private theorem mem_of_finite_places {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {A : ∀ v, Subgroup (G v)}
    (H : Subgroup (Πʳ v, [G v, A v])) (L C : ∀ v, Subgroup (G v))
    (hL : ∀ v, ∀ x ∈ L v, RestrictedTensor.singleHom A v x ∈ H)
    (base : ∀ h : Πʳ v, [G v, A v], (∀ v, h v ∈ L v) → (∀ v, h v ∈ C v) → h ∈ H)
    (T : Finset ι) : ∀ h : Πʳ v, [G v, A v], (∀ v, h v ∈ L v) → (∀ v ∉ T, h v ∈ C v) → h ∈ H := by
  induction T using Finset.induction_on with
  | empty => exact fun h h1 h2 => base h h1 fun v => h2 v (Finset.notMem_empty v)
  | insert a s has ih =>
    intro h h1 h2
    rw [← RestrictedTensor.single_mul_eraseAt a h]
    refine H.mul_mem (hL a _ (h1 a)) (ih _ (fun v => ?_) (fun v hv => ?_))
    · by_cases hva : v = a
      · subst hva; rw [RestrictedTensor.eraseAt_apply_self]; exact one_mem _
      · rw [RestrictedTensor.eraseAt_apply_of_ne _ hva]; exact h1 v
    · by_cases hva : v = a
      · subst hva; rw [RestrictedTensor.eraseAt_apply_self]; exact one_mem _
      · rw [RestrictedTensor.eraseAt_apply_of_ne _ hva]; exact h2 v (by simp [hva, hv])

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem rhoF_mul (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (a b : AdelicGLn.FiniteAdelicGL K n) (x : LL μ) :
    rhoF μ (a * b) x = rhoF μ a (rhoF μ b x) := by
  simp only [rhoF, _root_.map_mul]
  exact UnitaryRep.map_mul_apply _ _ _ _

private theorem rhoF_one (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (x : LL μ) : rhoF μ 1 x = x := by
  simp only [rhoF, _root_.map_one]
  exact UnitaryRep.map_one_apply _ _

private def stab (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (x : LL μ) : Subgroup (AdelicGLn.FiniteAdelicGL K n) where
  carrier := {g | rhoF μ g x = x}
  one_mem' := rhoF_one μ x
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [rhoF_mul, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← rhoF_mul, inv_mul_cancel, rhoF_one]

private theorem isClosed_stab (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (x : LL μ) :
    IsClosed (stab μ x : Set (AdelicGLn.FiniteAdelicGL K n)) :=
  isClosed_eq (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).continuous_orbit x).comp MultiplicityOne.continuous_finProj)
    continuous_const

private theorem mem_fixF (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (W : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (x : LL μ) :
    x ∈ fixF μ W ↔ ∀ u ∈ W, rhoF μ u x = x := by
  simp [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem mem_fixL (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w)) (x : LL μ) :
    x ∈ fixL μ w J ↔ ∀ g ∈ J, rhoF μ (AdelicGLn.localEmbedding w g) x = x := by
  simp [fixL, mem_fixF]

private theorem finAt_finEmb' (h : AdelicGLn.FiniteAdelicGL K n) (v : Pl K) :
    finAt v (finEmb K n h) = AdelicGLn.finiteRestrictedEquiv K n h v := by
  show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n h)).2) v = _
  rw [prodEquiv_finEmb]

private theorem equiv_localEmbedding (w : Pl K) (g : Gw n w) :
    AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.localEmbedding w g) =
      RestrictedTensor.singleHom (fun v : Pl K => GLnLocal.integralGL (v.adicCompletion K) n) w g :=
  ContinuousMulEquiv.apply_symm_apply _ _

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.fixLev :
    UpperTheory.ConvolutionTheory.C.FixLev := by
  intro K _ _ n μ _ P U
  let e := AdelicGLn.finiteRestrictedEquiv K n
  let I : ∀ v : Pl K, Subgroup (Gw n v) := fun v => GLnLocal.integralGL (v.adicCompletion K) n
  let lev : ∀ v : Pl K, Subgroup (Gw n v) := fun v => if v ∈ P then U v else I v
  have hmem : ∀ h, h ∈ levOn P U ↔ ∀ v, e h v ∈ lev v := fun h => by
    show (∀ v, finAt v (finEmb K n h) ∈ _) ↔ _
    simp only [finAt_finEmb']
    rfl
  have hloc : ∀ (v : Pl K) (g : Gw n v), g ∈ lev v → AdelicGLn.localEmbedding v g ∈ levOn P U := fun v g hg => by
    refine (hmem _).2 fun w => ?_
    show e (AdelicGLn.localEmbedding v g) w ∈ lev w
    rw [equiv_localEmbedding]
    by_cases hw : w = v
    · subst hw; rw [RestrictedTensor.singleHom_apply_self]; exact hg
    · rw [RestrictedTensor.singleHom_apply_of_ne _ hw]; exact one_mem _
  apply le_antisymm
  · intro x hx
    rw [mem_fixF] at hx
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
      refine (mem_fixL μ v _ x).2 fun g hg => hx _ (hloc v g ?_)
      simpa [lev, hv, I] using hg
    · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
      refine (mem_fixL μ v _ x).2 fun g hg => hx _ (hloc v g ?_)
      simpa [lev, hv] using hg
  · intro x hx
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
    have hfix : ∀ (v : Pl K) (g : Gw n v), g ∈ lev v → rhoF μ (AdelicGLn.localEmbedding v g) x = x := fun v g hg => by
      by_cases hv : v ∈ P
      · have := (Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 h2 v) hv)
        exact (mem_fixL μ v _ x).1 this g (by simpa [lev, hv] using hg)
      · have := (Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 h1 v) hv)
        exact (mem_fixL μ v _ x).1 this g (by simpa [lev, hv, I] using hg)
    let H : Subgroup (Πʳ v : Pl K, [Gw n v, I v]) := (stab μ x).comap e.symm.toMulEquiv.toMonoidHom
    have hHc : IsClosed (H : Set (Πʳ v : Pl K, [Gw n v, I v])) := (isClosed_stab μ x).preimage e.symm.continuous
    have hL : ∀ v, ∀ g ∈ lev v, RestrictedTensor.singleHom I v g ∈ H := fun v g hg => by
      show rhoF μ (e.symm _) x = x
      have : e.symm (RestrictedTensor.singleHom I v g) = AdelicGLn.localEmbedding v g := by
        rw [ContinuousMulEquiv.symm_apply_eq]
        exact (equiv_localEmbedding v g).symm
      rw [this]
      exact hfix v g hg
    have hfin := mem_of_finite_places H lev (fun _ => ⊥) hL (fun h _ hb => by
      have : h = 1 := DFunLike.ext _ _ fun v => Subgroup.mem_bot.1 (hb v)
      rw [this]; exact one_mem _)
    have hint := mem_of_finite_places H lev I hL (fun h ha hb => by
      let x0 : ∀ v : Pl K, (I v : Set (Gw n v)) := fun v => ⟨h v, hb v⟩
      let y : Finset (Pl K) → ∀ v : Pl K, (I v : Set (Gw n v)) := fun S v => if v ∈ S then x0 v else ⟨1, one_mem _⟩
      let f : (∀ v : Pl K, (I v : Set (Gw n v))) → Πʳ v : Pl K, [Gw n v, I v] := RestrictedProduct.structureMap _ _ Filter.cofinite
      have hf : Continuous f := RestrictedProduct.isEmbedding_structureMap.continuous
      have hy : Tendsto y atTop (𝓝 x0) := tendsto_pi_nhds.2 fun v =>
        tendsto_const_nhds.congr' ((eventually_ge_atTop ({v} : Finset (Pl K))).mono fun S hS => by
          have : v ∈ S := hS (Finset.mem_singleton_self v)
          simp [y, this])
      have hlim := (hf.tendsto x0).comp hy
      have hx0 : f x0 = h := DFunLike.ext _ _ fun v => rfl
      rw [hx0] at hlim
      refine hHc.mem_of_tendsto hlim (Eventually.of_forall fun S => ?_)
      refine hfin S _ (fun v => ?_) (fun v hv => ?_)
      · by_cases hv : v ∈ S
        · show ((y S v : _) : Gw n v) ∈ lev v
          simp only [y, hv, if_true]; exact ha v
        · show ((y S v : _) : Gw n v) ∈ lev v
          simp only [y, hv, if_false]; exact one_mem _
      · show ((y S v : _) : Gw n v) ∈ (⊥ : Subgroup (Gw n v))
        simp only [y, hv, if_false]; exact one_mem _) P
    refine (mem_fixF μ _ x).2 fun u hu => ?_
    have := hint (e u) ((hmem u).1 hu) (fun v hv => by
      have := (hmem u).1 hu v
      simpa [lev, hv] using this)
    show u ∈ stab μ x
    have h3 : e.symm (e u) ∈ stab μ x := this
    simpa using h3
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.occursIff
    (K : Type) [Field K] [NumberField K] (n : ℕ)
    (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) (σ : SmIrr (Gw n w)) :
    Occurs μ V w σ ↔ ∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (σ.ρ g x) = Dp.locOn hV w g (f x) := by
  constructor
  · rintro ⟨f, hf0, hfV, hf⟩
    refine ⟨f.codRestrict V hfV, ?_, ?_⟩
    · intro h
      apply hf0
      exact LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun h x)
    · intro g x
      apply Subtype.ext
      change f (σ.ρ g x) = Dp.localRepresentationL2 μ w g (f x)
      rw [← Dp.rhoLoc K n μ w g (f x)]
      exact hf g x
  · rintro ⟨f, hf0, hf⟩
    refine ⟨V.subtype ∘ₗ f, ?_, fun x => (f x).2, ?_⟩
    · intro h
      apply hf0
      exact LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h x)
    · intro g x
      change (f (σ.ρ g x) : LL μ) = rhoL μ w g (f x)
      rw [Dp.rhoLoc K n μ w g]
      exact congrArg Subtype.val (hf g x)
end
