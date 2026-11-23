module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TorusFrame

open NumberField Matrix Complex GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem angles_add (φ ψ : Fin (r - 1) → ℝ) (a : Fin r) : angles (φ + ψ) a = angles φ a + angles ψ a := by
  unfold angles; split_ifs <;> simp [Finset.sum_add_distrib]; ring

theorem angles_smul (c : ℝ) (φ : Fin (r - 1) → ℝ) (a : Fin r) : angles (c • φ) a = c * angles φ a := by
  unfold angles; split_ifs <;> simp [Finset.mul_sum]

theorem angles_zero (a : Fin r) : angles (0 : Fin (r - 1) → ℝ) a = 0 := by
  unfold angles; split_ifs <;> simp

def anglesL (r : ℕ) : (Fin (r - 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun φ a := angles φ a
  map_add' φ ψ := funext fun a => angles_add φ ψ a
  map_smul' c φ := funext fun a => angles_smul c φ a

theorem continuous_angles (a : Fin r) : Continuous fun φ : Fin (r - 1) → ℝ => angles φ a :=
  ((continuous_apply a).comp (LinearMap.continuous_of_finiteDimensional (anglesL r)) :)

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem isUnit_det_of_isOrth {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    IsUnit (mat x τ).det := by
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq, det_mul, det_mul, det_transpose, det_diagonal] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_mul, zero_mul] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn; split_ifs <;> norm_num

def frameU {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : GL (Fin r) ℂ :=
  nonsingInvUnit (mat x τ) (isUnit_det_of_isOrth hx τ)

def phaseU (φ : Fin (r - 1) → ℝ) : GL (Fin r) ℂ where
  val := diagonal fun a => exp (I * (angles φ a : ℂ))
  inv := diagonal fun a => exp (-(I * (angles φ a : ℂ)))
  val_inv := by rw [diagonal_mul_diagonal]; simp [← exp_add]
  inv_val := by rw [diagonal_mul_diagonal]; simp [← exp_add]

def torusGL {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => frameU hx τ * phaseU (θ τ) * (frameU hx τ)⁻¹

theorem torusGL_val {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ) (τ : X.Ψ) :
    ((torusGL hx θ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => exp (I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ := rfl

def torusDerL {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin (r - 1) → ℝ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) where
  toFun θ τ a b := (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) a b
  map_add' θ θ' := by
    funext τ a b
    simp only [Pi.add_apply, angles_add, ofReal_add, mul_add, ← diagonal_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c θ := by
    funext τ a b
    have : (diagonal fun d => I * (angles (c • θ τ) d : ℂ)) = (c : ℂ) • diagonal fun d => I * (angles (θ τ) d : ℂ) := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h, angles_smul]; ring
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

def torusDer {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin (r - 1) → ℝ) →L[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
  LinearMap.toContinuousLinearMap (torusDerL x)

theorem torusDer_apply {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (θ : Ψ → Fin (r - 1) → ℝ) (τ : Ψ) (a b : Fin r) :
    torusDer x θ τ a b = (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) a b := rfl

end GlobalTheory.TorusFrame
end
end

section

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
open scoped Topology

noncomputable section

namespace GlobalTheory.UnipCoefInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (a b : ℕ) (s : kˣ) : Set (Fin a → Fin b → k) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ => cball s

theorem mem_box {a b : ℕ} {s : kˣ} {X : Fin a → Fin b → k} :
    X ∈ box a b s ↔ ∀ p q, X p q ∈ cball s := by
  simp [box, Set.mem_univ_pi]

theorem isOpen_box (a b : ℕ) (s : kˣ) : IsOpen (box a b s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s

theorem isCompact_box (a b : ℕ) (s : kˣ) : IsCompact (box a b s) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s

theorem box_mono {a b : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    box a b s ⊆ box a b t := by
  intro X hX
  rw [mem_box] at hX ⊢
  intro p q
  exact le_trans (show valuation k (X p q) ≤ valuation k (s : k) from hX p q) h

theorem add_mem_box_iff {a b : ℕ} {s : kˣ} {X Y : Fin a → Fin b → k} (hY : Y ∈ box a b s) :
    X + Y ∈ box a b s ↔ X ∈ box a b s := by
  rw [mem_box] at hY
  simp only [mem_box, Pi.add_apply]
  constructor
  · intro h p q
    simpa using add_mem_cball (h p q) (neg_mem_cball (hY p q))
  · intro h p q
    exact add_mem_cball (h p q) (hY p q)

theorem exists_mem_box {a b : ℕ} (X : Fin a → Fin b → k) : ∃ s : kˣ, X ∈ box a b s := by
  set γ : ValueGroupWithZero k := ∏ pq : Fin a × Fin b, max 1 (valuation k (X pq.1 pq.2)) with hγ
  have h1 : ∀ pq ∈ (Finset.univ : Finset (Fin a × Fin b)), 1 ≤ max 1 (valuation k (X pq.1 pq.2)) :=
    fun _ _ => le_max_left _ _
  have hγ1 : 1 ≤ γ := Finset.one_le_prod' h1
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective γ
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact absurd (hy ▸ hγ1) (by simp)
  refine ⟨Units.mk0 y hy0, mem_box.mpr fun p q => ?_⟩
  show valuation k (X p q) ≤ valuation k y
  rw [hy]
  exact (le_max_right _ _).trans (Finset.single_le_prod' h1 (Finset.mem_univ (p, q)))

theorem directed_box (a b : ℕ) : Directed (· ⊆ ·) (box (k := k) a b) := by
  intro s t
  rcases le_total (valuation k (s : k)) (valuation k (t : k)) with h | h
  · exact ⟨t, box_mono h, subset_rfl⟩
  · exact ⟨s, subset_rfl, box_mono h⟩

theorem exists_subset_box {a b : ℕ} {K : Set (Fin a → Fin b → k)} (hK : IsCompact K) :
    ∃ s : kˣ, K ⊆ box a b s :=
  hK.elim_directed_cover _ (isOpen_box a b) (fun X _ => Set.mem_iUnion.mpr (exists_mem_box X))
    (directed_box a b)

section Meas
variable [MeasurableSpace k] [BorelSpace k]

theorem main : ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  intro N V _ _ π hπ a b μ hμ u hu hadd l w hw F hF hFw
  haveI := secondCountable k
  haveI := t2Space k
  haveI : OpensMeasurableSpace (Fin b → k) := inferInstance
  haveI : OpensMeasurableSpace (Fin a → Fin b → k) := inferInstance
  have hu0 : u 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

  have hcont : ∀ y : V, Continuous fun X => l (π (u X) y) := by
    intro y
    have hlc : IsLocallyConstant fun X => π (u X) y := by
      refine (IsLocallyConstant.iff_eventually_eq _).mpr fun X₀ => ?_
      have hO : IsOpen ((fun X => u (X - X₀)) ⁻¹' {g | π g y = y}) :=
        (hπ y).preimage (hu.comp (continuous_id.sub continuous_const))
      have hX₀ : X₀ ∈ (fun X => u (X - X₀)) ⁻¹' {g | π g y = y} := by
        simp [hu0]
      filter_upwards [hO.mem_nhds hX₀] with X hX
      have hX' : π (u (X - X₀)) y = y := hX
      have e : X = X₀ + (X - X₀) := by abel
      rw [e, hadd, map_mul, Module.End.mul_apply, hX']
    exact (hlc.comp l).continuous
  have hmeas : ∀ s : kˣ, MeasurableSet (box a b s) := fun s => (isOpen_box a b s).measurableSet
  have hint : ∀ (y : V) (s : kˣ), IntegrableOn (fun X => l (π (u X) y)) (box a b s) μ :=
    fun y s => (hcont y).continuousOn.integrableOn_compact (isCompact_box a b s)

  have hshift : ∀ (y : V) (s : kˣ) (Y : Fin a → Fin b → k), Y ∈ box a b s →
      ∫ X in box a b s, l (π (u (X + Y)) y) ∂μ = ∫ X in box a b s, l (π (u X) y) ∂μ := by
    intro y s Y hY
    rw [← integral_indicator (hmeas s), ← integral_indicator (hmeas s)]
    have : ∀ X, (box a b s).indicator (fun X => l (π (u (X + Y)) y)) X =
        (box a b s).indicator (fun X => l (π (u X) y)) (X + Y) := by
      intro X
      by_cases hX : X ∈ box a b s
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem ((add_mem_box_iff hY).mpr hX)]
      · rw [Set.indicator_of_notMem hX,
          Set.indicator_of_notMem (fun h => hX ((add_mem_box_iff hY).mp h))]
    simp only [this]
    exact integral_add_right_eq_self (μ := μ) (fun X => (box a b s).indicator (fun X => l (π (u X) y)) X) Y

  have key : ∀ w' ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y},
      ∃ s₀ : kˣ, ∀ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) →
        ∫ X in box a b s, l (π (u X) w') ∂μ = 0 := by
    intro w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, y, rfl⟩ := hx
      obtain ⟨s₀, hs₀⟩ := exists_mem_box Y
      refine ⟨s₀, fun s hs => ?_⟩
      have hY : Y ∈ box a b s := box_mono hs hs₀
      have e : ∀ X, l (π (u X) (π (u Y) y - y)) = l (π (u (X + Y)) y) - l (π (u X) y) := by
        intro X
        rw [map_sub, map_sub, hadd, map_mul, Module.End.mul_apply]
      simp only [e]
      have hi2 : IntegrableOn (fun X => l (π (u (X + Y)) y)) (box a b s) μ :=
        ((hcont y).comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact (isCompact_box a b s)
      rw [integral_sub hi2 (hint y s), hshift y s Y hY, sub_self]
    | zero => exact ⟨1, fun s _ => by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨s₁, h₁⟩ := hx
      obtain ⟨s₂, h₂⟩ := hz
      rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
      · refine ⟨s₂, fun s hs => ?_⟩
        simp only [map_add (f := _)]
        rw [integral_add (hint x s) (hint z s), h₁ s (h.trans hs), h₂ s hs, add_zero]
      · refine ⟨s₁, fun s hs => ?_⟩
        simp only [map_add (f := _)]
        rw [integral_add (hint x s) (hint z s), h₁ s hs, h₂ s (h.trans hs), add_zero]
    | smul c x _ hx =>
      obtain ⟨s₀, h₀⟩ := hx
      refine ⟨s₀, fun s hs => ?_⟩
      simp only [map_smul, smul_eq_mul]
      rw [integral_const_mul, h₀ s hs, mul_zero]
  obtain ⟨s₀, hs₀⟩ := key w hw
  obtain ⟨s₁, hs₁⟩ := exists_subset_box hF
  obtain ⟨s, hs0, hs1⟩ : ∃ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) ∧
      box a b s₁ ⊆ box a b s := by
    rcases le_total (valuation k (s₀ : k)) (valuation k (s₁ : k)) with h | h
    · exact ⟨s₁, h, subset_rfl⟩
    · exact ⟨s₀, le_rfl, box_mono h⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := box a b s)
    (fun X hX => image_eq_zero_of_notMem_tsupport (fun h => hX (hs1 (hs₁ h))))]
  simp only [hFw]
  exact hs₀ s hs0

end Meas

theorem integral_coef_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  intro k _ _ _ _ _ _
  exact main

end GlobalTheory.UnipCoefInt
end
end

section

open Polynomial Matrix

namespace GlobalTheory.LocalCommutant

open GlobalTheory.ClassParam

variable {S : Type} [CommRing S] {n : ℕ}

theorem krylov_mulVec (Y : Matrix (Fin n) (Fin n) S) (v c : Fin n → S) :
    krylov Y v *ᵥ c = ∑ j, c j • (Y ^ (j : ℕ) *ᵥ v) := by
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem aeval_sum_monomial (Y : Matrix (Fin n) (Fin n) S) (c : Fin n → S) :
    aeval Y (∑ j : Fin n, monomial (j : ℕ) (c j)) = ∑ j : Fin n, c j • Y ^ (j : ℕ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, aeval_monomial, Algebra.smul_def]

theorem exists_isUnit_krylov (R : Type) [CommRing R] [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R)
    (hs : Y.charpoly.Separable) : ∃ v, IsUnit (krylov Y v) := by
  obtain ⟨w, hw⟩ := exists_cyclic_field (Y.map (IsLocalRing.residue R)) (by rw [charpoly_map]; exact hs.map)
  choose e he using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨e, (Matrix.isUnit_iff_isUnit_det _).2 ?_⟩
  have h1 : w = (IsLocalRing.residue R) ∘ e := funext fun i => (he i).symm
  rw [h1, ← krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hw
  exact (isUnit_map_iff (IsLocalRing.residue R) _).1 (isUnit_iff_ne_zero.2 hw)

theorem exists_aeval_of_comm (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ)
    (Y T : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) (hc : T * Y = Y * T) :
    ∃ p : R[X], T = aeval Y p := by
  obtain ⟨e, hK⟩ := exists_isUnit_krylov R Y hs
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hK
  set K := krylov Y e
  set c := K⁻¹ *ᵥ (T *ᵥ e)
  refine ⟨∑ j : Fin n, monomial (j : ℕ) (c j), ?_⟩
  set p : R[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  set D := T - aeval Y p
  have hKc : K *ᵥ c = T *ᵥ e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hDe : D *ᵥ e = 0 := by
    have h2 : aeval Y p *ᵥ e = K *ᵥ c := by
      rw [aeval_sum_monomial, Matrix.sum_mulVec, krylov_mulVec]
      simp [Matrix.smul_mulVec]
    rw [Matrix.sub_mulVec, h2, hKc, sub_self]
  have hpY : aeval Y p * Y = Y * aeval Y p := by
    calc aeval Y p * Y = aeval Y (p * X) := by simp
      _ = aeval Y (X * p) := by rw [mul_comm]
      _ = Y * aeval Y p := by simp
  have hDY : Commute D Y := Commute.sub_left hc hpY
  have hDK : D * K = 0 := by
    ext i j
    have h2 : D *ᵥ (Y ^ (j : ℕ) *ᵥ e) = 0 := by
      rw [Matrix.mulVec_mulVec, (hDY.pow_right _).eq, ← Matrix.mulVec_mulVec, hDe, Matrix.mulVec_zero]
    have := congrFun h2 i
    simpa [K, krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hD : D = 0 := by
    calc D = D * K * K⁻¹ := by rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
      _ = 0 := by rw [hDK, zero_mul]
  exact sub_eq_zero.1 hD

end GlobalTheory.LocalCommutant
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.BZBridge

section Transport

variable {H G V : Type} [Group H] [Group G] [TopologicalSpace H] [TopologicalSpace G]
  [AddCommGroup V] [Module ℂ V]

def subrepCompEquiv (π : Representation ℂ G V) (Φ : H ≃* G) :
    Subrepresentation (π.comp Φ.toMonoidHom : Representation ℂ H V) ≃o Subrepresentation π where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (Φ.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (Φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp (π : Representation ℂ G V) (Φ : H ≃* G) (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp Φ.toMonoidHom : Representation ℂ H V) := by
  have := h
  exact (subrepCompEquiv π Φ).isSimpleOrder

theorem isSmooth_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (h : IsSmooth π) :
    IsSmooth (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V) := by
  intro v
  exact (h v).preimage (map_continuous Φ)

theorem isAdmissible_of_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (hs : IsSmooth π)
    (h : IsAdmissible (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V)) : IsAdmissible π := by
  refine ⟨hs, fun K hKo hKc => ?_⟩

  set K' : Subgroup H := K.comap Φ.toMulEquiv.toMonoidHom with hK'
  have hset : (K' : Set H) = Φ.symm '' (K : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨Φ x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      show Φ (Φ.symm y) ∈ K
      simpa using hy
  have hK'o : IsOpen (K' : Set H) := hKo.preimage (map_continuous Φ)
  have hK'c : IsCompact (K' : Set H) := by
    rw [hset]
    exact hKc.image (map_continuous Φ.symm)
  have := h.2 K' hK'o hK'c
  refine Submodule.finiteDimensional_of_le (S₂ := fixed (π.comp Φ.toMulEquiv.toMonoidHom) K') ?_
  intro v hv
  simp only [fixed, eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq] at hv ⊢
  intro x
  have h1 := hv ⟨Φ x, x.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  exact h1

end Transport

def glReindex (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ε : ι ≃ κ) : GL ι K ≃ₜ* GL κ K where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv K K ε).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩

theorem irreducibleAdmissible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : IrreducibleAdmissible k := by
  intro n _ _ V _ _ π hs hi
  let Φ := glReindex k (Fintype.equivFin n).symm
  exact isAdmissible_of_comp π Φ hs
    (hA k (Fintype.card n) V _ (isSmooth_comp π Φ hs) (isIrreducible_comp π Φ.toMulEquiv hi))

end GlobalTheory.BZBridge
end
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → sᵀ * s = 1 → P.det ≠ 0 → GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | exact GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | (intros; apply GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.arithmetic_forms_span_invariant : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  first | exact @GlobalTheory.IntFormsRank.rkK_Mall | exact GlobalTheory.IntFormsRank.rkK_Mall | (intros; apply GlobalTheory.IntFormsRank.rkK_Mall <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.integralForms_eq_span_integralRationalForms : ∀ (LL Ks WL G0 : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ), A.IsKsForm → (∀ u : J0, ∀ f ∈ A.WK, A.ρ u f ∈ A.WK) → (∀ u : J0, ((A.chi u * lam0 u : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)) → A.Mall J0 lam0 = Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0} := by
  first | exact @GlobalTheory.mall_eq_span_rat | exact GlobalTheory.mall_eq_span_rat | (intros; apply GlobalTheory.mall_eq_span_rat <;> assumption)
end
