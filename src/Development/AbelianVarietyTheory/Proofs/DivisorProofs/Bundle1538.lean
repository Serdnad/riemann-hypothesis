module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousDblIncl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.RealLiftCompD

open Matrix GlobalTheory.RealLiftGen

theorem exists_compD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (∀ w : InfinitePlace F, Mat (R w) (S w)), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) ∧ ∀ w (M M' : Mat (R w) (S w)), C w * M = C w * M' → M = M' := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm (R w) (S w) := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm (R w) (S w) * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm (R w) (S w)), Matrix.mul_assoc (Jm (R w) (S w)), hF, Jm_mul_Jm]
    have h2 : (Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : UG (cA σ) J → InfinitePlace F → Matrix β β ℂ :=
    fun g w => (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMmul : ∀ g h w, M (g * h) w = M g w * M h w := by
    intro g h w
    simp only [hM, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM1 : ∀ w, M 1 w = 1 := by
    intro w
    simp only [hM, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ g w, (M g w)ᵀ * K w * (M g w).map star = K w := by
    intro g w
    have hg := g.2
    change ((g.1 : Matrix β β (AE F E)))ᵀ * J * ((g.1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M g w)ᵀ * J.map (piInf (τ w)) * (M g w).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  let k : UG (cA σ) J →* (∀ w : InfinitePlace F, Mat (R w) (S w)) :=
    { toFun := fun g w => A' w * M g w * C w
      map_one' := by funext w; simp only [hM1, Matrix.mul_one, hAC, Pi.one_apply]
      map_mul' := by
        intro g h; funext w
        simp only [hMmul, Pi.mul_apply]
        calc A' w * (M g w * M h w) * C w = A' w * M g w * (C w * A' w) * M h w * C w := by
              rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hk : ∀ g w, k g w = A' w * M g w * C w := fun _ _ => rfl
  have hCk : ∀ g w, C w * k g w = M g w * C w := by
    intro g w; simp only [hk, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  refine ⟨k, ?_, fun g w => (hCk g w).symm, fun g w => ?_, fun w X X' h => ?_⟩
  · have h1 : Continuous (fun g : UG (cA σ) J => ((g.1 : Matrix β β (AE F E)))) :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_pi fun w => ?_
    exact (continuous_const.matrix_mul (h1.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (τ w)))).matrix_mul
      continuous_const
  · have hT : (k g w)ᵀ * Jm (R w) (S w) * (k g w).map star = Jm (R w) (S w) := by
      rw [← hF w]
      calc (k g w)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (k g w).map star
          = (C w * k g w)ᵀ * K w * (C w * k g w).map star := by
            simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = (C w)ᵀ * ((M g w)ᵀ * K w * (M g w).map star) * (C w).map star := by
            simp only [hCk, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = _ := by rw [hMu]
    have h2 := congrArg (fun X => X.map star) hT
    simp only [map_star_mul, Jm_map_star, map_star_star] at h2
    exact h2
  · have := congrArg (fun Y => A' w * Y) h
    simpa only [← Matrix.mul_assoc, hAC, Matrix.one_mul] using this

end GlobalTheory.RealLiftCompD
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
namespace GlobalTheory.RealLift.VacBox

def eL {R S : ℕ} : Ix R S → Ix (R + S) (S + R) :=
  Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))

def eR {R S : ℕ} : Ix R S → Ix (R + S) (S + R) :=
  Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))

theorem dbl_cols {α β : Type} [Fintype β] {P Q R S : ℕ} (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ) :
    (A * c * (dblM C)ᵀ).toCols₁ = A * c.submatrix id eL * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ = A * c.submatrix id eR * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id eL = Jm P Q * c.submatrix id eL * Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id eR = -(Jm P Q * c.submatrix id eR * Jm R S) :=
  GlobalTheory.T.doubledSpaceFrame_colBlocks_eq α β P Q R S A C c

theorem heisOp_rot_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) :
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 :=
  GlobalTheory.T.fockHeisenbergOperatorOfCoords_real_I_smul_signConj_one P Q R S c t

theorem box_deriv {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ))
    (hg₁ : ∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y)
    (hg₂ : ∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y)
    (hh : ∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x)
    (hf₀ : ∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) :=
  GlobalTheory.T.heisenberg_derivative_on_schwartz_tensor_conj F κ a₁ b₁ a₂ b₂ f g₁ g₂ f₀ h hg₁ hg₂ hh hf₀ x

def conjS {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem sumPl_smul_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (L L' : ι → Module.End ℂ V) (v : V) (z : ℂ) (h : ∀ w, L' w v = z • L w v) :
    sumPl (V := fun _ : ι => V) L' (PiTensorProduct.tprod ℂ fun _ => v) =
      z • sumPl (V := fun _ : ι => V) L (PiTensorProduct.tprod ℂ fun _ => v) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl, PiTensorProduct.map_tprod]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : ∀ M : Module.End ℂ V, (fun i => Function.update (fun i => (LinearMap.id : V →ₗ[ℂ] V)) w M i v) =
      Function.update (fun _ => v) w (M v) := by
    intro M; funext i
    by_cases hi : i = w
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [e, e, h w]
  exact MultilinearMap.map_update_smul _ _ _ _ _

theorem sub_smul' {m n k : Type} (z : ℂ) (M : Matrix m n ℂ) (e : k → n) :
    (z • M).submatrix id e = z • M.submatrix id e := rfl

theorem toCols_at {F E α β₁ β₂ : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {u : Matrix α (β₁ ⊕ β₂) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evI F) u) : At (evI F) u.toCols₁ ∧ At (evI F) u.toCols₂ :=
  ⟨fun r hr => by ext i j; exact congrFun (congrFun (hu r hr) i) (Sum.inl j),
   fun r hr => by ext i j; exact congrFun (congrFun (hu r hr) i) (Sum.inr j)⟩

theorem vac_box : DerEx → VacLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ))
    (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ)),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsDblCoord (cA σ) (-1) JA JB d dd →
    IsFockMap ψ τ dd A (fun w => dblM (C w)) Φd →
    ∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr)) := by
  intro hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
  obtain ⟨D, hD1⟩ := hD F E σ α β κ ψ JA JB d hψ
  obtain ⟨Dd, hDd⟩ := hD F E σ α (β ⊕ β) (κ ⊕ κ) ψ JA (dbl JB) dd hψ
  set f₁ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hf₁
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (conjS f₁)
  have hf₀' : ∀ x, f₀ x = f₁ (x ∘ Sum.inl) * star (f₁ (x ∘ Sum.inr)) := fun x => hf₀ x
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  have hder : ∀ u₁ : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u₁ → ∀ c₁ : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u₁.map (piInf (τ w)) = A w * c₁ w * (C w)ᵀ) →
      D u₁ f₁ = Φ (sumPl (fun w => heisOp (c₁ w)) (PiTensorProduct.tprod ℂ fun _ => 1)) := fun u₁ hu₁ c₁ hc₁ =>
    GlobalTheory.SDUnique.sd_unique ((hD1 u₁ hu₁ f₁).1) (hΦ.2 u₁ hu₁ c₁ hc₁ _)
  have hbox : ∀ u : Matrix α (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∀ x, Dd u f₀ x =
      D u.toCols₁ f₁ (x ∘ Sum.inl) * star (f₁ (x ∘ Sum.inr)) +
        f₁ (x ∘ Sum.inl) * star (D u.toCols₂ f₁ (x ∘ Sum.inr)) := by
    intro u hu x
    obtain ⟨hu₁, hu₂⟩ := toCols_at hu
    have e := hdd u.toCols₁ u.toCols₂
    rw [Matrix.fromCols_toCols] at e
    refine box_deriv (d.e u.toCols₁).1 (d.e u.toCols₁).2 (d.e u.toCols₂).1 (d.e u.toCols₂).2 f₁ _ _ f₀ _
      ((hD1 _ hu₁ f₁).2) ((hD1 _ hu₂ f₁).2) (fun y => ?_) hf₀' x
    rw [(hDd u hu f₀).2 y, e]
  have key : ∀ u u' : Matrix α (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' →
      ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (dblM (C w))ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * (((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) •
        (Jm P Q * c w * Jm (R + S) (S + R))) * (dblM (C w))ᵀ) →
      ∀ f f' : SInf F (κ ⊕ κ), SD (fun t => dd.rho ψ (realAd F t • u)) f₀ f →
        SD (fun t => dd.rho ψ (realAd F t • u')) f₀ f' → f' = Complex.I • f := by
    intro u u' hu hu' c hc hc' f f' hf hf'
    rw [← GlobalTheory.SDUnique.sd_unique ((hDd u hu f₀).1) hf, ← GlobalTheory.SDUnique.sd_unique ((hDd u' hu' f₀).1) hf']
    obtain ⟨hu₁, hu₂⟩ := toCols_at hu
    obtain ⟨hu₁', hu₂'⟩ := toCols_at hu'
    have hI : ∀ w, ((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) = ((1 : ℝ) : ℂ) * Complex.I := fun w => by simp
    have h1 := hder _ hu₁ (fun w => (c w).submatrix id eL) (fun w => by
      rw [← (dbl_cols (A w) (C w) (c w)).1, ← hc w]; rfl)
    have h2 := hder _ hu₂ (fun w => (c w).submatrix id eR) (fun w => by
      rw [← (dbl_cols (A w) (C w) (c w)).2.1, ← hc w]; rfl)
    have h1' := hder _ hu₁' (fun w => (((1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eL * Jm R S))
      (fun w => by
        rw [← (dbl_cols (A w) (C w) (c w)).2.2.1, ← sub_smul', ← hI w,
          ← (dbl_cols (A w) (C w) _).1, ← hc' w]; rfl)
    have h2' := hder _ hu₂' (fun w => (((-1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eR * Jm R S))
      (fun w => by
        have e : (((-1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eR * Jm R S) =
            ((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) • (-(Jm P Q * (c w).submatrix id eR * Jm R S)) := by
          rw [hI w, smul_neg, ← neg_smul]; congr 1; push_cast; ring
        rw [e, ← (dbl_cols (A w) (C w) (c w)).2.2.2, ← sub_smul', ← (dbl_cols (A w) (C w) _).2.1, ← hc' w]; rfl)
    rw [sumPl_smul_tprod _ _ _ _ (fun w => heisOp_rot_one _ 1)] at h1'
    rw [sumPl_smul_tprod _ _ _ _ (fun w => heisOp_rot_one _ (-1))] at h2'
    rw [map_smul] at h1' h2'
    ext x
    rw [SchwartzMap.smul_apply, hbox u' hu' x, hbox u hu x, h1', h2', h1, h2]
    simp only [SchwartzMap.smul_apply, smul_eq_mul, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring
  obtain ⟨z', hz'⟩ := hV F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd hCM hψ hFrd hΦd f₀ 1 key
  have hne1 : f₁ ≠ 0 := fun h0 => GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (h0.trans (map_zero Φ).symm))
  obtain ⟨y, hy⟩ : ∃ y, f₁ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne1 (SchwartzMap.ext h)
  have hz0 : z' ≠ 0 := by
    rintro rfl
    have h := congrArg (fun g : SInf F (κ ⊕ κ) => g (Sum.elim y y)) hz'
    simp only [zero_smul, SchwartzMap.zero_apply, hf₀', Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    exact mul_ne_zero hy (star_ne_zero.2 hy) h
  refine ⟨z'⁻¹, inv_ne_zero hz0, fun x => ?_⟩
  have h := congrArg (fun g : SInf F (κ ⊕ κ) => g x) hz'
  simp only [SchwartzMap.smul_apply, smul_eq_mul, hf₀'] at h
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

end GlobalTheory.RealLift.VacBox

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.Compare

theorem constant_eq_dbl :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (c cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → IsFockMap ψ τ d A C Φ →
    (∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)),
      ((gd : GL (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (β ⊕ β) (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((g : GL β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) 0 0 1 →
      ∀ φ₁ ∈ (adeleClass F).sp κ, ∀ φ₂ ∈ (adeleClass F).sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) →
    ActsBy τ C om Φ (fockAct2 P Q R S) c →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr))) →
    0 < R + S → ∀ w, c w = cd w :=
  compare_of GlobalTheory.T.exists_central_circle_oneParameter_unitary_realPlace GlobalTheory.VacuumWeight.fockAct2_diagonal_one GlobalTheory.tprod_one_pol_ne_zero

end GlobalTheory.RealLift.Compare
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaTrContCM

theorem continuous_thetaTr_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hs hψ JA JB ξ hA hBm κ _ co hco φ hφ
  exact GlobalTheory.ThetaTrContF.continuous_thetaTrF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hs JA JB ξ hA hBm κ co hco φ hφ

end GlobalTheory.ThetaTrContCM
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.continuous_thetaTransform_schwartz_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @GlobalTheory.ThetaTrContF.continuous_thetaTrF | exact GlobalTheory.ThetaTrContF.continuous_thetaTrF | (intros; apply GlobalTheory.ThetaTrContF.continuous_thetaTrF <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaQuasiRatCM

theorem thetaTr_ratWF_add_quasi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (Formalism.IndefR.DatumF.ratWF γ + w) =
              B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hξ hψ JA JB ξ hA hJB κ _ co hrat φ hφ γ w
  exact GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hξ JA JB ξ hA hJB κ co hrat φ hφ γ w

end GlobalTheory.ThetaQuasiRatCM
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.thetaTransform_rationalTranslate_quasiInvariant_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (ratWF γ + w) = B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w := by
  first | exact @GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add | exact GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add | (intros; apply GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add <;> assumption)
end

section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory

theorem conj_one_tmul_charpoly : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (x : (R ⊗[ℚ] A)ˣ) (y : A), (LevelExists.mulMatAlg R A ((x : R ⊗[ℚ] A) * (1 ⊗ₜ[ℚ] y) * ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A))).charpoly = (LinearMap.mulLeft ℚ y).charpoly.map (algebraMap ℚ R) := by
  intro R _ _ A _ _ _ x y
  set b := Module.finBasis ℚ A
  set u := Units.map (LevelExists.mulMatAlg R A).toMonoidHom x with hu
  have h1 : LevelExists.mulMatAlg R A (x : R ⊗[ℚ] A) = (u : Matrix _ _ R) := rfl
  have h2 : LevelExists.mulMatAlg R A ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A) = ((u⁻¹ : (Matrix _ _ R)ˣ) : Matrix _ _ R) := by
    rw [hu, ← map_inv]; rfl
  have hM : LevelExists.mulMatAlg R A (1 ⊗ₜ[ℚ] y) =
      (LinearMap.toMatrix b b (LinearMap.mulLeft ℚ y)).map (algebraMap ℚ R) := by
    ext i j
    simp [LevelExists.mulMatAlg, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_repr_tmul, b, Algebra.leftMulMatrix_eq_repr_mul]
  rw [map_mul, map_mul, h1, h2, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hM, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix]

end GlobalTheory
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → V.valuation (L.derivWeierstrassP z) = V.valuation u ^ 3 := by
  first | exact @GlobalTheory.valuation_derivWeierstrassP_torsion_odd | exact GlobalTheory.valuation_derivWeierstrassP_torsion_odd | (intros; apply GlobalTheory.valuation_derivWeierstrassP_torsion_odd <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.projArith_charZero_functionField_injective_constants : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  first | exact @GlobalTheory.isArithVar_charZero_functionField_and_injective | exact GlobalTheory.isArithVar_charZero_functionField_and_injective | (intros; apply GlobalTheory.isArithVar_charZero_functionField_and_injective <;> assumption)
end
