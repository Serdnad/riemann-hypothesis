module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.Rearrangement

@[expose] public section

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

noncomputable section

namespace GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ}

def dualCoord (E : KMod n) :
    (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) where
  toFun ξ := WithLp.toLp 2 fun i => ξ (stdOrthonormalBasis ℂ E.V i)
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp
  invFun v := ∑ i, v i • innerSL ℂ (stdOrthonormalBasis ℂ E.V i)
  left_inv ξ := by
    ext x
    have hx := (stdOrthonormalBasis ℂ E.V).sum_repr' x
    conv_rhs => rw [← hx]

    simp [map_sum, mul_comm]
  right_inv v := by
    ext j
    have ho := (stdOrthonormalBasis ℂ E.V).orthonormal
    simp [orthonormal_iff_ite.mp ho]

theorem norm_dualCoord (E : KMod n) (ξ : E.V →L[ℂ] ℂ) : ‖dualCoord E ξ‖ = ‖ξ‖ := by
  set r := (InnerProductSpace.toDual ℂ E.V).symm ξ with hr
  have h1 : ‖r‖ = ‖ξ‖ := (InnerProductSpace.toDual ℂ E.V).symm.norm_map ξ
  have h2 : ‖(stdOrthonormalBasis ℂ E.V).repr r‖ = ‖r‖ :=
    (stdOrthonormalBasis ℂ E.V).repr.norm_map r
  rw [← h1, ← h2, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : (dualCoord E ξ) i = ξ (stdOrthonormalBasis ℂ E.V i) := rfl
  rw [h3, OrthonormalBasis.repr_apply_apply, ← InnerProductSpace.toDual_symm_apply (𝕜 := ℂ), ← hr,
    norm_inner_symm]

def dualAct (E : KMod n) : (E.V →L[ℂ] E.V) →ₗ[ℂ]
    (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) where
  toFun T := LinearMap.toContinuousLinearMap
    ((dualCoord E).toLinearMap ∘ₗ
      (((ContinuousLinearMap.compL ℂ E.V E.V ℂ).flip T : (E.V →L[ℂ] ℂ) →L[ℂ] (E.V →L[ℂ] ℂ)) :
        (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ∘ₗ (dualCoord E).symm.toLinearMap)
  map_add' S T := by
    ext v : 1
    simp
  map_smul' c T := by
    ext v : 1
    simp

theorem dualAct_apply (E : KMod n) (T : E.V →L[ℂ] E.V) (v) :
    dualAct E T v = dualCoord E ((dualCoord E).symm v ∘L T) := by
  simp [dualAct]

theorem continuous_unitary_inv :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k⁻¹ := by
  refine Continuous.subtype_mk (p := (· ∈ Matrix.unitaryGroup (Fin n) ℂ)) ?_ _
  simpa using (continuous_subtype_val.star :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => star k.1)

theorem dualRep_exists {n : ℕ} (E : KMod n) :
    ∃ (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))
      (ρ' : Matrix.unitaryGroup (Fin n) ℂ →*
        (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
          EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))),
      Continuous ρ' ∧ (∀ k v, ‖ρ' k v‖ = ‖v‖) ∧ ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ) := by
  have hact : ∀ k ξ, dualAct E (E.ρ k⁻¹) (dualCoord E ξ) = dualCoord E (ξ ∘L E.ρ k⁻¹) := by
    intro k ξ
    rw [dualAct_apply, LinearEquiv.symm_apply_apply]
  let ρ' : Matrix.unitaryGroup (Fin n) ℂ →*
      (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) :=
    { toFun := fun k => dualAct E (E.ρ k⁻¹)
      map_one' := by
        ext1 v
        rw [dualAct_apply, inv_one, map_one]
        change dualCoord E ((dualCoord E).symm v ∘L ContinuousLinearMap.id ℂ E.V) = v
        rw [ContinuousLinearMap.comp_id, LinearEquiv.apply_symm_apply]
      map_mul' := by
        intro k l
        ext1 v
        obtain ⟨ξ, rfl⟩ := (dualCoord E).surjective v
        rw [ContinuousLinearMap.mul_apply, hact l, hact k, hact (k * l), _root_.mul_inv_rev, map_mul]
        rfl }
  refine ⟨dualCoord E, ρ', ?_, ?_, fun k ξ => (hact k ξ).symm⟩
  · have h1 : Continuous (dualAct E) := LinearMap.continuous_of_finiteDimensional _
    exact h1.comp (E.cont.comp continuous_unitary_inv)
  · intro k v
    obtain ⟨ξ, rfl⟩ := (dualCoord E).surjective v
    have hle : ∀ (l : Matrix.unitaryGroup (Fin n) ℂ) (η : E.V →L[ℂ] ℂ), ‖η ∘L E.ρ l‖ ≤ ‖η‖ := by
      intro l η
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      simpa [E.iso] using η.le_opNorm (E.ρ l x)
    have hback : (ξ ∘L E.ρ k⁻¹) ∘L E.ρ k = ξ := by
      ext x
      have : E.ρ k⁻¹ (E.ρ k x) = x := by
        have h := congrArg (fun T : E.V →L[ℂ] E.V => T x) (E.ρ.map_mul k⁻¹ k)
        simpa using h.symm
      simp [this]
    have h2 : ‖ξ ∘L E.ρ k⁻¹‖ = ‖ξ‖ := by
      refine le_antisymm (hle _ _) ?_
      calc ‖ξ‖ = ‖(ξ ∘L E.ρ k⁻¹) ∘L E.ρ k‖ := by rw [hback]
        _ ≤ _ := hle _ _
    change ‖dualAct E (E.ρ k⁻¹) (dualCoord E ξ)‖ = _
    rw [hact, norm_dualCoord, norm_dualCoord, h2]

end GlobalTheory.CompanionTheory.RealCount
end
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult.Short

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot nsq)

variable {n : ℕ}

theorem dL_add (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, sum_add_distrib]

theorem dL_sub (u v w : Fin n → ℝ) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, sum_sub_distrib]

theorem dL_smul (c : ℝ) (u w : Fin n → ℝ) : dot (c • u) w = c * dot u w := by
  simp [dot, mul_sum, mul_assoc]

theorem d_comm (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp [dot, mul_comm]

theorem dR_add (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, sum_add_distrib]

theorem dR_sub (u v w : Fin n → ℝ) : dot u (v - w) = dot u v - dot u w := by
  simp [dot, mul_sub, sum_sub_distrib]

theorem dR_smul (c : ℝ) (u w : Fin n → ℝ) : dot u (c • w) = c * dot u w := by
  rw [d_comm, dL_smul, d_comm]

theorem d_perm (u v : Fin n → ℝ) (w : Equiv.Perm (Fin n)) : dot (u ∘ w) (v ∘ w) = dot u v := by
  simpa [dot] using Equiv.sum_comp w (fun a => u a * v a)

theorem d_self_nonneg (u : Fin n → ℝ) : 0 ≤ dot u u :=
  sum_nonneg fun a _ => mul_self_nonneg _

theorem rho_sub (a b : Fin n) : rhoV n a - rhoV n b = (b : ℕ) - (a : ℕ) := by
  simp only [rhoV]; ring

theorem rho_anti : StrictAnti (rhoV n) := by
  intro a b h
  have h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h
  have := rho_sub a b
  linarith

theorem rearr (u : Fin n → ℝ) (hu : Antitone u) (σ : Equiv.Perm (Fin n)) :
    dot u (rhoV n ∘ σ) ≤ dot u (rhoV n) :=
  Monovary.sum_mul_comp_perm_le_sum_mul (hu.monovary rho_anti.antitone)

def s0 (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

def mB (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ := if (a, b) ∈ B then 1 else 0

def sg (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ := s0 a b - 2 * mB B a b + 2 * mB B b a

theorem sign_antisymmetric_alt (a b : Fin n) : s0 b a = -s0 a b := by
  unfold s0
  rcases lt_trichotomy a b with h | h | h
  · simp [h, asymm h]
  · simp [h]
  · simp [h, asymm h]

theorem sg_anti (B : Finset (Fin n × Fin n)) (a b : Fin n) : sg B b a = -sg B a b := by
  unfold sg; rw [sign_antisymmetric_alt a b]; ring

theorem sign_self_eq_zero (a : Fin n) : s0 a a = 0 := by simp [s0]

theorem sum_sign_eq_two_rho (a : Fin n) : ∑ b, s0 a b = 2 * rhoV n a := by
  have h : ∀ b, s0 a b = (if a < b then (1 : ℝ) else 0) - (if b < a then (1 : ℝ) else 0) := by
    intro b
    unfold s0
    rcases lt_trichotomy a b with h | h | h
    · simp [h, asymm h]
    · simp [h]
    · simp [h, asymm h]
  simp only [h, sum_sub_distrib, sum_boole]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  have ha := a.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp [rhoV]
  ring

theorem sum_row_count (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, mB B a b = ((B.filter fun p => p.1 = a).card : ℝ) := by
  have : B.filter (fun p => p.1 = a) = (univ.filter fun b => (a, b) ∈ B).image (fun b => (a, b)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨y, h, rfl, rfl⟩
    · rintro ⟨c, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  rw [this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)]
  simp [mB]

theorem sum_column_count (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, mB B b a = ((B.filter fun p => p.2 = a).card : ℝ) := by
  have : B.filter (fun p => p.2 = a) = (univ.filter fun b => (b, a) ∈ B).image (fun b => (b, a)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨x, h, rfl, rfl⟩
    · rintro ⟨c, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  rw [this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]
  simp [mB]

theorem sum_sg (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, sg B a b = 2 * (rhoV n a - wtB B a) := by
  simp only [sg, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_sign_eq_two_rho, sum_row_count, sum_column_count, wtB]
  ring

theorem sg_val (B : Finset (Fin n × Fin n)) (hB : ∀ p ∈ B, p.1 < p.2) {a b : Fin n} (hab : a ≠ b) :
    sg B a b = 1 ∨ sg B a b = -1 := by
  have key : ∀ a b : Fin n, a < b → sg B a b = 1 ∨ sg B a b = -1 := by
    intro a b h
    have h1 : (b, a) ∉ B := fun hm => asymm h (hB _ hm)
    by_cases hm : (a, b) ∈ B
    · right; simp [sg, s0, mB, h, h1, hm]; norm_num
    · left; simp [sg, s0, mB, h, h1, hm]
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h
  · rw [sg_anti B b a]
    rcases key b a h with h' | h' <;> simp [h']

end GlobalTheory.CompanionTheory.RealMult.Short

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot nsq)
open Short

end GlobalTheory.CompanionTheory.RealMult
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

section Conj

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_isom_iff (c : R →+* R) (B g : GL ι R) (D J : Matrix ι ι R)
    (h : (B : Matrix ι ι R)ᵀ * D * (B : Matrix ι ι R).map c = J) :
    (((B⁻¹ * g * B : GL ι R) : Matrix ι ι R)ᵀ * J * ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R).map c = J) ↔
      (g : Matrix ι ι R)ᵀ * D * (g : Matrix ι ι R).map c = D := by
  have h1 : (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have h2 : (B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]
  have h1' : (B : Matrix ι ι R)ᵀ * (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  have h2' : ((B⁻¹ : GL ι R) : Matrix ι ι R).map c * (B : Matrix ι ι R).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]
  have key : ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R)ᵀ * J * ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R).map c =
      (B : Matrix ι ι R)ᵀ * ((g : Matrix ι ι R)ᵀ * D * (g : Matrix ι ι R).map c) * (B : Matrix ι ι R).map c := by
    subst h
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (B : Matrix ι ι R)ᵀ * (g : Matrix ι ι R)ᵀ * ((((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ) * D *
          ((B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) * (g : Matrix ι ι R).map c *
          (B : Matrix ι ι R).map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [key]
  constructor
  · intro e
    have e' := congrArg (fun M => (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * M * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) e
    subst h
    have l : ∀ M : Matrix ι ι R, (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * ((B : Matrix ι ι R)ᵀ * M * (B : Matrix ι ι R).map c) *
        ((B⁻¹ : GL ι R) : Matrix ι ι R).map c = M := fun M => by
      calc _ = ((((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ) * M *
            ((B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [l] at e'
    rw [e', l]
  · intro e
    rw [e, h]

end Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def bA (b : GL (Fin n ⊕ Fin n) E) : GL (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)) b

theorem bA_val (b : GL (Fin n ⊕ Fin n) E) :
    ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = incM F b.1 := rfl

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR]

theorem gram_frame (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ *
        dbl (incM F Y.J) * ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map
          (adCM σ χ).σ = Ad.J (AE F E) ε (Fin n) := by
  have := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) hb
  have e1 : (bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)).1.map (adCM σ χ).σ = (b.1.map σ).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    exact cA_inclR σ _
  have e2 : dbl (incM F Y.J) = (dbl Y.J).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl, incM]
  have e3 : (bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)).1ᵀ = (b.1ᵀ).map (inclR (F := F) (E := E) (AF F)) := rfl
  have e4 : Ad.J (AE F E) ε (Fin n) = (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;> simp [Ad.J, h, Matrix.one_apply]
  rw [e1, e2, e3, e4, ← this]
  simp only [Matrix.map_mul]

def frameEquiv (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    G2 σ Y ≃* (adCM σ χ).U ε (Fin n) where
  toFun x := ⟨(bA b)⁻¹ * x.1 * bA b, (conj_isom_iff (adCM σ χ).σ (bA b) x.1 _ _ (gram_frame χ ε b hb)).2 x.2⟩
  invFun y := ⟨bA b * y.1 * (bA b)⁻¹, by
    have h := (conj_isom_iff (adCM σ χ).σ (bA (F := F) b) (bA b * y.1 * (bA b)⁻¹) _ _ (gram_frame χ ε b hb)).1
    apply h
    have : (bA (F := F) b)⁻¹ * (bA b * y.1 * (bA b)⁻¹) * bA b = y.1 := by group
    rw [this]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    show bA b * ((bA b)⁻¹ * x.1 * bA b) * (bA b)⁻¹ = x.1
    group
  right_inv y := by
    apply Subtype.ext
    show (bA b)⁻¹ * (bA b * y.1 * (bA b)⁻¹) * bA b = y.1
    group
  map_mul' x y := by
    apply Subtype.ext
    show (bA b)⁻¹ * (x.1 * y.1) * bA b = ((bA b)⁻¹ * x.1 * bA b) * ((bA b)⁻¹ * y.1 * bA b)
    group

theorem frameEquiv_val (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (x : G2 σ Y) :
    (frameEquiv χ ε b hb x).1 = (bA b)⁻¹ * x.1 * bA b := rfl

theorem continuous_frameEquiv (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    Continuous (frameEquiv χ ε b hb) := by
  refine Continuous.subtype_mk ?_ _

  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem continuous_frameEquiv_symm (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    Continuous (frameEquiv χ ε b hb).symm := by
  refine Continuous.subtype_mk ?_ _

  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.CompanionTheory.SiegelFrame
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ChzConj

theorem chz_conj : ∀ (D : D7) (ρ p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (b : Mx D p p) (y : Mx D ρ p) (z₀ : hermA D ρ),
  z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) →
    chz ψ b₀ z₀ = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) := by
  intro D ρ p ψ b₀ b y z₀ hz
  unfold chz pr
  rw [hz]
  congr 2
  change Matrix.trace (Matrix.map b₀.1 (incA D) * ((y * b) * adj y)) = Matrix.trace (b * (adj y * (Matrix.map b₀.1 (incA D) * y)))
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ChzConj

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem leftInv_of_isLaw : ∀ {D : D7} {n : ℕ} (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsHeckeChar D χ → IsLaw χ s f → LeftInv (P D n ⊓ GF D n) f := by
  intro D n χ s f hχ hf γ hγ g
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hγ.1
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 a ha
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hf γ hγ.1 a ha g, hu, hχ.2 u, h1]
  simp

end GlobalTheory.CompanionTheory.FJE
end
end
