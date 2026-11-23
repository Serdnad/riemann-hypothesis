module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle139
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjection
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRadicalNormalFormPairOfFlags
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RmulMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle145
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.OrbitTerm

variable {E : Type} [Field E] [NumberField E] {j : ℕ}

def oneInf (E : Type) [Field E] [NumberField E] (j : ℕ) : MatInf E j := fun _ a b => if a = b then 1 else 0

theorem of_oneInf (w : InfinitePlace E) : Matrix.of (oneInf E j w) = 1 := by
  ext a b; simp [oneInf, Matrix.one_apply]

theorem of_mul (x y : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl

theorem matInf_ext {x y : MatInf E j} (h : ∀ w, Matrix.of (x w) = Matrix.of (y w)) : x = y :=
  funext fun w => Matrix.of.injective (h w)

theorem matInf_mul_assoc (x y z : MatInf E j) : x * y * z = x * (y * z) :=
  matInf_ext fun w => by simp only [of_mul, Matrix.mul_assoc]

theorem oneInf_mul (x : MatInf E j) : oneInf E j * x = x :=
  matInf_ext fun w => by rw [of_mul, of_oneInf, Matrix.one_mul]

theorem mul_oneInf (x : MatInf E j) : x * oneInf E j = x :=
  matInf_ext fun w => by rw [of_mul, of_oneInf, Matrix.mul_one]

theorem detNorm_mul (x y : MatInf E j) : _root_.GlobalTheory.FlagMeas.detNorm E j (x * y) = _root_.GlobalTheory.FlagMeas.detNorm E j x * _root_.GlobalTheory.FlagMeas.detNorm E j y := by
  simp only [_root_.GlobalTheory.FlagMeas.detNorm, of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem detNorm_oneInf : _root_.GlobalTheory.FlagMeas.detNorm E j (oneInf E j) = 1 := by
  simp [_root_.GlobalTheory.FlagMeas.detNorm, of_oneInf]

theorem detNorm_nonneg (x : MatInf E j) : 0 ≤ _root_.GlobalTheory.FlagMeas.detNorm E j x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem detNorm_pos_iff (x : MatInf E j) : 0 < _root_.GlobalTheory.FlagMeas.detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  rw [(detNorm_nonneg x).lt_iff_ne', _root_.GlobalTheory.FlagMeas.detNorm, Finset.prod_ne_zero_iff]
  simp

theorem measurable_entry (w : InfinitePlace E) (a b : Fin j) : Measurable fun x : MatInf E j => x w a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
    (measurable_pi_apply (X := fun _ : InfinitePlace E => Fin j → Fin j → ℂ) w))

theorem measurable_detNorm : Measurable (_root_.GlobalTheory.FlagMeas.detNorm E j) := by
  have h : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2 := by
    refine continuous_finsetProd _ fun w _ => Continuous.pow (Continuous.norm ?_) 2
    exact Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)
  exact h.measurable

theorem measurableSet_detNorm_pos : MeasurableSet {g : MatInf E j | 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g} :=
  measurableSet_lt measurable_const measurable_detNorm

theorem measurable_mul_left (γ : MatInf E j) : Measurable fun g : MatInf E j => γ * g := by
  refine Measurable.of_eval (X := fun _ : InfinitePlace E => Fin j → Fin j → ℂ) fun w =>
    Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  show Measurable fun g : MatInf E j => ∑ c, γ w a c * g w c b
  exact Finset.measurable_sum _ fun c _ => (measurable_entry w c b).const_mul _

theorem measurable_inv_entry (w : InfinitePlace E) (a b : Fin j) :
    Measurable fun g : MatInf E j => (Matrix.of (g w))⁻¹ a b := by
  have h1 : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => (Matrix.of (x w)).det :=
    Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)
  have h2 : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => (Matrix.of (x w)).adjugate a b :=
    (Continuous.matrix_adjugate (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)).matrix_elem a b
  have h3 := h1.measurable.inv.mul h2.measurable
  have : (fun g : MatInf E j => (Matrix.of (g w))⁻¹ a b) =
      fun g : MatInf E j => ((Matrix.of (g w)).det)⁻¹ * (Matrix.of (g w)).adjugate a b := by
    funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']; rfl
  rw [this]; exact h3

theorem haarGL_singular (hj : 1 ≤ j) : haarGL E j {g | 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g}ᶜ = 0 := by
  have hm : MeasurableSet {g : MatInf E j | 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g}ᶜ := measurableSet_detNorm_pos.compl
  unfold haarGL
  erw [withDensity_apply _ hm]
  refine setLIntegral_eq_zero hm fun g hg => ?_
  have h0 : _root_.GlobalTheory.FlagMeas.detNorm E j g = 0 := le_antisymm (not_lt.1 hg) (detNorm_nonneg g)
  simp [h0, zero_pow (by omega : j ≠ 0)]

theorem haarGL_restrict (hj : 1 ≤ j) : (haarGL E j).restrict {g | 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g} = haarGL E j :=
  Measure.restrict_eq_self_of_ae_mem (haarGL_singular hj)

instance : SigmaFinite (haarGL E j) :=
  haveI : SigmaFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → Fin j → ℂ)) := inferInstance
  @SigmaFinite.withDensity_ofReal (InfinitePlace E → Fin j → Fin j → ℂ) _ volume inferInstance
    fun x => (_root_.GlobalTheory.FlagMeas.detNorm E j x)⁻¹ ^ j

def embGL (γ : GL (Fin j) E) : MatInf E j := fun w a b => w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)

theorem embGL_mul (γ δ : GL (Fin j) E) : embGL (γ * δ) = embGL γ * embGL δ := by
  funext w a b
  show embGL (γ * δ) w a b = ∑ c, embGL γ w a c * embGL δ w c b
  simp [embGL, Matrix.mul_apply]

theorem embGL_one : embGL (1 : GL (Fin j) E) = oneInf E j := by
  funext w a b
  simp only [embGL, oneInf, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} : x ∈ autGL E j Λ ↔
    ∃ γ : GL (Fin j) E, (∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) ∧ x = embGL γ :=
  ⟨fun ⟨γ, h, h'⟩ => ⟨γ, h, funext fun w => funext fun a => funext fun b => h' w a b⟩,
    fun ⟨γ, h, h'⟩ => ⟨γ, h, fun _ _ _ => by rw [h']; rfl⟩⟩

theorem countable_autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : (autGL E j Λ).Countable := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  have : Countable (GL (Fin j) E) := Units.val_injective.countable
  refine (Set.countable_range (embGL : GL (Fin j) E → MatInf E j)).mono fun x hx => ?_
  obtain ⟨γ, -, rfl⟩ := mem_autGL.1 hx
  exact ⟨γ, rfl⟩

theorem oneInf_mem_autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : oneInf E j ∈ autGL E j Λ :=
  mem_autGL.2 ⟨1, by simp, embGL_one.symm⟩

theorem mul_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x y : MatInf E j} (hx : x ∈ autGL E j Λ)
    (hy : y ∈ autGL E j Λ) : x * y ∈ autGL E j Λ := by
  obtain ⟨γ, h, rfl⟩ := mem_autGL.1 hx
  obtain ⟨δ, h', rfl⟩ := mem_autGL.1 hy
  refine mem_autGL.2 ⟨γ * δ, fun z => ?_, (embGL_mul γ δ).symm⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h, h']

theorem exists_inv_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} (hx : x ∈ autGL E j Λ) :
    ∃ y ∈ autGL E j Λ, y * x = oneInf E j ∧ x * y = oneInf E j := by
  obtain ⟨γ, h, rfl⟩ := mem_autGL.1 hx
  refine ⟨embGL γ⁻¹, mem_autGL.2 ⟨γ⁻¹, fun z => ?_, rfl⟩, ?_, ?_⟩
  · rw [← h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rw [← embGL_mul, inv_mul_cancel, embGL_one]
  · rw [← embGL_mul, mul_inv_cancel, embGL_one]

theorem detNorm_pos_of_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} (hx : x ∈ autGL E j Λ) :
    0 < _root_.GlobalTheory.FlagMeas.detNorm E j x := by
  obtain ⟨y, -, h, -⟩ := exists_inv_mem_autGL hx
  have h1 := detNorm_mul y x
  rw [h, detNorm_oneInf] at h1
  refine (detNorm_nonneg x).lt_of_ne' fun h0 => ?_
  rw [h0, mul_zero] at h1
  exact one_ne_zero h1

theorem covol_eq_of_aedisjoint {X : Type} [Mul X] [MeasurableSpace X] (S : Set X) (μ : Measure X) (A D : Set X)
    (hS : S.Countable) (hm : ∀ γ ∈ S, Measurable fun x => γ * x) (hμ : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ)
    (hinv : ∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x)
    (hD : MeasurableSet D) (hDA : D ⊆ A) (hcov : ∀ x ∈ A, ∃ γ ∈ S, γ * x ∈ D)
    (hdis : ∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → μ {x | γ * x ∈ D ∧ δ * x ∈ D} = 0) : covol S μ A = μ D := by
  apply le_antisymm
  · unfold covol
    exact iInf_le_of_le D (iInf_le_of_le hD (iInf_le_of_le hcov le_rfl))
  unfold covol
  refine le_iInf fun C => le_iInf fun hC => le_iInf fun hCc => ?_
  have : Countable S := hS.to_subtype
  choose inv hinvS hl hr using hinv
  have h1 : D ⊆ ⋃ δ : S, (fun x => inv δ δ.2 * x) ⁻¹' (C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hCc x (hDA hx)
    refine Set.mem_iUnion.2 ⟨⟨inv γ hγ, hinvS γ hγ⟩, ?_, ?_⟩
    · have e : inv (inv γ hγ) (hinvS γ hγ) * x = γ * x := by
        conv_lhs => rw [← hl γ hγ x, hl]
      show inv (inv γ hγ) (hinvS γ hγ) * x ∈ C
      rw [e]; exact hγx
    · show inv γ hγ * (inv (inv γ hγ) (hinvS γ hγ) * x) ∈ D
      rw [hr]; exact hx
  have hmeas : ∀ δ : S, MeasurableSet (C ∩ (fun x => δ.1 * x) ⁻¹' D) := fun δ => hC.inter (hm δ δ.2 hD)
  calc μ D ≤ ∑' δ : S, μ ((fun x => inv δ δ.2 * x) ⁻¹' (C ∩ (fun x => δ.1 * x) ⁻¹' D)) :=
        (measure_mono h1).trans (measure_iUnion_le _)
    _ = ∑' δ : S, μ (C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
        refine tsum_congr fun δ => ?_
        rw [← Measure.map_apply (hm _ (hinvS δ δ.2)) (hmeas δ), hμ _ (hinvS δ δ.2)]
    _ = μ (⋃ δ : S, C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
        refine (measure_iUnion₀ (fun γ δ hne => ?_) fun δ => (hmeas δ).nullMeasurableSet).symm
        refine measure_mono_null (fun x hx => ?_) (hdis γ γ.2 δ δ.2 fun h => hne (Subtype.ext h))
        exact ⟨hx.1.2, hx.2.2⟩
    _ ≤ μ C := measure_mono (Set.iUnion_subset fun δ => Set.inter_subset_left)

end GlobalTheory.OrbitTerm
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.HomConjDet

section General

variable {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

theorem det_eq_of_equiv (e : U ≃ₗ[ℂ] V) (φ : U →ₗ[ℂ] U) (ψ : V →ₗ[ℂ] V)
    (h : ∀ x, e (φ x) = ψ (e x)) : LinearMap.det φ = LinearMap.det ψ := by
  rw [← LinearMap.det_conj φ e]
  congr 1
  ext y
  simp [h]

variable [Module.Finite ℂ U] [Module.Finite ℂ V]

theorem det_comp_left (α : V →ₗ[ℂ] V) :
    LinearMap.det (LinearMap.llcomp ℂ U V V α : (U →ₗ[ℂ] V) →ₗ[ℂ] (U →ₗ[ℂ] V)) = LinearMap.det α ^ Module.finrank ℂ U := by
  let b := Module.finBasis ℂ U
  have h := LinearMap.det_pi (fun _ : Fin (Module.finrank ℂ U) => α)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  symm
  refine det_eq_of_equiv (b.constr ℂ) _ _ fun x => ?_
  refine b.ext fun i => ?_
  simp

theorem det_comp_right (β : U →ₗ[ℂ] U) :
    LinearMap.det (LinearMap.lcomp ℂ V β) = LinearMap.det β ^ Module.finrank ℂ V := by
  let b := Module.finBasis ℂ V
  have h := LinearMap.det_pi (fun _ : Fin (Module.finrank ℂ V) => β.dualMap)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, LinearMap.det_dualMap] at h
  rw [← h]
  symm
  refine det_eq_of_equiv ((LinearEquiv.linearMapPi ℂ).trans (LinearEquiv.congrRight b.equivFun.symm))
    _ _ fun x => ?_
  ext y
  simp [LinearEquiv.congrRight]

end General

variable {n : ℕ}

def homMat (P Q : Submodule ℂ (Fin n → ℂ)) :
    (((Fin n → ℂ) ⧸ P) →ₗ[ℂ] Q) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.toMatrix' : ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ
    LinearMap.llcomp ℂ _ _ _ Q.subtype ∘ₗ LinearMap.lcomp ℂ Q P.mkQ

theorem homMat_mulVec (P Q : Submodule ℂ (Fin n → ℂ)) (T : ((Fin n → ℂ) ⧸ P) →ₗ[ℂ] Q) (y : Fin n → ℂ) :
    homMat P Q T *ᵥ y = (T (P.mkQ y) : Fin n → ℂ) := by
  simp [homMat, LinearMap.toMatrix'_mulVec]

theorem homMat_injective (P Q : Submodule ℂ (Fin n → ℂ)) : Function.Injective (homMat P Q) := by
  intro S T h
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := P.mkQ_surjective x
  apply Subtype.ext
  rw [← homMat_mulVec, ← homMat_mulVec, h]

theorem range_homMat (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) : LinearMap.range (homMat P Q) = H := by
  ext X
  rw [hH]
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨fun y hy => ?_, fun y => ?_⟩
    · rw [homMat_mulVec, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hy]
      simp
    · rw [homMat_mulVec]
      exact Subtype.property _
  · rintro ⟨h1, h2⟩
    refine ⟨P.liftQ ((Matrix.toLin' X).codRestrict Q fun y => by simpa using h2 y) ?_, ?_⟩
    · intro y hy
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simpa using h1 y hy
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun y => ?_
      rw [Matrix.toLin'_apply, homMat_mulVec]
      simp

theorem det_conj_hom : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → (∀ y ∈ P, f *ᵥ y ∈ P) → (∀ y ∈ Q, f *ᵥ y ∈ Q) → (∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) → Module.finrank ℂ H = (n - Module.finrank ℂ P) * Module.finrank ℂ Q ∧ ∀ φ : H →ₗ[ℂ] H, (∀ X : H, ((φ X : H) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = detOn f Q ^ (n - Module.finrank ℂ P) * detOn f P ^ Module.finrank ℂ Q := by
  intro n f g P Q H hfg hdet hP hQ hH
  obtain rfl := range_homMat P Q H hH
  let e := LinearEquiv.ofInjective _ (homMat_injective P Q)
  have hq : Module.finrank ℂ ((Fin n → ℂ) ⧸ P) = n - Module.finrank ℂ P := by
    have := P.finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun] at this
    omega
  refine ⟨?_, fun φ hφ => ?_⟩
  · rw [← e.finrank_eq, Module.finrank_linearMap, hq]
  have hgf : g * f = 1 := mul_eq_one_comm.1 hfg
  have hgP := GlobalTheory.FlagLeviGroup.inv_keeps hgf P hP
  have hP' : ∀ y ∈ P, Matrix.toLin' f y ∈ P := fun y hy => by simpa using hP y hy
  have hQ' : ∀ y ∈ Q, Matrix.toLin' f y ∈ Q := fun y hy => by simpa using hQ y hy
  have hgP' : P ≤ P.comap (Matrix.toLin' g) := fun y hy => by simpa using hgP y hy
  set α := (Matrix.toLin' f).restrict hQ' with hα
  set β := P.mapQ P (Matrix.toLin' g) hgP' with hβ
  have h1 : LinearMap.det (LinearMap.llcomp ℂ _ _ _ α ∘ₗ LinearMap.lcomp ℂ Q β) = LinearMap.det φ := by
    refine det_eq_of_equiv e _ _ fun T => ?_
    apply Subtype.ext
    rw [hφ]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    simp only [Matrix.toLin'_apply, e, LinearEquiv.ofInjective_apply, ← Matrix.mulVec_mulVec,
      homMat_mulVec]
    simp [hα, hβ, LinearMap.restrict_apply]
  have h2 := LinearMap.det_eq_det_mul_det P (Matrix.toLin' g) hgP'
  have h3 : LinearMap.det ((Matrix.toLin' f).restrict hP') *
      LinearMap.det ((Matrix.toLin' g).restrict hgP') = 1 := by
    rw [← map_mul, ← LinearMap.det_id (A := ℂ) (M := P)]
    congr 1
    refine LinearMap.ext fun y => Subtype.ext ?_
    simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec, hfg]
  have h4 : ‖g.det‖ = 1 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => ‖M.det‖) hfg
    simpa [hdet] using this
  have h5 : LinearMap.det β = LinearMap.det ((Matrix.toLin' f).restrict hP') * g.det := by
    rw [← LinearMap.det_toLin' g, h2, ← mul_assoc, h3, one_mul]
  rw [← h1, LinearMap.det_comp, det_comp_left, det_comp_right, hq, h5, detOn, detOn, dite_eq_left hP',
    dite_eq_left hQ']
  simp [h4, hα]

end GlobalTheory.HomConjDet
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.twoFlagsGramNumber_normalForm_eq_gram_projection : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ), 2 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) ∧ ∀ (u : UT r → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yv k r z z' g₀ (uEmb k r (upper u) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
  first | exact @GlobalTheory.Amp.NormGram.Yv_normal | exact GlobalTheory.Amp.NormGram.Yv_normal | (intros; apply GlobalTheory.Amp.NormGram.Yv_normal <;> assumption)
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_radical_normalForm_pair_of_flags : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (p : Point ℂ (r + 1)), TwoFl k r z z' g₀ → ZhatO k r z z' g₀ = ptMat p → ∃ p₁ p₀ : PPar k r, pOf k r p₀ *ᵥ z' = z' ∧ IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) ∧ Zr k r (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) = Zr k r g₀ ∧ ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r := by
  first | exact @GlobalTheory.Amp.NormalEx.normal_form | exact GlobalTheory.Amp.NormalEx.normal_form | (intros; apply GlobalTheory.Amp.NormalEx.normal_form <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_blockAntidiagonal_scaled_pairing_matrix : ∀ {K : Type} [Field K] {j r : ℕ} (hj : j ≤ r) (w : Formalism.MainNotions.S.Loc.Pt K j),
    ∃ β : Fin r → ℕ, Monotone β ∧ (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
      ∀ (σ : K →+* ℂ) (sgn : Fin j → ℤˣ) (ρ : ℝ), 0 < ρ →
      GlobalTheory.Amp.BlockAnti (fun a : Fin j => β (Fin.castLE hj a))
        (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) := by
  first | exact @GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing | exact GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing | (intros; apply GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  first | exact @GlobalTheory.HL.sumData_mass_eq_sumCls | exact GlobalTheory.HL.sumData_mass_eq_sumCls | (intros; apply GlobalTheory.HL.sumData_mass_eq_sumCls <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TotalWeight

theorem natCast_pow_le_pow_of_exponent_le (q m a e e' : ℕ) (he : e ≤ e') (h1 : (1 : ℝ) ≤ (q : ℝ) ^ (m + a)) :
    (q : ℝ) ^ (e * m) ≤ ((q : ℝ) ^ (m + a)) ^ e' := by
  have h2 : (q : ℝ) ^ m ≤ (q : ℝ) ^ (m + a) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simpa using h1
      · simp [hm.ne']
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (Nat.le_add_right _ _)
  calc (q : ℝ) ^ (e * m) = ((q : ℝ) ^ m) ^ e := by rw [mul_comm, pow_mul]
    _ ≤ ((q : ℝ) ^ (m + a)) ^ e := pow_le_pow_left₀ (by positivity) h2 e
    _ ≤ _ := pow_le_pow_right₀ h1 he

theorem sumCls_one_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k)
    (h : ∃ d Λ, S.IsTerm d Λ) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  obtain ⟨d, Λ, hT⟩ := h
  obtain ⟨ha, hD, -, -, h1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : 0 ≤ S.vth := by
    unfold Frames.vth
    split_ifs <;> norm_num
  have hHp : S.Hp = (S.q : ℝ) ^ ((S.vth + S.vD).toNat + S.a.toNat) := by
    unfold Frames.Hp
    rw [← zpow_natCast]
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (add_nonneg hth hD)]
    ring
  refine (GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans
    ((GlobalTheory.IntClsCount.main L r k S hD).trans ?_)
  have he : r * (r + 1) ≤ 3 * (r + 1) ^ 2 := by nlinarith
  rw [hHp] at h1 ⊢
  have key := ENNReal.ofReal_le_ofReal (natCast_pow_le_pow_of_exponent_le S.q _ _ _ _ he h1)
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at key
  exact key

end GlobalTheory.HL.TotalWeight
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 ≤ S.a ∧ 0 ≤ S.vD ∧ (∀ l, S.D l ∈ L.O) ∧ (S.q : ℝ) ^ S.a ≤ S.Hp ∧ 1 ≤ S.Hp ∧ (∃ i : ℕ, (i : ℤ) ≤ S.a ∧ S.be d Λ = S.q ^ i) ∧ (S.BBzero d Λ ↔ S.be d Λ = 1) ∧ (¬ S.BBzero d Λ → (S.q : ℝ) ≤ S.Hp) ∧ (∀ y ∈ S.sat Λ, algebraMap F E ((S.ϖ : F) ^ S.a) • y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ S.spanTo S.f j ⊔ S.spanTo S.f' j, y - y₁ ∈ S.M d Λ := by
  first | exact @GlobalTheory.HL.Defect.exponents_and_defect | exact GlobalTheory.HL.Defect.exponents_and_defect | (intros; apply GlobalTheory.HL.Defect.exponents_and_defect <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

theorem _root_.GlobalTheory.T.adelicLattice_selfDual_hermitian : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  first | exact @GlobalTheory.AdelicLattice.adelicLattice_selfDual | exact GlobalTheory.AdelicLattice.adelicLattice_selfDual | (intros; apply GlobalTheory.AdelicLattice.adelicLattice_selfDual <;> assumption)
end
