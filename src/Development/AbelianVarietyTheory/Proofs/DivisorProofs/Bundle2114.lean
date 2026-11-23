module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle103
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n k : ℕ} {J : Matrix (Fin n) (Fin n) E} {X : Matrix (Fin n) (Fin k) E}


omit [NumberField E] in
theorem scalesBy_mul {p q : GAd σ J} {β γ : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β)
    (e' : ScalesBy σ J X q γ) : ScalesBy σ J X (p * q) (β * γ) := by
  unfold ScalesBy at *
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Units.val_mul, Matrix.mul_assoc]


omit [NumberField E] in
theorem scalesBy_inv {p : GAd σ J} {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β) :
    ScalesBy σ J X p⁻¹ β⁻¹ := by
  unfold ScalesBy at *
  calc (matHom _ σ J p⁻¹).1 * adMat F X = (matHom _ σ J p⁻¹).1 * (adMat F X * β.1 * (β⁻¹).1) := by
        rw [Matrix.mul_assoc (adMat F X), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F X * (β⁻¹).1 := by
        rw [← e]; simp only [Matrix.mul_assoc]
    _ = adMat F X * (β⁻¹).1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem absE_pos (u : (AF F ⊗[F] E)ˣ) : (0 : ℝ) < absE F E u := by
  have h : absE F E u * absE F E u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

theorem isCompact_isHt_scales : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ IsHt (levelAll σ J L a) h ∧ ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h H
  haveI := H.lat
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll H.cm J L a
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx H.cm H.herm H.witt
  have hsc : ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
    intro p β e g
    obtain ⟨q, γ, e', k, hk, rfl⟩ := H.iwa g
    rw [← mul_assoc, H.ht _ _ (scalesBy_mul e e') _ hk, H.ht _ _ e' _ hk, map_mul, map_mul, NNReal.coe_mul]
  let φ : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E) := fun p =>
    adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X)
  have h1 : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hyx]; simp
  have hφ : ∀ p β, ScalesBy σ J X p β → φ p = β.1 := fun p β e => by
    unfold ScalesBy at e
    show adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X) = β.1
    rw [e, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have cφ : Continuous φ := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  let P := GlobalTheory.StdPar.frameStab σ J X (⊤ : Subgroup (GL (Fin (r + 1)) (AF F ⊗[F] E)))
  have cP : IsClosed (P : Set (GAd σ J)) := GlobalTheory.StdPar.isClosed_frameStab hyx isClosed_univ
  have hP : ∀ p : P, ScalesBy σ J X p.1 p.2.choose := fun p => p.2.choose_spec.2
  let u : P → (AF F ⊗[F] E)ˣ := fun p => Matrix.GeneralLinearGroup.det p.2.choose
  have cu : Continuous u := Units.continuous_iff.2
    ⟨((cφ.comp continuous_subtype_val).matrix_det).congr fun p => by
        simp only [Function.comp, u, hφ _ _ (hP p)]; rfl,
      ((cφ.comp (continuous_subtype_val.inv)).matrix_det).congr fun p => by
        show (φ (p.1⁻¹)).det = _
        rw [hφ _ _ (scalesBy_inv (hP p)), ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]⟩
  refine ⟨hK, ⟨fun g => ?_, ?_, fun k hk => by simpa using H.ht 1 1 (by simp [ScalesBy]) k hk, fun g => ?_⟩, hsc⟩
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    rw [H.ht _ _ e _ hk]; exact absE_pos _
  · refine GlobalTheory.Doubling.continuous_of_prod cP hK
      (fun g => let ⟨p, β, e, k, hk, e'⟩ := H.iwa g; ⟨⟨p, β, trivial, e⟩, k, hk, e'⟩) ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (cu.comp continuous_fst))).congr
      fun x => (H.ht _ _ (hP x.1) _ x.2.2).symm
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    rw [mul_assoc, hsc _ _ e, H.ht _ _ e _ hk]

end GlobalTheory.ResidueEisenstein.HtCont

end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal

open GlobalTheory.DegCmp

section

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def sameDegQuot (ev : V →ₗ[K] Ω) : IntermediateField K Ω where
  carrier := {x | ∃ (e : ℕ) (q : Ω), q ∈ (LinearMap.range ev) ^ e ∧ q ≠ 0 ∧ x * q ∈ (LinearMap.range ev) ^ e}
  mul_mem' := by
    rintro x y ⟨e, q, hq, hq0, hxq⟩ ⟨e', q', hq', hq'0, hyq'⟩
    refine ⟨e + e', q * q', ?_, mul_ne_zero hq0 hq'0, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul hq hq'
    · rw [pow_add, show x * y * (q * q') = (x * q) * (y * q') by ring]
      exact Submodule.mul_mem_mul hxq hyq'
  add_mem' := by
    rintro x y ⟨e, q, hq, hq0, hxq⟩ ⟨e', q', hq', hq'0, hyq'⟩
    refine ⟨e + e', q * q', ?_, mul_ne_zero hq0 hq'0, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul hq hq'
    · rw [pow_add, show (x + y) * (q * q') = (x * q) * q' + q * (y * q') by ring]
      exact Submodule.add_mem _ (Submodule.mul_mem_mul hxq hq') (Submodule.mul_mem_mul hq hyq')
  algebraMap_mem' a := by
    refine ⟨0, 1, by simp [Submodule.one_eq_range], one_ne_zero, ?_⟩
    rw [pow_zero, mul_one]
    exact Submodule.algebraMap_mem a
  inv_mem' := by
    rintro x ⟨e, q, hq, hq0, hxq⟩
    by_cases hx : x = 0
    · subst hx
      exact ⟨e, q, hq, hq0, by simpa using hxq⟩
    · refine ⟨e, x * q, hxq, mul_ne_zero hx hq0, ?_⟩
      rwa [show x⁻¹ * (x * q) = q by field_simp]

theorem ratioField_le_sameDegQuot (ev : V →ₗ[K] Ω) : ratioField ev ≤ sameDegQuot ev := by
  rw [ratioField, IntermediateField.adjoin_le_iff]
  rintro a ⟨v, w, rfl⟩
  by_cases hw : ev w = 0
  · rw [hw, div_zero]; exact (sameDegQuot ev).zero_mem
  · refine ⟨1, ev w, by simp, hw, ?_⟩
    rw [div_mul_cancel₀ _ hw, pow_one]
    exact LinearMap.mem_range_self ev v

theorem isRatio_of_genRatios (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) : GenRatios ev → ∀ (τ : ℕ) (t : Ω), IsRatio ev τ t := by
  rintro ⟨hev, htop⟩ τ t
  obtain ⟨w, hw⟩ : ∃ w, ev w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hev (LinearMap.ext h)
  have hmem : t / ev w ^ τ ∈ sameDegQuot ev := by
    apply ratioField_le_sameDegQuot ev
    rw [htop]; trivial
  obtain ⟨e, q, hq, hq0, hp⟩ := hmem
  refine ⟨e, q, hq, hq0, ?_⟩
  have : t * q = (t / ev w ^ τ * q) * ev w ^ τ := by
    field_simp
  rw [this, add_comm, pow_add]
  exact Submodule.mul_mem_mul hp (Submodule.pow_mem_pow _ (LinearMap.mem_range_self ev w) τ)

end

end GlobalTheory.DegVal
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

open Pointwise

namespace GlobalTheory.ResLine.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in
theorem inv_eigen {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) :
    (matHom _ σ J p⁻¹).1 * adMat F x = (l⁻¹).1 • adMat F x := by
  have h1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : l.1 • ((matHom _ σ J p⁻¹).1 * adMat F x) = adMat F x := by
    rw [← Matrix.mul_smul, ← hp, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  calc _ = ((l⁻¹).1 * l.1) • ((matHom _ σ J p⁻¹).1 * adMat F x) := by rw [Units.inv_mul, one_smul]
    _ = _ := by rw [← smul_smul, h2]

omit [NumberField F] in
theorem exists_col_ne {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, col X i 0 ≠ 0 := by
  by_contra hc
  push Not at hc
  have h0 : ∀ j, X j 0 = 0 := fun j => hc j
  have := congrFun (congrFun hW.xy 0) 0
  simp [Matrix.mul_apply, Formalism.UG.cT, h0] at this

set_option linter.style.haveILetI false in
theorem isCompact_and_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h →
    IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ Continuous h := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hCM, -, -, hW, hA, hI1, hI2⟩ := hS
  let _ : Submodule.IsFullLattice E L := hA.lat
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hCM J L a
  refine ⟨hK, ?_⟩
  obtain ⟨i, hi⟩ := exists_col_ne hW
  set x := col X with hx
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 :=
    Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous
  let Λ : GAd σ J → AF F ⊗[F] E := fun g =>
    ((matHom _ σ J g).1 * adMat F x) i 0 * inclR (F := F) (AF F) (x i 0)⁻¹
  have hΛ : Continuous Λ := ((hm.matrix_mul continuous_const).matrix_elem i 0).mul continuous_const
  have key : ∀ p (l : (AF F ⊗[F] E)ˣ), (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → l.1 = Λ p := by
    intro p l hl
    have e := congrFun (congrFun hl i) 0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at e
    simp only [Λ, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  let P : Set (GAd σ J) := {p | (matHom _ σ J p).1 * adMat F x = Λ p • adMat F x ∧ Λ p * Λ p⁻¹ = 1}
  have memP : ∀ p, (∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) → p ∈ P := by
    rintro p ⟨l, hl⟩
    have e1 := key p l hl
    have e2 := key p⁻¹ l⁻¹ (inv_eigen hl)
    exact ⟨by rw [← e1]; exact hl, by rw [← e1, ← e2, Units.mul_inv]⟩
  have hPc : IsClosed P :=
    (isClosed_eq (hm.matrix_mul continuous_const) (hΛ.smul continuous_const)).inter
      (isClosed_eq (hΛ.mul (hΛ.comp continuous_inv)) continuous_const)
  let u : P → (AF F ⊗[F] E)ˣ := fun p => ⟨Λ p, Λ p.1⁻¹, p.2.2, by rw [mul_comm]; exact p.2.2⟩
  have hu : Continuous u := Units.continuous_iff.2
    ⟨hΛ.comp continuous_subtype_val, (hΛ.comp continuous_inv).comp continuous_subtype_val⟩
  let f : P → ℝ := fun p => (absE F E (u p) : ℝ)
  have hf : Continuous f := NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hu)
  have hval : ∀ p : P, ∀ k ∈ levelAll σ J L a, h (p.1 * k) = f p := fun p k hk =>
    hI2 p.1 (u p) p.2.1 k hk
  rw [continuous_iff_isClosed]
  intro s hs
  have hpre : h ⁻¹' s = (Subtype.val '' (f ⁻¹' s)) * (levelAll σ J L a : Set (GAd σ J)) := by
    ext g; constructor
    · intro hg
      obtain ⟨p, l, hl, k, hk, rfl⟩ := hI1 g
      have hp : p ∈ P := memP p ⟨l, hl⟩
      refine ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      show f ⟨p, hp⟩ ∈ s
      rw [← hval ⟨p, hp⟩ k hk]; exact hg
    · rintro ⟨_, ⟨p, hp, rfl⟩, k, hk, rfl⟩
      show h (p.1 * k) ∈ s
      rw [hval p k hk]; exact hp
  rw [hpre]
  exact (hPc.isClosedEmbedding_subtypeVal.isClosedMap _ (hs.preimage hf)).mul_right_of_isCompact hK

end GlobalTheory.ResLine.HtCont

end
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal NNReal

namespace GlobalTheory.ResLine

theorem map_eq_self_of_normalises_lattice {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    (Λ : Subgroup B) [Countable Λ] (ν : Measure B) [ν.IsHaarMeasure] (D : Set B) (hD : IsFundamentalDomain Λ D ν)
    (hfin : ν D ≠ ⊤) (φ : B ≃ₜ* B) (h1 : ∀ b ∈ Λ, φ b ∈ Λ) (h2 : ∀ b ∈ Λ, φ.symm b ∈ Λ) : ν.map φ = ν := by
  haveI : (ν.map φ).IsHaarMeasure := φ.isHaarMeasure_map ν
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map φ) ν
  set c := Measure.haarScalarFactor (ν.map φ) ν
  have hφm : Measurable φ := φ.continuous.measurable
  have hq : Measure.QuasiMeasurePreserving φ ν ν := by
    refine ⟨hφm.aemeasurable, ?_⟩
    rw [hc]
    exact Measure.smul_absolutelyContinuous
  have h' : IsFundamentalDomain Λ (φ ⁻¹' D) ν := by
    refine hD.preimage_of_equiv hq (e := fun g : Λ => (⟨φ.symm g, h2 g g.2⟩ : Λ)) ?_ ?_
    · constructor
      · intro a b hab
        apply Subtype.ext
        exact φ.symm.injective (congrArg Subtype.val hab)
      · intro a
        exact ⟨⟨φ a, h1 a a.2⟩, Subtype.ext (φ.symm_apply_apply a)⟩
    · intro g x
      simp [Subgroup.smul_def]
  have hm : ν (φ ⁻¹' D) = ν D := h'.measure_eq hD
  have h0 : ν D ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map φ) D = ν (φ ⁻¹' D) :=
    MeasurableEquiv.map_apply φ.toHomeomorph.toMeasurableEquiv D
  have h3 : (c : ℝ≥0∞) * ν D = 1 * ν D := by
    calc (c : ℝ≥0∞) * ν D = (c • ν) D := by simp [Measure.smul_apply]
      _ = (ν.map φ) D := by rw [hc]
      _ = 1 * ν D := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h3
    exact_mod_cast this
  rw [hc, hc1, one_smul]

theorem lintegral_conj_eq_of_semiLat : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ m ∈ M, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (m * u * m⁻¹) ∂ν = ∫⁻ u : N, f u ∂ν := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM h m hm f hf
  haveI := h.haarN
  haveI : LocallyCompactSpace N := h.closedN.locallyCompactSpace
  haveI : LocallyCompactSpace M := h.closedM.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  have hcount : ∀ K : Subgroup G, Countable (Λ.subgroupOf K) := fun K =>
    Function.Injective.countable (f := fun g : Λ.subgroupOf K => (⟨g.1.1, g.2⟩ : Λ))
      fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun g : Λ => (g : G)) hab))
  haveI := hcount N
  haveI := hcount M
  have hB : ∀ x : M, ∀ b ∈ N, M.subtype x * b * (M.subtype x)⁻¹ ∈ N := fun x b hb => h.norm x x.2 b hb
  have key := GlobalTheory.ConjModulus.map_conj_eq_self_of_lattice M G M.subtype continuous_subtype_val N h.closedN hB ν h.haarN
    (Λ.subgroupOf M) π DM h.haarM h.domM h.finM (fun x hx => by
      have hx' : (x : G) ∈ Λ := hx
      refine map_eq_self_of_normalises_lattice (Λ.subgroupOf N) ν DN h.domN h.finN
        (GlobalTheory.ConjModulus.conjCME M.subtype N hB x) ?_ ?_
      · intro b hb
        have hb' : (b : G) ∈ Λ := hb
        exact Λ.mul_mem (Λ.mul_mem hx' hb') (Λ.inv_mem hx')
      · intro b hb
        have hb' : (b : G) ∈ Λ := hb
        exact Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hx') hb') (Λ.inv_mem (Λ.inv_mem hx'))) ⟨m, hm⟩
  have hφm : Measurable (fun b : N => (⟨M.subtype ⟨m, hm⟩ * b * (M.subtype ⟨m, hm⟩)⁻¹, hB ⟨m, hm⟩ b b.2⟩ : N)) :=
    (GlobalTheory.ConjModulus.conjCME M.subtype N hB ⟨m, hm⟩).continuous.measurable
  have := lintegral_map (μ := ν) (hf.comp measurable_subtype_coe) hφm
  rw [key] at this
  exact this.symm

end GlobalTheory.ResLine
end

section

noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem idem_smul_mul {A : Type} [CommRing A] [Algebra (AF F) A] {ε : AF F} (hε : ε * ε = ε) (a b : A) :
    (ε • a + (1 - ε) • (1 : A)) * (ε • b + (1 - ε) • (1 : A)) = ε • (a * b) + (1 - ε) • (1 : A) := by
  simp only [Algebra.smul_def, mul_one]
  have he : algebraMap (AF F) A ε * algebraMap (AF F) A ε = algebraMap (AF F) A ε := by rw [← map_mul, hε]
  rw [map_sub, map_one]
  linear_combination (a * b - a - b + 1) * he


variable (E) in
def idemUnit (ε : AF F) (hε : ε * ε = ε) : (AE F E)ˣ →* (AE F E)ˣ where
  toFun l := ⟨ε • l.1 + (1 - ε) • 1, ε • (l⁻¹ : (AE F E)ˣ).1 + (1 - ε) • 1,
    by rw [idem_smul_mul hε, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul],
    by rw [idem_smul_mul hε, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]⟩
  map_one' := Units.ext (by simp only [Units.val_one, Units.val_mk]; rw [← add_smul, add_sub_cancel, one_smul])
  map_mul' a b := Units.ext (by simp only [Units.val_mul, Units.val_mk]; rw [idem_smul_mul hε])


def eFin (v : Pl F) : AF F := GlobalTheory.LatVac.liftV v 1

def eInf (F : Type) [Field F] [NumberField F] : AF F := realAd F 1

theorem eFin_idem (v : Pl F) : eFin v * eFin v = eFin v := by
  have h := GlobalTheory.LatVac.at_liftV v 1 (eFin v - 1) (by
    rw [eFin, map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem eInf_idem : eInf F * eInf F = eInf F := by
  have h := at_partInf (M := AF F) (1 : AF F) (eInf F - 1) (by
    rw [eInf, GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, evI_realAd_one, sub_self])
  simp only [partInf, smul_eq_mul, mul_one] at h
  unfold eInf at h ⊢
  rw [sub_mul, one_mul, sub_eq_zero] at h
  exact h


variable (E) in
def unitAt (v : Pl F) : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eFin v) (eFin_idem v)


variable (F E) in
def unitArch : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eInf F) eInf_idem



theorem unitAt_mem (v : Pl F) (l : (AE F E)ˣ) : unitAt E v l ∈ idelesAt E (evFin F v) := by
  intro u hu
  have h := GlobalTheory.LatVac.at_liftV v 1 u hu
  change u • (eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1) = 0
  rw [show eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1 = eFin v • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eFin v = 0 from h, zero_smul]

theorem unitArch_mem (l : (AE F E)ˣ) : unitArch F E l ∈ idelesAt E (evI F) := by
  intro u hu
  have h := at_partInf (M := AF F) (1 : AF F) u hu
  simp only [partInf, smul_eq_mul, mul_one] at h
  change u • (eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1) = 0
  rw [show eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1 = eInf F • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eInf F = 0 from h, zero_smul]

end GlobalTheory.ThK.ConeEuler
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_majorantFrame_compact_subgroup_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), K ≤ infPts σ J → IsCompact (K : Set (GAd σ J)) →
    ∃ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)),
      (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ K ≤ majCpt σ J c := by
  first | exact @GlobalTheory.CptMajorant.exists_frame_le_majCpt | exact GlobalTheory.CptMajorant.exists_frame_le_majCpt | (intros; apply GlobalTheory.CptMajorant.exists_frame_le_majCpt <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem _root_.GlobalTheory.T.exists_linearEquiv_mul_twistingSection_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∃ φ : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀), (∀ f, (φ f : Rul Xo c) = f * s.sig) ∧ (∀ g, (φ.symm g : Rul Xo c) = g * s.inv) ∧ (∀ a : c.F, a ≠ 0 → (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) → ∀ f ∈ latOn U Z G, ∀ g : cuspOn U Z (G + G₀), (g : Rul Xo c) = a • (φ f : Rul Xo c) → g ∈ latOn U Z (G + G₀)) ∧ (∀ b : c.F, b ≠ 0 → (∀ w, s.hi w ≤ (vAdd w b : ℝ)) → ∀ g ∈ latOn U Z (G + G₀), ∀ f : cuspOn U Z G, (f : Rul Xo c) = b • (φ.symm g : Rul Xo c) → f ∈ latOn U Z G) := by
  first | exact @GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral | exact GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral | (intros; apply GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem _root_.GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∀ f ∈ suppOn Z, ∀ (σ : c.F →+* ℂ) (D : D7) (V : HSp D) (dict : GA D V → Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) (μ : Measure (AutQ V)), petAt (U (goodOf c σ)) x V dict μ (G + G₀) (f * s.sig) = s.cInf σ * petAt (U (goodOf c σ)) x V dict μ G f := by
  first | exact @GlobalTheory.FlatTw.PetTw.petAt_mul_sig | exact GlobalTheory.FlatTw.PetTw.petAt_mul_sig | (intros; apply GlobalTheory.FlatTw.PetTw.petAt_mul_sig <;> assumption)
end
