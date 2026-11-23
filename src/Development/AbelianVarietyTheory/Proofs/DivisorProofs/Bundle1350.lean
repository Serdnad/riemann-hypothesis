module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame.HomW

section Idem

variable {R L : Type} [CommRing R] [Field L] {n : ℕ} (ι : L →+ R) (hm : ∀ x y, ι (x * y) = ι x * ι y)
include hm

theorem map_mul_map (X Y : Matrix (Fin n) (Fin n) L) : X.map ι * Y.map ι = (X * Y).map ι := by
  ext i j

  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hm]

theorem e_mul (t : L) : ι 1 * ι t = ι t := by rw [← hm, one_mul]

theorem f_mul (t : L) : (1 - ι 1) * ι t = 0 := by rw [sub_mul, one_mul, e_mul ι hm, sub_self]

theorem ff : (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
  have := e_mul ι hm 1
  linear_combination this

theorem f_smul_map (X : Matrix (Fin n) (Fin n) L) : (1 - ι 1) • X.map ι = 0 := by
  ext i j
  simp [Matrix.smul_apply, f_mul ι hm]

theorem f_smul_mul_map (Y : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin n) L) :
    (1 - ι 1) • (Y * X.map ι) = 0 := by
  rw [← Matrix.mul_smul, f_smul_map ι hm, Matrix.mul_zero]

theorem f_smul_map_mul (Y : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin n) L) :
    (1 - ι 1) • (X.map ι * Y) = 0 := by
  rw [← Matrix.smul_mul, f_smul_map ι hm, Matrix.zero_mul]

theorem map_one' : (1 : Matrix (Fin n) (Fin n) L).map ι = ι 1 • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

def Mm (K : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) R := (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) R) + K.map ι

omit hm in
theorem Mm_def (K : Matrix (Fin n) (Fin n) L) : Mm ι K = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) R) + K.map ι := rfl

theorem Mm_mul (K K' : Matrix (Fin n) (Fin n) L) : Mm ι K * Mm ι K' = Mm ι (K * K') := by
  simp only [Mm_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ff ι hm,
    Matrix.one_mul, Matrix.mul_one, f_smul_map ι hm, map_mul_map ι hm, add_zero, zero_add]

theorem Mm_one : Mm ι (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  rw [Mm_def, map_one' ι hm, ← add_smul, sub_add_cancel, one_smul]

theorem sandwich (Y : Matrix (Fin n) (Fin n) R) (K1 K2 K3 : Matrix (Fin n) (Fin n) L) :
    Mm ι K1 * ((1 - ι 1) • Y + K2.map ι) * Mm ι K3 = (1 - ι 1) • Y + (K1 * K2 * K3).map ι := by
  simp only [Mm_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ff ι hm,
    Matrix.one_mul, Matrix.mul_one, f_smul_map ι hm, map_mul_map ι hm, f_smul_mul_map ι hm, f_smul_map_mul ι hm,
    add_zero, zero_add]

def toGL : GL (Fin n) L →* GL (Fin n) R where
  toFun g := ⟨Mm ι (g : Matrix (Fin n) (Fin n) L), Mm ι ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    by rw [Mm_mul ι hm, Units.mul_inv, Mm_one ι hm], by rw [Mm_mul ι hm, Units.inv_mul, Mm_one ι hm]⟩
  map_one' := Units.ext (by show Mm ι ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1; rw [Units.val_one, Mm_one ι hm])
  map_mul' g g' := Units.ext (by
    show Mm ι ((g * g' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Mm ι (g : Matrix (Fin n) (Fin n) L) * Mm ι (g' : Matrix (Fin n) (Fin n) L)
    rw [Units.val_mul, Mm_mul ι hm])

omit hm in
theorem Mm_transpose (K : Matrix (Fin n) (Fin n) L) : (Mm ι K)ᵀ = Mm ι Kᵀ := by
  simp only [Mm_def, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_map]

end Idem

section Core

variable {L : Type} [Field L] {n : ℕ}

theorem unit_core (σL : L →+* L) (δ : L) (hδ : δ ≠ 0) (T : Matrix (Fin n) (Fin n) L) (P : GL (Fin n) L)
    (JT h : Matrix (Fin n) (Fin n) L)
    (hJT : JT = -δ⁻¹ • ((P : Matrix (Fin n) (Fin n) L)ᵀ * T * (P : Matrix (Fin n) (Fin n) L).map σL)ᵀ)
    (hh : (h.map σL)ᵀ * JT * h = JT) :
    ((P : Matrix (Fin n) (Fin n) L) * h * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))ᵀ * T *
      ((P : Matrix (Fin n) (Fin n) L) * h * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map σL = T := by
  set Pm : Matrix (Fin n) (Fin n) L := (P : Matrix (Fin n) (Fin n) L)
  set Pi : Matrix (Fin n) (Fin n) L := ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  set G := Pmᵀ * T * Pm.map σL with hGdef
  have hPP : Pm * Pi = 1 := Units.mul_inv P
  have h1 : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have h2 : Pm.map σL * Pi.map σL = 1 := by rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σL) (map_one σL)]
  have hGt : (h.map σL)ᵀ * Gᵀ * h = Gᵀ := by
    rw [hJT, Matrix.mul_smul, Matrix.smul_mul] at hh
    have := congrArg (fun M : Matrix (Fin n) (Fin n) L => (-δ) • M) hh
    simpa only [smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ, one_smul] using this
  have hG : hᵀ * G * h.map σL = G := by
    have := congrArg Matrix.transpose hGt
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at this
    exact this
  calc (Pm * h * Pi)ᵀ * T * (Pm * h * Pi).map σL
      = Piᵀ * (hᵀ * (Pmᵀ * T * Pm.map σL) * h.map σL) * Pi.map σL := by
        simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = Piᵀ * (Pmᵀ * T * Pm.map σL) * Pi.map σL := by rw [← hGdef, hG]
    _ = (Piᵀ * Pmᵀ) * T * (Pm.map σL * Pi.map σL) := by simp only [Matrix.mul_assoc]
    _ = T := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end Core

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L] {n : ℕ}

theorem e_smul_incM (v : Pl (F := F)) (ι : L →+ AE F E) (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (J : Matrix (Fin n) (Fin n) E) : ι 1 • incM F J = (tJ ι J).map ι := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, incM, tJ, smul_eq_mul]
  rw [pre_spec]
  apply (hAt _).1
  intro u hu
  have h1 : u • ι 1 = 0 := (hAt (ι 1)).2 ⟨1, rfl⟩ u hu
  rw [← smul_mul_assoc, h1, zero_mul]

theorem incM_split (v : Pl (F := F)) (ι : L →+ AE F E) (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (J : Matrix (Fin n) (Fin n) E) : incM F J = (1 - ι 1) • incM F J + (tJ ι J).map ι := by
  rw [← e_smul_incM v ι hAt, ← add_smul, sub_add_cancel, one_smul]

theorem Mm_cA (σ : E →ₐ[F] E) (σL : L →+* L) (ι : L →+ AE F E) (hσ : ∀ x, ι (σL x) = cA σ (ι x))
    (K : Matrix (Fin n) (Fin n) L) : (Mm ι K).map (cA σ) = Mm ι (K.map σL) := by
  have he : cA σ (ι 1) = ι 1 := by rw [← hσ, map_one]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Mm_def, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_sub, he, hσ]
  · simp [Mm_def, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, hσ]

end Adelic

theorem homW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] (σL : L →+* L) (δ : L)
    (ι : L →+ AE F E), δ ≠ 0 → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      ∀ (P JT : GL (Fin n) L), (JT : Matrix (Fin n) (Fin n) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι P X.J)ᵀ →
      ∃ iW : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* UA σ X.J, ∀ h,
        mat (iW h) = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) +
          ((P : Matrix (Fin n) (Fin n) L) * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι := by
  intro F E _ _ _ _ _ σ v n X L _ σL δ ι hδ hAt hm hσ P JT hJT
  let φ : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* GL (Fin n) L :=
    (MulAut.conj P).toMonoidHom.comp (Subgroup.subtype _)
  have hφ : ∀ h, ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (P : Matrix (Fin n) (Fin n) L) *
      ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro h
    simp [φ, MulAut.conj_apply, Units.val_mul]
  have hmem : ∀ h, (toGL ι hm).comp φ h ∈ UG (cA σ) (incM F X.J) := by
    intro h
    have hh : (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JT : Matrix (Fin n) (Fin n) L) *
        ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n) (Fin n) L) := h.2
    show (Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))ᵀ * incM F X.J *
      (Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map (cA σ) = incM F X.J
    rw [Mm_transpose, Mm_cA σ σL ι hσ]
    conv_lhs => rw [incM_split v ι hAt X.J]
    rw [sandwich ι hm, hφ, unit_core σL δ hδ (tJ ι X.J) P JT _ hJT hh, ← incM_split v ι hAt X.J]
  refine ⟨((toGL ι hm).comp φ).codRestrict _ hmem, fun h => ?_⟩
  show Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = _
  rw [hφ, Mm_def]

end GlobalTheory.InertLocFrame.HomW
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNLevi

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

def qI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F)))

def qF (F : Type) [Field F] [NumberField F] : F →+* FiniteAdeleRing (𝓞 F) F :=
  (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F))

def compM (P : Matrix κ κ F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x)

theorem compM_apply (P : Matrix κ κ F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (x : κ → AdeleRing (𝓞 F) F) :
    compM P φ x = φ (P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) := rfl

def archEquiv (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun y := P.map (qI F) *ᵥ y
  invFun y := Q.map (qI F) *ᵥ y
  map_add' y y' := Matrix.mulVec_add _ _ _
  map_smul' r y := by rw [RingHom.id_apply, Matrix.mulVec_smul]
  left_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def finHomeo (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) where
  toFun z := P.map (qF F) *ᵥ z
  invFun z := Q.map (qF F) *ᵥ z
  left_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem comp_pureA (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    compM P (pureA F f g) =
      pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv P Q hPQ hQP) f) (g ∘ finHomeo P Q hPQ hQP) := by
  funext x
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let p : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).1) =
      P.map (qI F) *ᵥ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) := by
    funext i
    change q ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  have h2 : (fun i => ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).2) =
      P.map (qF F) *ᵥ (fun i => (x i).2) := by
    funext i
    change p ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  simp only [compM_apply, pureA, Function.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [h1, h2]
  rfl

theorem comp_mem (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∀ φ ∈ schA F κ, compM P φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (compM P) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨_, _, ⟨hg.1.comp_continuous (finHomeo P Q hPQ hQP).continuous,
      hg.2.comp_homeomorph (finHomeo P Q hPQ hQP)⟩, comp_pureA P Q hPQ hQP f g⟩
  exact fun φ hφ => hle hφ

theorem act_levi {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks A 0 0 B) w = (A.map (algebraMap K R) *ᵥ w.1, B.map (algebraMap K R) *ᵥ w.2) := by
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h0, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, add_zero, zero_add]

theorem dot_transpose {R ι : Type} [CommRing R] [Fintype ι] (M : Matrix ι ι R) (x v : ι → R) :
    x ⬝ᵥ (Mᵀ *ᵥ v) = (M *ᵥ x) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem realised_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ]
    [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det → Realised ψ (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ) := by
  intro F _ _ ψ κ _ _ A hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix κ κ (AdeleRing (𝓞 F) F) := A.map (algebraMap F (AdeleRing (𝓞 F) F))
  let Aim : Matrix κ κ (AdeleRing (𝓞 F) F) := A⁻¹.map (algebraMap F (AdeleRing (𝓞 F) F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨compM A⁻¹, comp_mem A⁻¹ A h2 h1, fun φ hφ => ⟨compM A φ, comp_mem A A⁻¹ h1 h2 φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ compM A⁻¹, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

end GlobalTheory.AdelicSvNLevi

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocSymp

theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] (σL : L →+* L) {α β : Type} [Fintype α] [Fintype β]
    (X Y : Matrix α β L) (A : Matrix α α L) (B : Matrix β β L) :
    (∑ i, ∑ j, ∑ k, ∑ l, X i j * A i k * B j l * σL (Y k l)) =
      Matrix.trace (A * Y.map σL * Bᵀ * Xᵀ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem trace_coords {L : Type} [CommRing L] (σL : L →+* L) {n d : ℕ}
    (PV A : Matrix (Fin n) (Fin n) L) (PW B : Matrix (Fin d) (Fin d) L) (x y : Matrix (Fin d) (Fin n) L) :
    Matrix.trace (A * (PV * yᵀ * PWᵀ).map σL * Bᵀ * (PV * xᵀ * PWᵀ)ᵀ) =
      Matrix.trace ((PVᵀ * A * PV.map σL) * (y.map σL)ᵀ * (PWᵀ * B * PW.map σL)ᵀ * x) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm PVᵀ]
  simp only [Matrix.mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_inclR {L : Type} [Field L] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v : Pl (F := F))
    (hAt : ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y) (a : L) (e : E) :
    ι a * inclR (F := F) (AF F) e = ι (a * GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) e)) := by
  have hat : ∃ z, ι z = ι 1 * inclR (F := F) (AF F) e := by
    refine (hAt _).1 fun u hu => ?_
    have h1 : u • ι 1 = 0 := (hAt (ι 1)).2 ⟨1, rfl⟩ u hu
    rw [← smul_mul_assoc, h1, zero_mul]
  rw [hmul, GlobalTheory.InertLocFrame.pre_spec ι hat, ← mul_assoc, ← hmul, mul_one]

end GlobalTheory.InertLocSymp


open GlobalTheory.InertLocSymp in
theorem GlobalTheory.InertLocSymp.psi_symp_eq :
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) →
      ∀ (PV JS : GL (Fin n) L) (PW JT : GL (Fin d) L),
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι PV X.J →
        (JT : Matrix (Fin d) (Fin d) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι PW W.J)ᵀ →
        ∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) := by
  intro F E _ _ _ _ _ σ B v n d X W L _ _ ϖ σL q δ ψL ι _ hδ hinj hAt hmul hσ hψ PV JS PW JT hGV hGW x y
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, map_zero] at hδ; exact zero_ne_one hδ.1

  have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) =
      ι (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j *
        GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l *
        σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) := by

    simp only [hTens, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [GlobalTheory.InertLocFrame.xm_apply, incM, Matrix.map_apply, ← hσ]
    rw [mul_inclR ι v hAt hmul, mul_inclR ι v hAt hmul, ← hmul]
    rfl

  have hS : (∑ i, ∑ j, ∑ k, ∑ l, ((PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i j *
        GlobalTheory.InertLocFrame.tJ ι X.J i k * GlobalTheory.InertLocFrame.tJ ι W.J j l *
        σL (((PV : Matrix (Fin n) (Fin n) L) * yᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) k l)) =
      -GlobalTheory.Hk3.locH σL δ JS JT x y := by
    rw [quadruple_sum_eq_trace_transpose_mul, trace_coords]
    have e1 : (PV : Matrix (Fin n) (Fin n) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι X.J * (PV : Matrix (Fin n) (Fin n) L).map σL =
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := hGV.symm
    have e2 : ((PW : Matrix (Fin d) (Fin d) L)ᵀ * GlobalTheory.InertLocFrame.tJ ι W.J * (PW : Matrix (Fin d) (Fin d) L).map σL)ᵀ =
        -δ • (JT : Matrix (Fin d) (Fin d) L) := by
      rw [hGW, smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ0, one_smul]; rfl
    rw [e1, e2, GlobalTheory.Hk3.locH, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm _ x]
    simp only [Matrix.mul_assoc]; ring
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have h1 : (2 : AF F) • ι 1 = 0 := by
      rw [two_smul, ← map_add (f := _), one_add_one_eq_two, h, map_zero]
    have : ι 1 = 0 := by
      rw [← one_smul (AF F) (ι 1), ← invOf_mul_self (2 : AF F), mul_smul, h1, smul_zero]
    exact one_ne_zero (hinj (this.trans (map_zero ι).symm))
  haveI : NeZero (2 : L) := ⟨h2⟩
  set z := GlobalTheory.Hk3.locH σL δ JS JT x y
  have hhalf : ⅟(2 : AF F) • ι z = ι (z / 2) := by
    have : ι z = (2 : AF F) • ι (z / 2) := by
      rw [two_smul, ← map_add (f := _), add_halves]
    rw [this, smul_smul, invOf_mul_self, one_smul]
  have hsymp : ⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (GlobalTheory.InertLocFrame.xm ι PV PW x) (GlobalTheory.InertLocFrame.xm ι PV PW y) =
      Algebra.trace (AF F) (AE F E) (ι (z / 2)) := by
    rw [symp, hT, hS, map_neg, neg_one_mul, neg_neg, ← smul_eq_mul, ← LinearMap.map_smul, hhalf]
  rw [hsymp, hψ, map_div₀, map_ofNat, add_div]
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TopForm

theorem bijective_formMap_of_bijective {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} (D : ℕ) (ρ : A →+* B) (h : ρ.comp α = β)
    (hρ : Function.Bijective ρ) : Function.Bijective (TopForm.formMap D ρ h) := by
  let e : A ≃+* B := RingEquiv.ofBijective ρ hρ
  let σ : B →+* A := e.symm.toRingHom
  have e1 : σ.comp ρ = RingHom.id A := RingHom.ext fun a => e.symm_apply_apply a
  have e2 : ρ.comp σ = RingHom.id B := RingHom.ext fun b => e.apply_symm_apply b
  have h' : σ.comp β = α := by
    rw [← h, ← RingHom.comp_assoc, e1, RingHom.id_comp]
  refine Function.bijective_iff_has_inverse.mpr ⟨TopForm.formMap D σ h', fun x => ?_, fun y => ?_⟩
  · rw [formMap_formMap ρ σ (RingHom.id A) e1 h h' (RingHom.id_comp α)]
    exact formMap_of_eq_id _ rfl _ x
  · rw [formMap_formMap σ ρ (RingHom.id B) e2 h' h (RingHom.id_comp β)]
    exact formMap_of_eq_id _ rfl _ y

end GlobalTheory.TopForm

namespace GlobalTheory.EtaleKlt

theorem ratPull_bijective_of_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ n : ℕ,
      Function.Bijective (EtaleKlt.ratPull p s n) := by
  intro k _ X Y _ _ p s _ hs n
  exact TopForm.bijective_formMap_of_bijective n _ (functionFieldMap_comp_constFn p s) hs

end GlobalTheory.EtaleKlt
end
end
